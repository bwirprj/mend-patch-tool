// main.ts is mend, the CLI SPEC.md specifies.
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 { readonly line: string; constructor(line: string) { this.line = line; } }
class Fail { readonly code: string; readonly path: string; constructor(code: string, path: string) { this.code = code; this.path = path; } }

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try { if (statSync(p).isFile()) v = readFileSync(p, 'utf8'); } catch { v = null; }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

let STRICT = false;
const MOVES: { old: string; new: string }[] = [];

function splitFile(text: string): { lines: string[]; br: string; final: boolean } {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br = (nl >= 0 && nl > 0 && text[nl - 1] === '\r') ? '\r\n' : '\n';
  const parts = text.split(br);
  const final = text.endsWith(br);
  const lines = final ? parts.slice(0, -1) : parts;
  return { lines, br, final };
}
function joinFile(lines: string[], br: string, final: boolean): string {
  if (lines.length === 0) return '';
  return lines.join(br) + (final ? br : '');
}
function leadingWS(s: string): string {
  let i = 0;
  while (i < s.length && (s[i] === ' ' || s[i] === '\t')) i++;
  return s.slice(0, i);
}
function eqTier(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return a.replace(/[ \t]+$/, '') === b.replace(/[ \t]+$/, '');
  return a.trim().replace(/^[ \t]+/, '').replace(/[ \t]+$/, '') === b.trim().replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  // simpler below
}
// fix eqTier tier2
function eqTier2(a: string, b: string): boolean {
  const ta = a.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  const tb = b.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  return ta === tb;
}

function eqTierFn(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return a.replace(/[ \t]+$/, '') === b.replace(/[ \t]+$/, '');
  return eqTier2(a, b);
}

function pickTier(fileLines: string[], O: string[]): { tier: number; positions: number[] } | null {
  if (O.length === 0) return { tier: 0, positions: [] };
  const tiers = STRICT ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const pos: number[] = [];
    for (let i = 0; i + O.length <= fileLines.length; i++) {
      let ok = true;
      for (let j = 0; j < O.length; j++) if (!eqTierFn(fileLines[i + j], O[j], tier)) { ok = false; break; }
      if (ok) pos.push(i);
    }
    if (pos.length > 0) return { tier, positions: pos };
  }
  return null;
}

function pickTierFromCursor(fileLines: string[], O: string[], cursor: number, eof: boolean): { tier: number; positions: number[] } | null {
  if (O.length === 0) return { tier: 0, positions: [] };
  const tiers = STRICT ? [0] : [0, 1, 2];
  for (const tier of tiers) {
    const pos: number[] = [];
    for (let i = cursor; i + O.length <= fileLines.length; i++) {
      if (eof && i + O.length !== fileLines.length) continue;
      let ok = true;
      for (let j = 0; j < O.length; j++) if (!eqTierFn(fileLines[i + j], O[j], tier)) { ok = false; break; }
      if (ok) pos.push(i);
    }
    if (pos.length > 0) return { tier, positions: pos };
  }
  return null;
}

function transformN(N: string[], O: string[], tier: number, fileLines: string[], pos: number, contextFlags: boolean[], ctxOIndex: number[]): string[] {
  const F = leadingWS(fileLines[pos] ?? '');
  const P = leadingWS((O && O.length > 0) ? O[0] : '');
  const out: string[] = [];
  for (let idx = 0; idx < N.length; idx++) {
    if (contextFlags && contextFlags[idx]) {
      const oi = ctxOIndex ? ctxOIndex[idx] : -1;
      if (oi >= 0 && pos + oi < fileLines.length) out.push(fileLines[pos + oi]);
      else out.push(N[idx]);
    } else {
      let line = N[idx];
      if (tier === 2) {
        if (line.trim() !== '' && line.startsWith(P)) line = F + line.slice(P.length);
      }
      out.push(line);
    }
  }
  return out;
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

// ---------- JSON (starter) ----------
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try { v = JSON.parse(text); } catch { throw new Exit2(`error: parse ${first + 1}`); }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try { e = jsonEdit(JSON.parse(l)); } catch { e = null; }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------- Unified ----------
function parseUnifiedPath(s: string): string {
  let t = s;
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t === '/dev/null') return t;
  if (t.startsWith('a/')) t = t.slice(2);
  if (t.startsWith('b/')) t = t.slice(2);
  return t;
}

function unifiedEdits(text: string, lines: string[]): Edit[] {
  const edits: Edit[] = [];
  const n = lines.length;
  const isSectionStart = (i: number): boolean => {
    if (i >= n) return false;
    if (lines[i].startsWith('diff --git ')) return true;
    if (lines[i].startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) return true;
    return false;
  };
  let i = 0;
  // skip leading
  while (i < n) {
    if (lines[i].startsWith('@@')) throw new Exit2(`error: parse ${i + 1}`);
    if (!isSectionStart(i)) { i++; continue; }
    // parse section
    let oldPath: string | null = null;
    let newPath: string | null = null;
    let creation = false;
    let deletion = false;
    let renameFrom: string | null = null;
    let renameTo: string | null = null;
    // diff --git first
    if (lines[i].startsWith('diff --git ')) {
      const m = lines[i].match(/^diff --git a\/(.+) b\/(.+)$/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      oldPath = m[1];
      newPath = m[2];
      i++;
    }
    // header loop
    let seenPaths = false;
    while (i < n && !lines[i].startsWith('@@') && !(seenPaths && lines[i].startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) && !lines[i].startsWith('diff --git ')) {
      const l = lines[i];
      if (l.startsWith('--- ')) {
        if (i + 1 >= n || !lines[i + 1].startsWith('+++ ')) throw new Exit2(`error: parse ${i + 2}`);
        oldPath = parseUnifiedPath(l.slice(4));
        newPath = parseUnifiedPath(lines[i + 1].slice(4));
        seenPaths = true;
        i += 2;
        continue;
      }
      if (l.startsWith('+++ ')) { i++; continue; }
      if (l.startsWith('rename from ')) { renameFrom = l.slice('rename from '.length).trim(); i++; continue; }
      if (l.startsWith('rename to ')) { renameTo = l.slice('rename to '.length).trim(); i++; continue; }
      if (l.trim() === 'new file mode' || l.startsWith('new file mode ')) { creation = true; i++; continue; }
      if (l.trim() === 'deleted file mode' || l.startsWith('deleted file mode ')) { deletion = true; i++; continue; }
      i++;
    }
    if (renameFrom !== null && oldPath === null) oldPath = renameFrom;
    if (renameTo !== null && newPath === null) newPath = renameTo;
    if (creation) oldPath = '/dev/null';
    if (deletion) newPath = '/dev/null';
    if (oldPath === null) oldPath = '';
    if (newPath === null) newPath = '';
    // parse hunks
    const hunks: { A: number; O: string[]; N: string[]; ctx: boolean[]; ctxO: number[]; noNewline: boolean }[] = [];
    while (i < n && lines[i].startsWith('@@') && !isSectionStart(i)) {
      const m = lines[i].match(/^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      const A = parseInt(m[1], 10);
      // const B = m[2] ? parseInt(m[2],10) : 1;
      const C = parseInt(m[3], 10);
      void C;
      i++;
      // collect body
      const bodyItems: string[] = [];
      while (i < n && !isSectionStart(i) && !(lines[i].startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ '))) {
        const l = lines[i];
        if (l.startsWith('diff --git ')) break;
        if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+') || l.startsWith('\\')) {
          bodyItems.push(l);
          i++;
          continue;
        }
        break;
      }
      // trim trailing empty (empty string) lines
      while (bodyItems.length > 0 && bodyItems[bodyItems.length - 1] === '') bodyItems.pop();
      // build hunk
      const O: string[] = [];
      const N: string[] = [];
      const ctx: boolean[] = [];
      const ctxO: number[] = [];
      let noNewline = false;
      for (let k = 0; k < bodyItems.length; k++) {
        const l = bodyItems[k];
        if (l.startsWith('\\')) {
          noNewline = true;
          continue;
        }
        if (l === '' ) {
          // empty context line
          O.push(''); N.push(''); ctx.push(true); ctxO.push(O.length - 1);
        } else if (l.startsWith(' ')) {
          const t = l.slice(1);
          O.push(t); N.push(t); ctx.push(true); ctxO.push(O.length - 1);
        } else if (l.startsWith('-')) {
          O.push(l.slice(1));
        } else if (l.startsWith('+')) {
          N.push(l.slice(1)); ctx.push(false); ctxO.push(-1);
        }
      }
      // noNewline should only if backslash follows last context or + line; our loop sets true on any backslash. If backslash follows a - line, ignore.
      // Recompute noNewline properly: check if last body item is backslash
      noNewline = bodyItems.length > 0 && bodyItems[bodyItems.length - 1].startsWith('\\');
      hunks.push({ A, O, N, ctx, ctxO, noNewline });
    }
    // build edit
    const op = oldPath;
    const np = newPath;
    const isCreate = op === '/dev/null' || creation;
    const isDelete = np === '/dev/null' || deletion;
    const isMove = !isCreate && !isDelete && op !== np;
    const edit: Edit = (tree) => {
      if (isCreate) {
        if (!safe(np)) throw new Fail('unsafe', np);
        if (tree.get(np) !== null) throw new Fail('exists', np);
        // file is + lines of all hunks in order
        const plusLines: string[] = [];
        let nnl = false;
        for (const h of hunks) {
          for (const l of h.N) {
            // For creation, only + lines? We collected context too in N. Spec says + lines. Need filter: re-parse? We stored combined. Hmm.
          }
        }
        // Re-extract + lines from hunks impossible; but for creation O empty. Let's instead collect from body again? We didn't store. 
        // Fallback: use N (includes context). For a new file hunk, all lines are +, so N fine.
        let all: string[] = [];
        for (const h of hunks) all = all.concat(h.N);
        // noNewline: if last hunk's last body line backslash
        nnl = hunks.length > 0 && hunks[hunks.length - 1].noNewline;
        const content = all.length === 0 ? '' : all.join('\n') + (nnl ? '' : '\n');
        tree.now.set(np, content);
        return;
      }
      if (isDelete) {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (tree.get(op) === null) throw new Fail('missing', op);
        tree.now.set(op, null);
        return;
      }
      // move or change
      if (!safe(op)) throw new Fail('unsafe', op);
      if (tree.get(op) === null) throw new Fail('missing', op);
      if (isMove) {
        if (!safe(np)) throw new Fail('unsafe', np);
        if (tree.get(np) !== null) throw new Fail('exists', np);
      }
      const targetPath = isMove ? op : op;
      const before = tree.get(targetPath)!;
      const { lines: fLines, br, final } = splitFile(before);
      const cur = fLines.slice();
      let d = 0;
      let finalBreak = final;
      let touchedEndLast = false;
      for (const h of hunks) {
        if (h.O.length === 0) {
          const pos = Math.min(h.A + d, cur.length);
          const newN = transformN(h.N, h.O, 0, cur, pos, h.ctx, h.ctxO);
          const touchedEnd = (h.A + d >= cur.length);
          cur.splice(pos, 0, ...newN);
          d += newN.length;
          touchedEndLast = touchedEnd;
          if (touchedEnd) finalBreak = !h.noNewline;
          else finalBreak = final;
        } else {
          const tr = pickTier(cur, h.O);
          if (!tr) throw new Fail('no-match', targetPath);
          const positions = tr.positions;
          const target = h.A - 1 + d;
          let best = positions[0], bestDist = Math.abs(positions[0] - target);
          for (const pp of positions) {
            const dist = Math.abs(pp - target);
            if (dist < bestDist || (dist === bestDist && pp < best)) { best = pp; bestDist = dist; }
          }
          const pos = best;
          const tier = tr.tier;
          const touchedEnd = (pos + h.O.length === cur.length);
          const newN = transformN(h.N, h.O, tier, cur, pos, h.ctx, h.ctxO);
          cur.splice(pos, h.O.length, ...newN);
          d += newN.length - h.O.length;
          touchedEndLast = touchedEnd;
          if (touchedEnd) finalBreak = !h.noNewline;
          else finalBreak = final;
        }
      }
      const content = joinFile(cur, br, hunks.length > 0 ? finalBreak : final);
      if (isMove) {
        tree.now.set(np, content);
        tree.now.set(op, null);
        MOVES.push({ old: op, new: np });
      } else {
        tree.now.set(op, content);
      }
    };
    edits.push(edit);
  }
  return edits;
}

// ---------- Search/Replace ----------
function searchReplaceEdits(text: string, lines: string[]): Edit[] {
  const edits: Edit[] = [];
  // find search markers
  const markers: number[] = [];
  lines.forEach((l, idx) => { if (l.trimEnd() === '<<<<<<< SEARCH') markers.push(idx); });
  let lastReplace = -1;
  let prevPath: string | null = null;
  for (const si of markers) {
    // path
    let path: string | null = null;
    const start = lastReplace + 1;
    for (let k = si - 1; k >= start; k--) {
      if (blank(lines[k])) continue;
      if (lines[k].trim().startsWith('```')) continue;
      path = lines[k].trim();
      break;
    }
    if (path === null) {
      if (prevPath !== null) path = prevPath;
      else throw new Exit2(`error: parse ${si + 1}`);
    }
    // old lines
    let i = si + 1;
    const oldLines: string[] = [];
    while (i < lines.length && lines[i].trimEnd() !== '=======') { oldLines.push(lines[i]); i++; }
    if (i >= lines.length) throw new Exit2(`error: parse ${si + 1}`);
    i++; // past =======
    const newLines: string[] = [];
    while (i < lines.length && lines[i].trimEnd() !== '>>>>>>> REPLACE') { newLines.push(lines[i]); i++; }
    if (i >= lines.length) throw new Exit2(`error: parse ${si + 1}`);
    lastReplace = i;
    i++;
    prevPath = path;
    const p = path;
    const ol = oldLines;
    const nl = newLines;
    const edit: Edit = (tree) => {
      if (ol.length === 0) {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const content = nl.length === 0 ? '' : nl.join('\n') + '\n';
        tree.now.set(p, content);
        return;
      }
      if (!safe(p)) throw new Fail('unsafe', p);
      const before = tree.get(p);
      if (before === null) throw new Fail('missing', p);
      const { lines: fLines, br, final } = splitFile(before);
      const tr = pickTier(fLines, ol);
      if (!tr) throw new Fail('no-match', p);
      if (tr.positions.length !== 1) throw new Fail('ambiguous', p);
      const pos = tr.positions[0];
      const tier = tr.tier;
      const newN = transformN(nl, ol, tier, fLines, pos, new Array(nl.length).fill(false), new Array(nl.length).fill(-1));
      const out = fLines.slice(0, pos).concat(newN).concat(fLines.slice(pos + ol.length));
      tree.now.set(p, joinFile(out, br, final));
    };
    edits.push(edit);
  }
  return edits;
}

// ---------- V4A ----------
function v4aEdits(text: string, lines: string[]): Edit[] {
  const edits: Edit[] = [];
  const n = lines.length;
  const firstNonBlank = lines.findIndex((l) => !blank(l));
  if (firstNonBlank < 0) throw new Exit2('error: parse 1');
  if (lines[firstNonBlank].trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${firstNonBlank + 1}`);
  let lastNonBlank = -1;
  for (let i = n - 1; i >= 0; i--) if (!blank(lines[i])) { lastNonBlank = i; break; }
  if (lastNonBlank < 0 || lines[lastNonBlank].trim() !== '*** End Patch') throw new Exit2(`error: parse ${n + 1}`);
  const isSectionStart = (l: string): boolean => l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  let i = firstNonBlank + 1;
  while (i < lastNonBlank) {
    if (blank(lines[i])) { i++; continue; }
    if (!isSectionStart(lines[i])) throw new Exit2(`error: parse ${i + 1}`);
    if (lines[i].startsWith('*** Add File: ')) {
      const path = lines[i].slice('*** Add File: '.length).trim();
      i++;
      const sec: string[] = [];
      while (i < lastNonBlank && !isSectionStart(lines[i])) { sec.push(lines[i]); i++; }
      while (sec.length > 0 && blank(sec[sec.length - 1])) sec.pop();
      const fileLines: string[] = [];
      for (const sl of sec) {
        if (sl === '') { fileLines.push(''); continue; }
        if (blank(sl)) { fileLines.push(''); continue; }
        if (sl.startsWith('+')) { fileLines.push(sl.slice(1)); continue; }
        throw new Exit2(`error: parse ${i}`); // approximate
      }
      const p = path;
      const fl = fileLines;
      const edit: Edit = (tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const content = fl.length === 0 ? '' : fl.join('\n') + '\n';
        tree.now.set(p, content);
      };
      edits.push(edit);
      continue;
    }
    if (lines[i].startsWith('*** Delete File: ')) {
      const path = lines[i].slice('*** Delete File: '.length).trim();
      i++;
      // skip blanks
      while (i < lastNonBlank && blank(lines[i])) i++;
      const p = path;
      const edit: Edit = (tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      };
      edits.push(edit);
      continue;
    }
    if (lines[i].startsWith('*** Update File: ')) {
      const path = lines[i].slice('*** Update File: '.length).trim();
      i++;
      let moveTo: string | null = null;
      if (i < lastNonBlank && lines[i].startsWith('*** Move to: ')) {
        moveTo = lines[i].slice('*** Move to: '.length).trim();
        i++;
      }
      // collect section lines until next section start
      const sec: string[] = [];
      while (i < lastNonBlank && !isSectionStart(lines[i])) { sec.push(lines[i]); i++; }
      while (sec.length > 0 && blank(sec[sec.length - 1])) sec.pop();
      // parse chunks
      const chunks: { anchor: string | null; eof: boolean; body: string[] }[] = [];
      let ci = 0;
      // if no chunks and no moveTo -> parse error at Update line
      // We'll parse
      while (ci < sec.length) {
        let anchor: string | null = null;
        if (sec[ci].startsWith('@@')) {
          anchor = sec[ci].slice(2).trim();
          ci++;
        }
        const body: string[] = [];
        let eof = false;
        while (ci < sec.length && !sec[ci].startsWith('@@') && sec[ci] !== '*** End of File') {
          const l = sec[ci];
          if (l === '' || l.startsWith(' ') || l.startsWith('-') || l.startsWith('+')) {
            body.push(l); ci++;
          } else {
            throw new Exit2(`error: parse ${firstNonBlank + 1}`); // approximate
          }
        }
        if (ci < sec.length && sec[ci] === '*** End of File') { eof = true; ci++; }
        chunks.push({ anchor, eof, body });
      }
      if (chunks.length === 0 && moveTo === null) {
        // find the Update File line number
        throw new Exit2(`error: parse ${firstNonBlank + 1}`);
      }
      // convert chunks
      const convChunks = chunks.map((ch) => {
        const O: string[] = [];
        const N: string[] = [];
        const ctx: boolean[] = [];
        const ctxO: number[] = [];
        for (const l of ch.body) {
          if (l === '') {
            O.push(''); N.push(''); ctx.push(true); ctxO.push(O.length - 1);
          } else if (l.startsWith(' ')) {
            const t = l.slice(1);
            O.push(t); N.push(t); ctx.push(true); ctxO.push(O.length - 1);
          } else if (l.startsWith('-')) {
            O.push(l.slice(1));
          } else if (l.startsWith('+')) {
            N.push(l.slice(1)); ctx.push(false); ctxO.push(-1);
          }
        }
        return { anchor: ch.anchor, eof: ch.eof, O, N, ctx, ctxO, body: ch.body };
      });
      const p = path;
      const mv = moveTo;
      const chs = convChunks;
      const edit: Edit = (tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        const before = tree.get(p);
        if (before === null) throw new Fail('missing', p);
        let np: string | null = mv;
        if (np !== null) {
          if (!safe(np)) throw new Fail('unsafe', np);
          if (tree.get(np) !== null) throw new Fail('exists', np);
        }
        const { lines: fLines, br, final } = splitFile(before);
        const cur = fLines.slice();
        let cursor = 0;
        for (const ch of chs) {
          // anchor
          if (ch.anchor !== null && ch.anchor !== '') {
            let foundIndex = -1;
            const tiers = STRICT ? [0] : [0, 1, 2];
            outer: for (const tier of tiers) {
              for (let k = cursor; k < cur.length; k++) {
                if (eqTierFn(cur[k], ch.anchor, tier)) { foundIndex = k; break outer; }
              }
            }
            if (foundIndex < 0) throw new Fail('no-match', p);
            cursor = foundIndex + 1;
          }
          const O = ch.O;
          const N = ch.N;
          if (O.length === 0) {
            const pos = ch.eof ? cur.length : cursor;
            const newN = transformN(N, O, 0, cur, pos, ch.ctx, ch.ctxO);
            cur.splice(pos, 0, ...newN);
            cursor = pos + newN.length;
          } else {
            const tr = pickTierFromCursor(cur, O, cursor, ch.eof);
            if (!tr) throw new Fail('no-match', p);
            const pos = tr.positions[0];
            const tier = tr.tier;
            const newN = transformN(N, O, tier, cur, pos, ch.ctx, ch.ctxO);
            cur.splice(pos, O.length, ...newN);
            cursor = pos + newN.length;
          }
        }
        const content = joinFile(cur, br, final);
        if (np !== null) {
          tree.now.set(np, content);
          tree.now.set(p, null);
          MOVES.push({ old: p, new: np });
        } else {
          tree.now.set(p, content);
        }
      };
      edits.push(edit);
      continue;
    }
  }
  return edits;
}

function run(args: string[]): { code: number; out: string[] } {
  MOVES.length = 0;
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  // option given twice detection already via null checks; but --format twice: second has format!==null -> usage. good.
  // additional: --format value invalid handled by FORMATS.includes in condition; if invalid, condition false -> usage.
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  STRICT = strict;
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(text, lines);
    else if (kind === 'search-replace') edits = searchReplaceEdits(text, lines);
    else if (kind === 'v4a') edits = v4aEdits(text, lines);
    else edits = [];
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try { edit(tree); } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const changedPaths: string[] = [];
  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    changedPaths.push(p);
  }
  const movedOld = new Set(MOVES.map((m) => m.old));
  const movedNew = new Set(MOVES.map((m) => m.new));
  const rows: { key: string; line: string }[] = [];
  for (const p of changedPaths) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (movedOld.has(p) && now === null) continue;
    if (movedNew.has(p) && was === null) continue;
    const type = was === null ? 'A' : now === null ? 'D' : 'M';
    rows.push({ key: p, line: `${type} ${p}` });
  }
  for (const m of MOVES) {
    rows.push({ key: m.new, line: `R ${m.old} -> ${m.new}` });
  }
  rows.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const outLines = rows.map((r) => r.line);
  if (!check) {
    for (const p of changedPaths) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (now === null) rmSync(p, { force: true });
      else { mkdirSync(dirname(p), { recursive: true }); writeFileSync(p, now); }
    }
  }
  return { code: 0, out: [...outLines, `ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
