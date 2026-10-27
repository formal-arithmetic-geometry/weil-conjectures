"""Is a node's own Lean proof written? Read from the live text (the human, 2026-10-24): a node whose own declarations are
sorry-free is proved even when it rests on a `sorry` below; that sorry is the work of the node recording it (sorry
route), and the DAG plan below the node is pruned. tools/target_progress.py counts with it and tools/dag_queue.py cuts
the stage-1/2 walk with it, so the queue never offers work the progress count calls pruned."""
import re
import leanindex as li

_s, _blocks = {}, {}
_DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec|partial|unsafe)\s+)*"
                   r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\b", re.M)
_COMMENTS = re.compile(r"--[^\n]*|/-.*?-/", re.S)


def sorries(m):
    """sorry count of module m in live, -1 when the file is missing"""
    if m not in _s:
        p = li.file_of(m)
        _s[m] = li.sorry_count(p.read_text(errors="ignore")) if p.is_file() else -1
    return _s[m]


_NAME = re.compile(r"\b(?:theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|example)\s+(?:\{[^}]*\}\s*)?([^\s:(\[{]+)")
_where = None


def _declared(blk):
    """the name a declaration block declares, as written after its keyword"""
    x = _NAME.search(blk[:600])
    return x.group(1).removeprefix("_root_.").split(".{")[0] if x else None


def _block_sorry(blk):
    return bool(re.search(r"\bsorry\b|\badmit\b", blk))


def _declaring(m, name):
    """the blocks of module m that declare `name` (not merely mention it)"""
    if m not in _blocks:
        p = li.file_of(m)
        t = _COMMENTS.sub("", p.read_text(errors="ignore")) if p.is_file() else ""
        starts = [x.start() for x in _DECL.finditer(t)] + [len(t)]
        _blocks[m] = [t[a:b] for a, b in zip(starts, starts[1:])]
    return [b for b in _blocks[m] if (d := _declared(b)) and (name == d or name.endswith("." + d))]


def decl_sorry(m, name, _hop=True):
    """True/False: the declaration `name` has `sorry` in its own text; None: not found.
    2026-10-25 (b2audit): read the block that declares `name`, in m or, when m does not declare it, in the module that
    does (a node may list declarations of other modules); a structure field or constructor is read in its parent's
    block. Before, any block of m whose header merely mentioned the short name counted, so a node listing a definition
    used in the statement of a sorried theorem (sk-def-sfb-dc-setting: `boundedConstructible` in the binders of
    `boundedConstructible_rightDerivedLowerStar_obj`) stayed open for that theorem's sorry (178 nodes); the old
    reading remains the last fallback."""
    global _where
    hit = _declaring(m, name)
    if hit:
        return any(_block_sorry(b) for b in hit)
    if _hop:
        if _where is None:
            try: _where = li.scan()[0]
            except Exception: _where = {}
        r = []
        for x in sorted(_where.get(name, ())):
            if x == m: continue
            n = sorries(x)
            r.append(None if n < 0 else False if n == 0 else decl_sorry(x, name, False))
        if r:
            return True if any(v is True for v in r) else False if all(v is False for v in r) else None
    parent = name.rsplit(".", 1)[0] if "." in name else ""
    if parent:
        hit = _declaring(m, parent)
        if hit:
            return any(_block_sorry(b) for b in hit)
    short = name.split(".")[-1]
    hit = [blk for blk in _blocks[m] if re.search(r"\b" + re.escape(short) + r"\b", blk.split(":=", 1)[0][:400])]
    if not hit:
        return None
    return any(_block_sorry(blk) for blk in hit)


def own_open(d, m):
    """the node's own declarations: True if one has sorry, False if all found and sorry-free, None if unknown"""
    l = d.get("lean") if isinstance(d.get("lean"), dict) else {}
    names = ([l["declaration"]] if l.get("declaration") else []) + list(l.get("declarations") or [])
    if not names or not m:
        return None
    r = [decl_sorry(m, x) for x in names]
    if any(x is True for x in r): return True
    if all(x is False for x in r): return False
    return None


def own(d, m):
    """own_open, short-cut by the module's count: a sorry-free module proves every declaration in it"""
    if not m:
        return None
    n = sorries(m)
    return own_open(d, m) if n > 0 else (False if n == 0 else None)


def written(d, m) -> bool:
    return own(d, m) is False
