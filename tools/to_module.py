#!/usr/bin/env python3
"""Convert Lean files to the Lean module system, the way the source library (slopmaster2) writes them.

Usage:
  tools/to_module.py [--check] [--no-fixes] PATH...   PATH is a .lean file or a directory (searched for *.lean)
  tools/to_module.py --live [--check]                 the whole conversion of this repository in one command:
                                                      lean/Sheaf, lean/TargetsCheck.lean and lean/Challenge.lean

Each file gets, as upstream does (e.g. WeilConjectures/AlgebraicGeometry/Curve/FieldExtension.lean):
  1. `module` as the first command, after the leading non-doc comment block (the copyright header);
  2. every `import X` turned into `public import X` (upstream convention: all 1845 upstream modules
     import publicly; only `import all X` lines, used to unfold a private body, stay non-public and
     are left untouched here);
  3. `@[expose] public section` after the imports and after the module docstring `/-! ... -/`
     that directly follows them (or directly after the imports if there is none). Like upstream,
     the section is not closed with `end`: it ends at the end of the file.
  4. a `private` declaration whose name is used where other modules can see it (the signature of a
     non-private declaration, the body of a non-private definition, abbreviation, instance or
     structure, which `@[expose]` exposes, or a top-level command such as `variable`) loses its
     `private`: Lean refuses a private name in exposed text (`Unknown identifier`). The check reads
     text only and repeats until nothing changes; each name made public is printed. A `private`
     theorem used only inside proofs stays private.
  5. the repairs listed in tools/to_module_fixes.tsv (path relative to lean/, kind, declaration):
       heartbeats <decl> [N]   `set_option maxHeartbeats N in` (default 1600000) before the declaration
                               (before its docstring and attributes), where the converted file needs it;
       public <decl>           remove `private` from that declaration (when step 4 does not see the use).
     A row whose declaration is not found is reported and the exit code is 1.
Everything else (docstrings, `set_option`, `open ... in`, `noncomputable section`,
`attribute [local instance]`) is left as is; the library option `autoImplicit = false` comes from
lakefile.toml and is unaffected. No statement is changed.

Idempotent: a file already in module form is left alone (missing pieces are completed).
--check prints the files that would change and exits 1 if there is any; nothing is written.
--no-fixes does steps 1-3 only.
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
FIXES = os.path.join(HERE, "to_module_fixes.tsv")
LEAN = os.path.join(os.path.dirname(HERE), "lean")
HEARTBEATS = "1600000"

IMPORT = re.compile(r"^(\s*)import(\s+)(?!all\b)")
ANY_IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s")
SECTION = re.compile(r"^\s*(?:@\[expose\]\s*)?public\s+section\b")


def _skip_comment(lines, i):
    """lines[i] starts a block comment `/-`; return the index after the line closing it."""
    depth = 0
    while i < len(lines):
        s = lines[i]
        j = 0
        while j < len(s):
            if s.startswith("/-", j):
                depth += 1
                j += 2
            elif s.startswith("-/", j):
                depth -= 1
                j += 2
                if depth == 0:
                    return i + 1
            else:
                j += 1
        i += 1
    return i


def convert(text):
    lines = text.split("\n")
    # 1. leading non-doc comments and blank lines
    i = 0
    while i < len(lines):
        s = lines[i].strip()
        if s == "" or s.startswith("--"):
            i += 1
        elif s.startswith("/-") and not s.startswith("/-!") and not s.startswith("/--"):
            i = _skip_comment(lines, i)
        else:
            break
    if i < len(lines) and lines[i].strip() == "module":
        i += 1
    else:
        lines.insert(i, "module")
        i += 1
        if i < len(lines) and lines[i].strip() != "":
            lines.insert(i, "")
        i += 1 if i < len(lines) and lines[i].strip() == "" else 0
    # 2. the import block (imports, blank lines, line comments)
    last_import = i - 1
    j = i
    while j < len(lines):
        s = lines[j].strip()
        if ANY_IMPORT.match(lines[j]):
            lines[j] = IMPORT.sub(r"\1public import\2", lines[j], count=1)
            last_import = j
            j += 1
        elif s == "" or s.startswith("--"):
            j += 1
        else:
            break
    # 3. @[expose] public section
    if any(SECTION.match(l) for l in lines):
        return "\n".join(lines)
    k = last_import + 1
    while k < len(lines) and lines[k].strip() == "":
        k += 1
    if k < len(lines) and lines[k].lstrip().startswith("/-!"):
        k = _skip_comment(lines, k)
    elif k > last_import + 1:
        k = last_import + 1  # insert right after the imports
    ins = ["", "@[expose] public section", ""]
    lines[k:k] = ins
    # tidy: no more than one blank line around the inserted block
    out = "\n".join(lines)
    out = re.sub(r"\n{3,}(@\[expose\] public section)", r"\n\n\1", out)
    out = re.sub(r"(@\[expose\] public section)\n{3,}", r"\1\n\n", out)
    if not out.endswith("\n"):
        out += "\n"
    return out


def _decls(text):
    import stage2_delivery as s2  # the tools' own reader of declarations
    return s2, s2.declarations(text)


def expose_private(text):
    """Step 4. Returns (text, [names made public])."""
    if not re.search(r"\bprivate\b", text) or "@[expose] public section" not in text:
        return text, []
    s2, decls = _decls(text)
    m = s2.mask(text)
    priv = [d for d in decls if d["short"] and re.search(r"\bprivate\b", m[d["start"]:d["kw_pos"]])]
    if not priv:
        return text, []
    def regions(d):
        r = [(d["kw_pos"], d["sig_end"])]
        if d["kw"] not in s2.THEOREM_KW:
            r.append((d["sig_end"], d["end"]))
        return r
    seen = []                                   # exposed text: non-private declarations and top-level commands
    pos = 0
    for d in sorted(decls, key=lambda x: x["start"]):
        seen.append((pos, d["start"]))
        pos = max(pos, d["end"])
        if d not in priv:
            seen += regions(d)
    seen.append((pos, len(m)))
    made = []
    while True:
        hit = None
        for d in priv:
            if d["short"] in made:
                continue
            last = d["short"].split(".")[-1]
            pat = re.compile(r"(?<![\w'])" + re.escape(last) + r"(?![\w'])")
            if any(pat.search(m, a, b) for a, b in seen if not (a >= d["start"] and b <= d["end"])):
                hit = d; break
        if hit is None:
            break
        made.append(hit["short"]); seen += regions(hit)
    out = text
    for d in sorted((d for d in priv if d["short"] in made), key=lambda x: -x["start"]):
        head = re.sub(r"\bprivate[ \t]+", "", out[d["start"]:d["kw_pos"]], count=1)
        out = out[:d["start"]] + head + out[d["kw_pos"]:]
    return out, made


def read_fixes():
    """path relative to lean/ -> [(kind, declaration, argument)]"""
    out = {}
    if os.path.exists(FIXES):
        for line in open(FIXES, encoding="utf-8"):
            p = line.rstrip("\n").split("\t")
            if line.startswith("#") or len(p) < 3:
                continue
            out.setdefault(p[0], []).append((p[1], p[2], p[3] if len(p) > 3 and p[3] else None))
    return out


def apply_fixes(text, rows):
    """Step 5. Returns (text, [problems])."""
    bad = []
    for kind, name, arg in rows:
        s2, decls = _decls(text)
        d = next((x for x in decls if name in (x["name"], x["short"])), None)
        if d is None:
            bad.append(f"{kind} {name}: no such declaration"); continue
        if kind == "public":
            head = re.sub(r"\bprivate[ \t]+", "", text[d["start"]:d["kw_pos"]], count=1)
            text = text[:d["start"]] + head + text[d["kw_pos"]:]
        elif kind == "heartbeats":
            line = f"set_option maxHeartbeats {arg or HEARTBEATS} in\n"
            at = d["start"]
            before = text[:at].rstrip()
            if before.endswith("-/"):                       # the docstring belongs to the declaration
                o = before.rfind("/--")
                if o >= 0:
                    at = o
            at = text.rfind("\n", 0, at) + 1
            prev = text[:at].split("\n")
            k = len(prev) - 2                                # walk up over `set_option ... in` / `open ... in` lines
            while k >= 0 and re.match(r"\s*(set_option|open)\b.*\bin\s*$", prev[k]):
                k -= 1
            if not any("maxHeartbeats" in l for l in prev[k + 1:]):
                text = text[:at] + line + text[at:]
        else:
            bad.append(f"{kind} {name}: unknown kind")
    return text, bad


def files(paths):
    for p in paths:
        if os.path.isdir(p):
            for r, ds, fs in os.walk(p):
                ds[:] = sorted(d for d in ds if not d.startswith("."))
                for f in sorted(fs):
                    if f.endswith(".lean"):
                        yield os.path.join(r, f)
        else:
            yield p


def main(argv):
    check = "--check" in argv
    nofix = "--no-fixes" in argv
    paths = [a for a in argv if not a.startswith("--")]
    if "--live" in argv:
        paths = [os.path.join(LEAN, x) for x in ("Sheaf", "TargetsCheck.lean", "Challenge.lean")]
        paths = [p for p in paths if os.path.exists(p)]
    if not paths:
        print(__doc__)
        return 2
    changed = 0
    total = 0
    problems = 0
    fixes = {} if nofix else read_fixes()
    used = set()
    for f in files(paths):
        total += 1
        old = open(f, encoding="utf-8").read()
        new = convert(old)
        if not nofix:
            rel = os.path.relpath(os.path.abspath(f), LEAN)
            new, made = expose_private(new)
            for n in made:
                print(f"to_module: {rel}: `private` removed from {n} (used in exposed text)")
            if rel in fixes:
                used.add(rel)
                new, bad = apply_fixes(new, fixes[rel])
                for b in bad:
                    problems += 1
                    print(f"to_module: {rel}: FIX NOT APPLIED: {b}")
        if new != old:
            changed += 1
            if check:
                print("would convert", f)
            else:
                open(f, "w", encoding="utf-8").write(new)
    verb = "would change" if check else "changed"
    if "--live" in argv:
        for rel in sorted(set(fixes) - used):
            problems += 1
            print(f"to_module: FIX NOT APPLIED: {rel} is in tools/to_module_fixes.tsv and is not a file of the library")
    print(f"to_module: {total} files, {changed} {verb}" + (f", {problems} fix(es) not applied" if problems else ""))
    return 1 if ((check and changed) or problems) else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
