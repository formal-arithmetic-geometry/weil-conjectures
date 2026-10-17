#!/usr/bin/env python3
"""Install only the R4 return-parser/NOANSWER repair; preserve other launcher changes.

Usage: python3 patch_dispatcher.py /path/to/dispatch_all.py
No processes are started or stopped. A running dispatcher loads it on its next restart.
"""
import ast
from pathlib import Path
import shutil
import sys

HELPERS = 'def parse_returns(text):\n    """Read review (branch head) and batch take-out (head) return headers."""\n    returns = {}\n    for match in re.finditer(r"^## (\\S+) \\(([^)]*)\\)\\n(.*?)(?=^## |\\Z)", text, re.M | re.S):\n        item, header, body = match.groups()\n        head = re.search(r"\\b(?:branch\\s+)?head\\s+([0-9a-f]{7,40})\\b", header)\n        if head or "." in item or re.match(r"(lem|lemma|def|prop|thm|cor|rem)", item):\n            returns[item] = (head.group(1) if head else "", body.strip())\n    return returns\n\ndef noanswer_detail(last_file):\n    """Keep fatal worker diagnostics when Codex exits without writing its answer."""\n    try:\n        p = pathlib.Path(last_file).with_name("log.txt")\n        with p.open("rb") as f:\n            f.seek(0, os.SEEK_END)\n            f.seek(max(0, f.tell() - 65536))\n            tail = f.read().decode(errors="replace")\n    except OSError:\n        return ""\n    errors = [line.strip() for line in tail.splitlines() if re.match(r"^ERROR:", line)]\n    return errors[-1] if errors else ""'
OLD = '        ret = {}\n        for m in re.finditer(r"^## (\\S+) \\(([^)]*)\\)\\n(.*?)(?=^## |\\Z)", c, re.M | re.S):\n            h = re.search(r"branch head ([0-9a-f]{7,})", m.group(2))\n            if h or "." in m.group(1) or re.match(r"(lem|lemma|def|prop|thm|cor|rem)", m.group(1)):\n                ret[m.group(1)] = (h.group(1) if h else "", m.group(3).strip())\n'
REAP_LOG = '            log(s.g, "worker ended", item, f"(stage {stage}, {w[\'kind\']}, {int((time.time()-w[\'t\'])/60)} min):", kind, rest[:160])'


def patch(source):
    tree = ast.parse(source)
    names = {n.name for n in tree.body if isinstance(n, ast.FunctionDef)}
    if not {'parse_returns', 'noanswer_detail'} & names:
        marker = '\n\ndef log(*a):\n'
        if source.count(marker) != 1:
            raise ValueError('dispatcher log function changed; inspect before applying')
        source = source.replace(marker, '\n\n' + HELPERS + marker)
    elif not {'parse_returns', 'noanswer_detail'} <= names:
        raise ValueError('partial helper installation; inspect before applying')
    if OLD in source:
        source = source.replace(OLD, '        ret = parse_returns(c)\n', 1)
    elif 'ret = parse_returns(c)' not in source:
        raise ValueError('return reader changed; inspect before applying')
    if 'rest = noanswer_detail(lm)[:260]' not in source:
        if source.count(REAP_LOG) != 1:
            raise ValueError('worker reaper changed; inspect before applying')
        source = source.replace(REAP_LOG,
            '            if kind == "NOANSWER" and not rest:\n'
            '                rest = noanswer_detail(lm)[:260]\n' + REAP_LOG)
    ast.parse(source)
    return source


def main():
    target = Path(sys.argv[1])
    before = target.read_text()
    after = patch(before)
    if after == before:
        print('Already installed:', target)
        return
    backup = target.with_name(target.name + '.maint-R4-return-head.bak')
    if backup.exists():
        raise SystemExit('Backup already exists; inspect before reinstalling: ' + str(backup))
    shutil.copy2(target, backup)
    target.write_text(after)
    print('Installed:', target, 'backup:', backup)


if __name__ == '__main__':
    main()
