#!/bin/bash
# The maintainer's duty of stages/2-statements.md §3 rule 7, once per green global build: add the proof-dependency
# imports that are missing (overwritten by a delivery in flight, or of nodes stated or split since), as one commit that
# the next build verifies. Called by ~/cc1/buildloop.sh after a build.py that exited 0; log ~/cc1/proof-imports-cycle.log.
#
#   1  nothing new built since the last run, or the last build not green: do nothing
#   2  tools/add_proof_imports.py --check (no lock, reads only): nothing missing -> no commit, done.
#      The tool itself never adds to a node that is proved, to the two reserved target modules, or an import that
#      closes a cycle.
#   3  under coord/.merge.lock and local/tree.lock (the tool's run, about 25 s): write the imports
#   4  without the locks: compile each touched file alone (tools/lean_file.sh, 60 s)
#   5  under coord/.merge.lock: a file that did not compile loses the lines just added (tried again after the next
#      build: the usual cause is an import landed but not built yet; after 3 failures its pairs go to
#      tools/proof_imports_skip.tsv); the files that compiled are committed, by path, in one commit
# Disable: touch ~/cc1/proof-imports-cycle.off
set -uo pipefail
export PATH=$HOME/.elan/bin:$PATH
REPO=${CYCLE_REPO:-$HOME/weil-conjectures-sheaf}
W=${CYCLE_WORK:-$HOME/cc1/proof-imports}
[ -e "$HOME/cc1/proof-imports-cycle.off" ] && exit 0
cd "$REPO" || exit 0
[ -f tools/add_proof_imports.py ] || exit 0
[ ! -e local/batch/open.json ] && [ ! -e local/batch/landing.json ] || exit 0
mkdir -p "$W"
say() { echo "$(date '+%F %T') $*"; }
read -r RES COMMIT < <(python3 -c "import json;d=json.load(open('local/builds/last.json'));print(d['result'],d.get('commit') or '-')" 2>/dev/null)
[ "${RES:-}" = green ] || exit 0
python3 tools/sorry_ledger.py report --post-build || say "sorry ledger failed; next green cycle retries"
[ "$COMMIT" != "$(cat "$W/cycle.stamp" 2>/dev/null)" ] || exit 0
J=$W/cycle.json
if python3 tools/add_proof_imports.py --check --json "$J" > "$W/cycle.check" 2>&1; then echo "$COMMIT" > "$W/cycle.stamp"; exit 0; fi
grep -q '^missing, to add: [1-9]' "$W/cycle.check" || { say "check failed: $(tail -1 "$W/cycle.check")"; exit 0; }

# Prevent a new batch while the precomputed import plan is applied/checked.
# This journal is not a lock and survives a failed cycle for the maintainer.
python3 -c "import json,pathlib; p=pathlib.Path('local/batch/proof-imports.json');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps({'commit':'$COMMIT'}))"
trap 'rm -f local/batch/proof-imports.json' EXIT
exec 8>> coord/.merge.lock; flock -w 110 8 || { say "merge lock busy; next cycle"; exit 0; }
exec 9>> local/tree.lock;   flock -w 60 9 || { say "tree lock busy; next cycle"; exit 0; }
[ ! -e local/batch/open.json ] && [ ! -e local/batch/landing.json ] || { flock -u 9; flock -u 8; exit 0; }
python3 tools/add_proof_imports.py --apply-plan "$J" > "$W/cycle.write" 2>&1; rc=$?
flock -u 9; flock -u 8
[ $rc = 0 ] || { say "write failed: $(tail -1 "$W/cycle.write")"; exit 0; }
mapfile -t MODS < <(python3 -c "import json;print('\n'.join(sorted({x[0] for x in json.load(open('$J')).get('added', [])})))")
[ ${#MODS[@]} -gt 0 ] || { echo "$COMMIT" > "$W/cycle.stamp"; exit 0; }

GOOD=(); BAD=()
for m in "${MODS[@]}"; do
  f=lean/${m//./\/}.lean
  if out=$(SHEAF_FILE_TIMEOUT=60 tools/lean_file.sh "$f" 2>&1); then GOOD+=("$m"); else BAD+=("$m"); echo "$m: $(echo "$out" | grep -m1 -e error -e Timeout | cut -c1-300)" > "$W/cycle.err.$m"; fi
done

flock -w 110 8 || { say "merge lock busy before the commit; the imports stay in the tree and the next build commits them"; exit 0; }
# a file that failed loses exactly the lines this run added, if it still has them
python3 - "$J" "$W" "${BAD[@]}" <<'PY'
import json, pathlib, sys, time
J, W, bad = sys.argv[1], pathlib.Path(sys.argv[2]), set(sys.argv[3:])
added = [x for x in json.load(open(J)).get("added", []) if x[0] in bad]
fails = W / "cycle-fail.tsv"
count = {}
if fails.exists():
    for l in fails.read_text().splitlines():
        m, n = l.split("\t"); count[m] = int(n)
for m in list(count):
    if m not in bad: del count[m]            # it compiled this time, or nothing was missing for it
skip = pathlib.Path("tools/proof_imports_skip.tsv")
for m in sorted(bad):
    p = pathlib.Path("lean") / pathlib.Path(*m.split(".")).with_suffix(".lean")
    drop = {f"import {d}" for mm, d, _, _ in added if mm == m}
    lines = p.read_text().split("\n")
    p.write_text("\n".join(l for l in lines if l not in drop))
    count[m] = count.get(m, 0) + 1
    if count[m] >= 3:
        with open(skip, "a") as f:
            for mm, d, _, _ in added:
                if mm == m: f.write(f"{m}\t{d}\tthe module did not compile with this run's imports in 3 build cycles ({time.strftime('%F')}); see the maintainer's log\n")
        del count[m]
fails.write_text("".join(f"{m}\t{n}\n" for m, n in sorted(count.items())))
PY
PATHS=(); for m in "${GOOD[@]}"; do PATHS+=("lean/${m//./\/}.lean"); done
git diff --quiet -- tools/proof_imports_skip.tsv || PATHS+=(tools/proof_imports_skip.tsv)
N=$(python3 -c "import json,sys;g=set(sys.argv[1:]);print(sum(1 for x in json.load(open('$J')).get('added', []) if x[0] in g))" "${GOOD[@]}")
if [ ${#PATHS[@]} -gt 0 ] && ! git diff --quiet -- "${PATHS[@]}"; then
  git commit -q -m "Imports of the proof dependencies: $N in ${#GOOD[@]} module(s) (stage 2, rule 7)

Added by tools/add_proof_imports.py after the build of ${COMMIT:0:9}: ${GOOD[*]:0:6}$([ ${#GOOD[@]} -gt 6 ] && echo ' ...'). Each
touched file compiled alone; the next global build verifies them.

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>" -- "${PATHS[@]}" \
    && say "after build ${COMMIT:0:9}: $N import(s) into ${#GOOD[@]} module(s) (${GOOD[*]:0:4}), commit $(git rev-parse --short=9 HEAD)" \
    || say "git commit failed"
else [ ${#GOOD[@]} -eq 0 ] || say "after build ${COMMIT:0:9}: $N import(s) into ${#GOOD[@]} module(s) (${GOOD[*]:0:4}) are already committed (a build's snapshot or a landing took the files)"
fi
flock -u 8
[ ${#BAD[@]} -eq 0 ] || say "did not compile, lines taken back (tried again after the next build): ${BAD[*]} | $(cat "$W/cycle.err.${BAD[0]}" 2>/dev/null | cut -c1-200)"
rm -f "$W"/cycle.err.*
echo "$COMMIT" > "$W/cycle.stamp"
exit 0
