## What changed

The retained A3 proof was installed in the project. The Lean sources were committed by the
server build loop in `a529fddd02` (the target module plus the three supporting modules). The
DAG records and this report were committed separately under the merge lock in the maintenance
commit recorded below.

The target proof closes `CategoryTheory.alphaCompactObjects_small_closed`; the three supporting
modules prove extension closure, a small bounded triangulated hull, and the retract factorization.

## Proved and sorry left

One original sorry was closed: `CategoryTheory.alphaCompactObjects_small_closed`.
The three supporting declarations are complete and contain no sorry. No new sorry was added.

## No longer needed

No existing imports or nodes were pruned. The three supporting modules and their DAG nodes are
needed by the target proof.

## Where the brief, the DAG or earlier work was wrong

The repeated failure is a delivery-tool defect. `deliver3.py` commits the delivery and then
rewrites tracked `tools/stage3_gate.py` and `tools/stage3_delivery.py` before running the clean
working-tree preflight. The rewrite is therefore reported as an uncommitted change and the
preflight rejects every otherwise valid delivery. These are launcher-owned landing tools and
were not edited. The required launcher repair is to perform the gate compatibility rewrite
before the commit, or to exclude the generated compatibility edit from the clean-tree check.

The Lean proof itself compiles one file at a time with `tools/lean_file.sh` in dependency order.
Existing source files changed in this maintenance operation have `.bak` copies beside them.

## New nodes

- `lem-sfb-alpha-compact-extensions`
- `lem-sfb-small-bounded-triangulated-hull`
- `lem-sfb-alpha-compact-factor-through`

Maintenance commit: see the commit made under `SHEAF_LEAD=L flock coord/.merge.lock`.
