# Worker report: lem-sfb-compactification-over-base

## Files written

- \`dag/nodes/sec-six-functors-basics/lem-sfb-compactification-over-base.json\`: existing statement, split into two proof steps; no new node and no Mathlib leaf.
- \`citations.json\`: verbatim quotations for the two cited nodes.
- \`report.md\`: this report.

## Attachments

No attachment. I searched the exact blueprint id, the project docstring tag, compactification terminology, and likely declaration names in \`/home/ubuntu/weil-src-slopmaster2/WeilConjectures\`; no sorry-free project declaration states this item. The declarations in the read-only upstream master are reference material only and were not used as completion evidence.

## WANTED

None. The current blueprint proof and the cited Nagata theorem are available locally.

## Corrections and source comparison

The imported statement agrees with \`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-setting/lem-sfb-compactification-over-base.md\`. I retained all hypotheses and the conclusion. I expanded the imported single paragraph into two steps. Step 1 now explicitly proves that the given \(S\)-morphism is separated and of finite type and that \(Y\) is qcqs; its finite-type inference cites the existing \`lemma-nagata-finite-type-to-separated-target\`. Step 2 applies \`sk-thm-nagata-compactification\` over \(Y\). No new node was justified: the separatedness check is a direct diagonal/base-change argument, and the target qcqs checks are standard consequences of the stated structure-map hypotheses. The imported \`cites_outside_uses\` flag is retained.

## Not duplicates

No new nodes were created. The existing \`lemma-nagata-finite-type-to-separated-target\` is reused; it states finite type in a commutative triangle with separated target, whereas this item asserts compactification of an \(S\)-morphism and additionally checks separatedness and qcqs hypotheses.

## Review by NN

I read the current item source and proof file, the fixed chapter record \`dag/chapters/sec-six-functors.json\`, the setting definition \`dag/nodes/sec-six-functors-basics/sk-def-sfb-dc-setting.json\`, the cited \`sk-thm-nagata-compactification\` node, and the cited \`lemma-nagata-finite-type-to-separated-target\` node. The latter's statement says verbatim: “In a commutative triangle \(T\\to Y\\to B\), if \(T\\to B\) is of finite type and \(Y\\to B\) is separated, then \(T\\to Y\) is of finite type.” The Nagata node says verbatim that every separated finite-type morphism to a qcqs base has a dense compactification. Both quotes are copied into \`citations.json\`.

Step 1 uses the finite-type-over-separated-target statement exactly with \(T=X\), \(Y=Y\), and \(B=S\). For separatedness of \(f\), I checked the diagonal square: \(X\\times_YX\\hookrightarrow X\\times_SX\) is the base change of the closed diagonal of \(a_Y\), and \(\Delta_f\) is the corresponding base change of the closed diagonal of \(a_X\). Thus the diagonal of \(f\) is closed. The hypotheses that \(a_X\) is finite type, \(a_Y\) separated, and both structure maps are quasi-compact/quasi-separated are exactly those in the item. The standard composition and stability facts then give \(Y\) quasi-compact and quasi-separated from \(a_Y\) and qcqs \(S\). I declared the off-unit finite-type lemma in \`split_report.tool_uses\` with the reason its statement is used.

Step 2 checks that the base for the Nagata theorem is \(Y\), which Step 1 established qcqs, and that \(f\) is separated and finite type. The theorem supplies a dense compactification, which entails the requested compactification in the sense of \`sk-def-nagata-sketch-data\`. No field, Noetherian, finite-presentation, or projectivity hypothesis was added.

I tested edge cases in the statement: if \(X\) is empty, the diagonal and compactification assertions reduce to the empty morphism and the theorem still applies; if \(S\) or \(Y\) is affine, the qcqs checks are immediate; and no argument assumes nonemptiness. The proof does not identify coefficient categories or use any SGA source.

I checked delivery-errors B–E: the statement introduces all objects and retains its source; no clause was moved into a new node; the only non-elementary imported facts are cited nodes with verbatim quotes; all proof dependencies equal the union of step uses; the blueprint \`is/from/same_as\` metadata is filled; the item Mathlib searches were run in two phrasings for each search kind and recorded exactly in the node and \`searches.jsonl\`; and no dependency path returns to this item. No Lean was written, compiled, or built.

## Unfinished work

No mathematical work remains in this one-level split. The dry run passed; nothing is to be delivered or pushed by this worker.


## Validation

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NN lem-sfb-compactification-over-base --no-push` completed successfully on the rerun: `OK (not pushed) deliver/NN/lem-sfb-compactification-over-base at 66390e9c66: preflight passed`. The first invocation reported only generated coordination-index files in its temporary worktree; rerunning after cleanup passed. The global `check_dag.py` output contains pre-existing repository-wide dependency/reachability warnings and cycles, with no item-specific failure. No files outside this sandbox were changed and nothing was pushed.

## Second reading by NN

- Item statement: compared every hypothesis and conclusion with current main-20261015 `lem-sfb-compactification-over-base.md`; exact agreement. The base S is qcqs, X/S separated finite type, Y/S separated quasi-compact, and f an S-morphism. The definition requires the open immersion to be quasi-compact; the cited Nagata statement supplies precisely that. No statement dispute or statement change.
- Step 1 (repaired): checked the statements of `def-weil-scheme-over-base`, `def-weil-finite-type-morphism`, `lem-pc-separated-quasi-separated`, and `lem-weil-pbc-qcqs-morphism-permanence` (clause 2). They give the structure-map equality, quasi-compactness of a_X, quasi-separatedness of a_Y, and then quasi-compact X and qcqs Y. Read Stacks schemes.tex, definition-quasi-compact / lemma-quasi-compact-affine (01K3/01K4), lemma-closed-immersion-quasi-compact (01K7), lemma-composition-quasi-compact, and lemma-separated-permanence (01KU). Every non-elementary inference now has its own cited statement; no finiteness hypothesis on Y/S is used beyond quasi-compactness.
- Step 2 (repaired): checked `lem-weil-pbc-separated-cancellation` clause (b), `lem-weil-pbc-proper-fp-permanence` clause (f), and `lem-weil-pbc-qcqs-morphism-permanence` clause (1), against schemes.tex lemma-compose-after-separated (01KV), morphisms.tex lemma-permanence-finite-type (01T8), and schemes.tex lemma-quasi-compact-permanence (03GI). The first two apply to a_X=a_Y f; the third applies to quasi-compact X and quasi-separated Y from Step 1. Read Mathlib IsSeparated.of_comp (Separated.lean:256), locallyOfFiniteType_of_comp (FiniteType.lean:72), and QuasiCompact.of_comp / quasiCompact_of_compactSpace (QuasiSeparated.lean:250/255). Finally local finite type plus quasi-compact is finite type by the cited definition. All uses are statements, not facts hidden in their proofs.
- Step 3 (formerly Step 2): checked `sk-thm-nagata-compactification` against its current main-20261015 section, and opened `sk-def-nagata-sketch-data`. The theorem's base is Y, now proved qcqs, and f has both required morphism properties. Its dense compactification has a quasi-compact open immersion and proper projection; forgetting density gives exactly the item. Read slopmaster2 Compactification/Dense.lean:75 and Defs.lean:193 as confirmation of the cited theorem's recorded interface, without treating upstream master sorries as proofs.
- New nodes: none; no B1–B7 checks or searches for a proposed child are needed. Reused only existing nodes. DAG title, statement, tag, and Mathlib-match searches found existing Mathlib leaves for all ancillary scheme-property facts; no duplicate, elementary child, or restatement was introduced.

Changes and reasons:

1. Replaced the first worker's two steps by three explicit steps, retaining the original statement and final Nagata argument. The first step had uncited separatedness/base-change/composition facts (C1) and compressed the entire hypothesis reduction. The repaired proof cites existing Mathlib leaves rather than making children.
2. Removed `lemma-nagata-finite-type-to-separated-target` from the dependencies. Its current `blueprint_update` states local finite type only, while its old statement and recorded closed declaration disagree about the quasi-compact part. Used the existing exact local-finite-type cancellation leaf instead, and proved quasi-compactness separately. This follows the current blueprint's proof. No other node was edited.
3. Added existing definition dependencies for S-schemes, finite type, separatedness, quasi-separatedness, and quasi-compact schemes; regenerated citations.json with literal current statements for every use in the three steps.
4. Removed the worker-written `split_report.tool_uses`: delivery-errors C8 reserves tool authorizations for the maintainer. All ancillary statements now used are already Mathlib leaves, so the route check needs no off-unit authorization. Nagata is the blueprint's own cited theorem.
5. Ran independent broader Mathlib searches through msearch.py (LeanFinder for open/proper factorization, Loogle name search, grep for compactification/Nagata, LeanSearch for proper ambient schemes). All services responded; no result states the whole item. Kept their actual logs and recorded verdicts. The item remains a split, with zero new Mathlib leaves.

Edge cases and graph checks: empty X needs no point choices; empty Y forces empty X; empty S forces both empty; a field or an affine base is allowed without a Noetherian hypothesis. No bound, positive dimension, finite presentation, or nonemptiness was added. For non-affine qcqs S, the permanence clauses still apply verbatim; no intersection of arbitrary affine opens was assumed affine. A traversal of both statement and proof dependencies of every replacement citation found no path to the item. No SGA route, Lean write, compiler, or Lake/build tool was used. The earlier first-worker review remains above as historical review; the repaired steps and this reading supersede its old dependency and tool-use descriptions.

Second-reader validation: the required `deliver.py NN lem-sfb-compactification-over-base --no-push` completed with `OK (not pushed) deliver/NN/lem-sfb-compactification-over-base at e130c48500: preflight passed`. No validation failure required a further repair. The initial delay was the delivery service worktree-capacity and per-group locks, not a mathematical or preflight failure. The final delivery command repeats preflight before pushing.
