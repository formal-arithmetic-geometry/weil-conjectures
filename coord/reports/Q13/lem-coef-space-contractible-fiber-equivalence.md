# Stage-1 report: lem-coef-space-contractible-fiber-equivalence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-space-contractible-fiber-equivalence.json`: item, split in three proof steps; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-space-path-fibration-replacement.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-space-kan-fibration-fiber-criterion.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-space-weak-equivalence-two-out-of-three.json`: statement-only supporting node; no Mathlib match.
- `citations.json`: seven verbatim step citations.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` and the upstream reference source for the item id, contractible homotopy-fiber terminology, and the surrounding coherent mapping-space declarations. No sorry-free project declaration states this criterion.

## WANTED

WANTED: Kerodon, Proposition 3.3.7.6 and Remark 3.4.0.6 (tag 0328), for the path-space fibration replacement and the contractible-homotopy-fiber criterion. The source is online but not archived in `literature/`; no Stacks tag states this infinity-categorical result.

## What was checked and corrected

The item was present as an unsplit statement in a read-only worktree, while the local snapshot did not contain its file. I retained its exact statement, dependencies, source, and blueprint ancestry. I checked the existing definition node `def-cbc-enhanced-diagrams-cones`; it defines Kan complexes, weak homotopy equivalences, path-space homotopy fibers, and weak contractibility exactly as used here.

The proof is split through three smaller facts. The path-space replacement node supplies the Kan fibration `p:E_f→Q`, the constant-path weak equivalence `P→E_f`, and identification of strict fibers with the stated homotopy fibers. The Kan-fibration criterion node is the specialized fiber theorem for a genuine Kan fibration. The two-out-of-three node supplies the cancellation used in both directions. These statements introduce all objects they use and remain unsplit as required for newly created nodes.

I tested the edge cases while checking the statements: the empty map `∅→∅` has vacuously contractible fibers and is a weak equivalence; `∅→*` has a noncontractible empty fiber and is not; and a map `*→BG` can have a misleading ordinary point fiber while its homotopy fiber is noncontractible. Thus the statement correctly uses homotopy fibers rather than set-theoretic fibers.

## Review by Q13

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, and delivery-errors B–E. I read the item node and the complete statement of `def-cbc-enhanced-diagrams-cones`, then checked every proof step against those statements. Step 1 uses only the path-space replacement statement and explicitly takes its Kan-fibration, constant-path weak-equivalence, and strict-fiber clauses. Step 2 uses that replacement, the two-out-of-three statement, and the iff direction of the Kan-fibration criterion to deduce contractibility of every homotopy fiber from weak equivalence of `f`. Step 3 uses the same three statements in the reverse direction. The displayed factorization `f=p∘i` is the construction supplied by the path-space node, and the two-out-of-three hypotheses are checked in the order used.

I searched the whole DAG and blueprint for path-space fiber replacements, Kan-fibration fiber criteria, and two-out-of-three statements before creating each supporting node. I ran the required LeanFinder, Loogle, and Mathlib-grep searches for the item and each new node through `msearch.py`; the exact records are copied into every node's `mathlib_searches`. The returned Mathlib model-category path-object and two-out-of-three declarations do not state the project’s geometric homotopy-fiber criterion without additional comparison theorems, so no Mathlib leaf is claimed. All citations in `citations.json` are verbatim substrings of their cited node statements. No SGA source is used and no Lean file or compiler was run.

## Unfinished work and validation

The three supporting statements remain intentionally unsplit for a later stage-1 worker. The required no-push delivery dry run is the remaining validation step.

## Not duplicates

lem-coef-space-kan-fibration-fiber-criterion vs lem-coef-space-contractible-fiber-equivalence: the new node treats a Kan fibration and its strict vertex fibers; the item treats an arbitrary map and its path-space homotopy fibers, so the new node is the intermediate fibration case rather than the item's statement.
lem-coef-space-path-fibration-replacement vs lem-coef-space-contractible-fiber-equivalence: the new node constructs the path-space Kan fibration and identifies strict and homotopy fibers; it does not assert the contractibility/equivalence criterion of the item.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-coef-space-contractible-fiber-equivalence: the new node is the general composition cancellation property for weak equivalences and has no fibers; the item is the fiberwise characterization of a map.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-cohen-completion-dvr: Kerodon tag 0328 concerns Kan fibrations and simplicial fibers; the existing Stacks tag 0328 concerns Cohen completion of DVRs.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-cohen-rings-exist: Kerodon 0328 is an infinity-categorical fiber criterion; the existing Stacks 0328 is existence of Cohen rings.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-completion-noetherian-quotient-noetherian: the new node is a simplicial homotopy theorem; the existing Stacks 0328 is a commutative-algebra completion theorem.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-cohen-structure-power-series-surjection: the new node concerns strict Kan fibers; the existing Stacks 0328 concerns Cohen structure and power-series surjections.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-flat-local-extension-given-residue-field: the new node has no rings or residue fields; the existing Stacks 0328 is a flat local extension result.
lem-coef-space-kan-fibration-fiber-criterion vs lem-weil-pbc-cohen-coefficient-ring-exists: the new node is the Kan-fibration criterion from Kerodon; the existing Stacks 0328 is coefficient-ring existence.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-cohen-completion-dvr: Kerodon 0328 supplies a path-space fibration replacement, whereas Stacks 0328 supplies a Cohen-completion statement for DVRs.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-cohen-rings-exist: the new node constructs simplicial path spaces; the existing Stacks node constructs Cohen rings.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-completion-noetherian-quotient-noetherian: the new node is about Kan complexes and evaluation maps; the existing Stacks node is about Noetherian quotients under completion.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-cohen-structure-power-series-surjection: the new node has no ring-theoretic hypotheses; the existing Stacks node proves a power-series surjection.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-flat-local-extension-given-residue-field: the new node compares strict and homotopy fibers; the existing Stacks node extends a flat local ring with a prescribed residue field.
lem-coef-space-path-fibration-replacement vs lem-weil-pbc-cohen-coefficient-ring-exists: the new node is a path-space construction; the existing Stacks node is Cohen coefficient-ring existence.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-cohen-completion-dvr: Kerodon 0328 gives two-out-of-three for weak equivalences; Stacks 0328 gives a DVR completion property.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-cohen-rings-exist: the new node concerns composition of simplicial weak equivalences; the existing Stacks node concerns Cohen-ring existence.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-completion-noetherian-quotient-noetherian: the new node is homotopical and has no rings; the existing Stacks node is a Noetherian completion theorem.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-cohen-structure-power-series-surjection: the new node is a categorical closure property; the existing Stacks node is a power-series surjectivity assertion.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-flat-local-extension-given-residue-field: the new node has no local-ring data; the existing Stacks node is a flat local extension lemma.
lem-coef-space-weak-equivalence-two-out-of-three vs lem-weil-pbc-cohen-coefficient-ring-exists: the new node concerns weak equivalence composition; the existing Stacks node concerns existence of a Cohen coefficient ring.

## Second reading by Q13

I independently opened the item and both retained supporting nodes, the definition node `def-cbc-enhanced-diagrams-cones`, the existing node `lem-coef-spaces-homotopy-fiber-detection`, and Kerodon tags 0328, 00ZP and 0101. I also read delivery-errors B–E, GOAL.md and coord/dag-sync.md. The item statement agrees hypothesis by hypothesis with Kerodon Remark 3.4.0.6 together with Proposition 3.3.7.6: the objects are small Kan complexes, the fibers are the explicit path-space homotopy fibers, and “contractible” has the weakly contractible meaning fixed by the cited definition. Kerodon’s “homotopy equivalence” is equivalent to the stated weak homotopy equivalence for Kan complexes by Proposition 3.3.7.6.

- Step 1: checked against the path-fibration node and Kerodon Example 3.1.8.10 (0101); PASS after correcting that node’s source place. The pullback uses evaluation at 0, projection at 1 is a Kan fibration, the constant-path map lies over (Q), and strict fibers are exactly the stated homotopy fibers.
- Step 2: checked against the path-fibration and Kan-fibration criterion nodes and Remark 3.4.0.6/Proposition 3.3.7.6; PASS. The cancellation used for (f=p\circ i) is the elementary cancellation of the component bijection and all based homotopy-group isomorphisms; the path and fiber assertions are the two cited node statements.
- Step 3: checked against the same two node statements and the reverse implication of Proposition 3.3.7.6; PASS. Contractible homotopy fibers become weakly contractible strict fibers, the criterion gives (p), and the same elementary cancellation gives (f).

- New node `lem-coef-space-path-fibration-replacement`: checked B1–B7 against Kerodon Example 3.1.8.10 (0101), Remark 3.4.0.6 (0328), and the explicit homotopy-fiber definition; PASS. It is statement-only, self-contained relative to its cited definition, and strictly smaller than the item.
- New node `lem-coef-space-kan-fibration-fiber-criterion`: checked B1–B7 against Kerodon Proposition 3.3.7.6 (00ZP); PASS. It states the genuine Kan-fibration case with all vertex fibers and introduces no extra hypotheses.

I searched the shared DAG for path-space, Kan-fibration fiber, weak-equivalence cancellation, and homotopy-fiber statements. The existing `lem-coef-spaces-homotopy-fiber-detection` is a broader comparison theorem, but its statement does not provide the path-space construction or the contractible-fiber criterion in the form used here; neither retained node is a duplicate. The initially proposed `lem-coef-space-weak-equivalence-two-out-of-three` was removed: its content is the elementary cancellation of the component bijection and homotopy-group isomorphisms already written in Steps 2–3, so it should not be a new node. Its Mathlib search returned only the abstract model-category two-out-of-three field, which is not a one-line exact declaration for this project’s explicitly defined weak equivalences.

I tested the edge cases (\varnothing\to\varnothing), (\varnothing\to\Delta^0), identity maps, and a point mapping to a nontrivial classifying space. The first and identity cases satisfy the criterion, the empty-to-point map fails because its fiber is empty, and the classifying-space example confirms that ordinary point fibers cannot replace homotopy fibers. No statement dispute or source error was found. No Lean file, compiler, Lake, build, preflight, or live project file was used.

Changes made: deleted the elementary duplicate two-out-of-three node; removed its proof dependencies and citation certificates; wrote the cancellation argument directly in Steps 2–3; corrected the path-fibration node’s source place from Proposition 3.3.7.6 to Example 3.1.8.10 plus Remark 3.4.0.6; updated the item split summary. The final split has two new unsplit nodes and zero Mathlib leaves.
