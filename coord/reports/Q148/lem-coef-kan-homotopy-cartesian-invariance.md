# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-homotopy-cartesian-invariance.json`: item, statement and hypotheses retained; three proof steps added; no new nodes and no Mathlib leaves.
- `citations.json`: five verbatim statement quotations covering every node cited by every proof step.
- `report.md`: this report. No Lean file, compiler, Lake build, live repository or launcher file was written.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, its blueprint tag, and the homotopy-cartesian/Kan path terminology. There is no sorry-free project declaration stating the item. The item's `lean_audit` remains `none`; the existing project declarations and Mathlib declarations do not attach the full arbitrary-object invariance assertion.

## WANTED

WANTED: archival copy of Charles Rezk, `Fibrations and homotopy colimits of simplicial sheaves`, Section 2.3, printed p. 4, https://rezk.web.illinois.edu/rezk-sharp-maps.pdf, for the weak-equivalence invariance of homotopy-cartesian square presentations. The source was read online and is not archived under `literature/`; the proof is therefore recorded as agent-written from the explicit path-model reduction.

## Findings and corrections

No `STATEMENT-DISPUTED` issue was found. The imported statement correctly allows all eight simplicial sets to be non-Kan or empty and requires strict commutation with every square edge; I preserved those clauses. The proof uses the already existing nodes `lem-coef-kan-fibrant-path-recognition`, `lem-coef-kan-homotopy-pullback-invariance`, and `lem-coef-kan-quillen-model-right-proper-core`. Their statements give, respectively, the functorial fibrant replacement and recognition criterion, invariance of the explicit path pullback for Kan complexes, and the Kan--Quillen weak-equivalence/model axioms. No helper node is needed: the argument is a direct three-step application of these statements and two-out-of-three.

I searched the whole DAG and current blueprint for an equivalent objectwise-invariance statement, including the Rezk Section 2.3 wording, and found no duplicate or same-as blueprint node. The item's inherited LeanFinder, LeanSearch, Loogle and Mathlib grep records were retained after reading their results; they found only generic path-object, fibration and ordinary pullback declarations, not this theorem. No new Mathlib search record was needed because no node was created and the item already carries the required searches.

## Not duplicates

No new nodes were created, so there are no new-node/existing-node duplicate pairs. The existing `lem-coef-kan-homotopy-pullback-invariance` is strictly narrower: it compares path pullbacks of already Kan cospans, while this item compares the homotopy-cartesian predicate on arbitrary strict squares after applying fibrant replacement.

## Review by Q148

I read `coord/brief-stage1.md`, `stages/1-dag.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, the B--E sections of `coord/delivery-errors.md`, the item node, its chapter and unit records, and the main-20261015 blueprint ancestor `prop-coef-integral-exceptional-adjoint.proof.md`. The item is not the unit key node, so no unit record was edited. The blueprint paragraph served is the displayed derived coefficient-adjunction paragraph's consequence (a), namely objectwise invariance of homotopy-cartesian square presentations.

For Step 1 I checked the full statement of `lem-coef-kan-fibrant-path-recognition`: it supplies a single functorial replacement `r:S→RS` obtained from a trivial-cofibration/Kan-fibration factorization. I checked the full statement of `lem-coef-kan-quillen-model-right-proper-core`: its functorial Kan--Quillen model structure has the stated weak equivalences and therefore the model two-out-of-three property. Naturality of `r` gives `r_S ≫ R(e)=e ≫ r_{S'}` for each corner weak equivalence; with both unit maps weak equivalences, two-out-of-three verifies that every `R(e)` is a weak equivalence. Functoriality verifies strict commutation of all four transformed edges. This step does not assume any original corner is Kan or nonempty.

For Step 2 I read the complete statement of `lem-coef-kan-homotopy-pullback-invariance`. It requires Kan complexes in both cospans, three objectwise weak equivalences, and the two strict cospan equations. The outputs `RX,RY,RZ` and their primed versions are Kan by Step 1's replacement choice; the transformed square equations supply exactly the required hypotheses. The node's coordinate formula gives the displayed map `h:P→P'`, including postcomposition of the path by `Rα_Z`; constant paths are carried to constant paths by that formula. No fibration or nonemptiness condition on the original eight objects is smuggled in.

For Step 3 I again checked the complete recognition statement: it identifies homotopy-cartesianness of each arbitrary square with weak equivalence of its constant-path comparison `RQ→P_R`. The coordinate definition makes `h∘c=c'∘Rα_Q` a strict equality. Step 1 supplies that `Rα_Q` is a weak equivalence and Step 2 supplies that `h` is one; the Kan--Quillen model structure supplies two-out-of-three, so `c` is a weak equivalence exactly when `c'` is. This proves both implications and covers empty and non-Kan original corners through the replacements.

I checked the edge cases of an empty corner, an identity corner map, a terminal base, and a square whose two path pullbacks are empty: all are handled by the same functorial formulas, with no appeal to a chosen point. Every citation quote in `citations.json` is copied verbatim from the cited node's current statement. The three proof steps are 665, 606 and 741 characters, so none hides a long unextracted lemma. There are no off-unit tool uses, no SGA sources, no statement changes, and no cycles.

## Unfinished work

None for this one-level stage-1 split. The item is ready for the required remote dry run and direct delivery; the cited prerequisite nodes remain separate DAG work below this item.
