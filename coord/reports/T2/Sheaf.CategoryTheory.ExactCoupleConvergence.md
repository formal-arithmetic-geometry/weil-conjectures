## What changed

Proved five auxiliary theorems in `Sheaf.CategoryTheory.ExactCoupleConvergence` without
changing any declaration signature, definition, public import, or existing docstring.
Added the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` for its proved image-subobject
factorization and pushforward lemmas. Updated `def-sp-convergence`'s proof, proof_deps,
and proof_origin to record the actual arguments and the remaining construction.

The proof of `g_factors_limitCycles` preserves, by induction, a lift to each finite
cycle object that is killed by that page's f. DerivedMaps.f_comm, the successor
projection equation, and cancellation of the derived-D inclusion give the induction
step. It needs no explicit formula involving iterated alpha images.

## Proved and sorry left

Proved (five of the original six sorries):

- `CategoryTheory.BigradedExactCouple.limitBoundary_le_cycle`.
- `CategoryTheory.BigradedExactCouple.g_factors_limitCycles`.
- `CategoryTheory.BigradedExactCouple.imageFiltration_antitone`.
- `CategoryTheory.BigradedExactCouple.weakConvergence_comparison`.
- `CategoryTheory.BigradedExactCouple.filtrationStep_comp_quotient_zero`.

The only sorry left in this delivery is the unchanged public theorem
`CategoryTheory.BigradedExactCouple.cycleBoundaryTower_exists`, node
`def-sp-convergence`. Its existing docstring describes the recursive construction and
quotient presentations. No new sorry or new theorem was added. The proved theorems
still depend on existing unfinished theory, including the tower-existence theorem
and the derived-couple construction in `Sheaf.CategoryTheory.ExactCouple`.

Local compilation passed without warnings. The required dry run checks local and
server compilation, declaration signatures, and the delivery preflight.

## No longer needed

No imports were removed; both original public imports are required by the statements.
No existing DAG node or module can be pruned from these proofs. The stronger finite
cycle formula using incoming iterates of alpha, suggested by the docstring of
`g_factors_limitCycles`, is unnecessary for that proof. It has no separate dependency
node or module in the current item, so there is no such import to remove.

## Where the brief, the DAG or earlier work was wrong

The item's DAG node has an empty proof and no proof dependencies, rather than the
numbered proof plan described in the generic brief. The auxiliary-theorem docstrings
supply the intended arguments. The node copy now records the arguments actually
formalized and identifies the tower construction as the remaining obligation.
The original docstring of `g_factors_limitCycles` suggests a stronger formula than
needed; its declaration and mathematical assertion are unchanged.

## Second reading by T2

1. Compared the delivered module with the repository version. All existing declaration signatures,
definitions, public imports, and docstrings are unchanged; the only added import is proof-only.
Verdict: pass.
2. Compiled the module with `lcompile.py`; it compiles cleanly. Searched for forbidden constructs;
there are no axioms, unsafe/opaque declarations, or implementation escapes. The sole remaining
`sorry` is the named `cycleBoundaryTower_exists` theorem already listed above. Verdict: pass.
3. Checked the five proof bodies against their unchanged statements and the available Mathlib and
library lemmas. No new statement was introduced, and no statement was weakened or given extra
hypotheses. Verdict: pass.
4. Checked proof routes and imports. The proof-only Subobject.Limits import is used by the image
factorization arguments; both public imports remain needed by declarations. The finite-cycle
induction is shorter than the stronger formula suggested by the old docstring. Verdict: pass.
5. Checked the DAG node and unit route. `def-sp-convergence` records the actual proof steps,
proof dependencies, and the remaining tower construction; the unit's tower-existence route is
preserved. The assigned unit record `sk-prop-av-pqf-finite` is an unrelated proper-and-quasi-finite
unit with empty realized entries; this pre-existing association was not changed, and no unit
step is bypassed by these auxiliary proofs. Verdict: pass for this delivery.

Changed only the five proofs, the proof-only import, the matching DAG proof metadata, and this
second-reading report section. No holes were added.

A scratch-copy `#print axioms` check of all five closed theorems found only `propext`,
`Classical.choice`, and `Quot.sound`, plus `sorryAx` in the three theorems depending on
the existing tower/derived-couple holes. The filtration antitonicity and quotient-zero
theorems use no `sorryAx`. No proof repair was needed during the second reading; only
the review report was appended.
