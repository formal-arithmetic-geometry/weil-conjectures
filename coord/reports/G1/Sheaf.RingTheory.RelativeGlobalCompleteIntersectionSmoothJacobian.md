## What changed

Completed `Algebra.isSmoothAtPrime_iff_exists_jacobian_minor` with its signature and visibility unchanged. Added two completely proved private helpers in the same module: `smooth_jacobian_localization` constructs a submersive presentation of the localization by composing the naive quotient presentation with the localization presentation; `jacobian_left_inverse_of_smooth_localization` localizes the specified conormal basis and takes matrices of the split differential. The main theorem uses direct Cauchy–Binet and the properness of the extended prime ideal to extract an increasing minor outside the prime.

Added proof-only imports `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`, `Mathlib.RingTheory.Localization.Ideal`, and `Mathlib.RingTheory.Localization.Module`. All original public imports remain unchanged. Updated only `proof`, `proof_deps`, and `proof_origin` of the existing node to match the implemented argument. No statements, definitions, instances, public imports, or other modules changed.

The chosen basis from the existing conormal theorem is uniquely specified by its values on the equations. Localizing it uses a real Mathlib construction. The proof introduces no data chosen from an undetermined existence theorem. The module's existing docstring is preserved; its numbered proof describes the original plan, while the updated node and inline comments describe the implementation.

## Proved and sorry left

Closed the single original hole: `Algebra.isSmoothAtPrime_iff_exists_jacobian_minor` (node `lem-weil-pbc-relative-global-complete-intersection-smooth-jacobian`). Both private helpers are proved. No `sorry` remains in the delivered module; no holes were added or split off.

This is a proof from the existing planned declarations, not a claim that its dependency closure is already sorry-free. It uses the existing declarations `Algebra.relativeGlobalCompleteIntersection_conormal_free`, `Algebra.smooth_localization_conormal_split`, and `Matrix.cauchy_binet`, which remain the next proof items. No dependency theorem is modified.

The compiler checked the full theorem without extra hypotheses, including the empty-minor case `c=0`, the empty sum for `c>n`, and arbitrary commutative rings. The reverse implication works without the complete-intersection hypothesis. Local single-file compilation passed without warnings after import pruning.

## No longer needed

Removed the direct proof import `Sheaf.LinearAlgebra.Matrix.LeftInverseMinors` and dependency node `lem-weil-pbc-matrix-left-inverse-minors`. Direct Cauchy–Binet supplies precisely the identity needed, avoiding the size hypothesis and the separate proof that `c ≤ n`.

Removed the direct proof import `Sheaf.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent` and direct dependency node `lem-weil-pbc-principal-localization-naive-cotangent`. Mathlib's naive quotient and localization presentation composition construct the reverse implication without the more elaborate cotangent-complex localization statement. This module remains a transitive dependency of `SmoothLocalizationConormalSplit`, so this delivery does not claim it has become globally unreachable.

No separate variable-renaming lemma, denominator-clearing theorem, nonzero-localization theorem, or additional module is needed. The block-triangular determinant and standard-smooth route are retained through the proved Mathlib composition API and smoothness instance. No unit realization is bypassed: the item is below the realized statements/steps of `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The original plan is longer than necessary: the localized-ideal properness criterion replaces explicit denominator clearing, Cauchy–Binet eliminates the intermediate size bound and scalar-left-inverse-minors lemma, and submersive presentation composition eliminates explicit renaming and cotangent-complex presentation glue. These are refinements below the unit level.

The repository does not contain the fetched `literature/stacks-project/algebra.tex`; the cited Tag 00TE statement and proof were checked at https://stacks.math.columbia.edu/tag/00TE. No new sourced statement or node is introduced.

## Second reading by G1

1. Compared the delivered module against the repository version. The theorem signature and all existing declaration signatures are byte-for-byte unchanged; only proof imports, private helpers, and the theorem proof changed. The node changes update only proof metadata and dependencies.

2. Compiled the delivered module with `lcompile.py`; it succeeds without warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof introduces no additional assumptions and handles the empty-minor and oversized-minor cases through Cauchy–Binet.

3. Checked the proof route against the existing dependency declarations and the Stacks Tag 00TE source. The localized conormal basis and split differential are used to obtain a left inverse, and the reverse implication constructs a smooth localization from the selected Jacobian minor. The existing node statement is unchanged and no new statement was added.

4. Reviewed pruning. The direct left-inverse-minors and principal-localization-naive-cotangent imports are unnecessary for this implementation; direct Cauchy–Binet and Mathlib presentation composition replace them. The remaining imports are used, and the unit route through smooth localization and standard smoothness is retained.

5. The DAG node proof, proof dependencies, and proof origin match the implementation. No new node or split-off theorem is present, and the unit `sk-thm-p1` remains realized.

Changed during second reading: added this review record only; no Lean code or statement changes were needed.
