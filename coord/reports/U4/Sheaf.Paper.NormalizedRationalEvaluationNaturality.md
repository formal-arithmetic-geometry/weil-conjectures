## What changed

Replaced the proof hole of `WeilConjectures.normalizedRationalEvaluation_naturality`
in `Sheaf.Paper.NormalizedRationalEvaluationNaturality` with a proof of the unchanged
statement. Private proved helpers establish ordinary evaluation naturality, naturality
of the actual completion unit, the normalized integral evaluation equation, and its
rational localization. Tensor-product induction in both localized arrows extends the
pure-tensor equation to arbitrary sums. All existing imports and public signatures stay
unchanged; no definition or upstream module is changed.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.normalizedRationalEvaluation_naturality`
(node `lem-coef-normalized-rational-evaluation-naturality`).
No holes added, no split-off results, and no `sorry` left in the delivered module.
Server `lcompile.py` passed cleanly in 20.5 seconds, with no warnings.
The proof uses the existing normalization theorems in its declared dependencies;
it does not claim those independent dependencies have been proved here.

## No longer needed

None. The proof follows the recorded route and uses all four recorded proof dependencies:
`def-weil-derived-pullback-tensor-hom`, `lem-pod-derived-automorphism-hom-evaluation`,
`def-pur-completed-pullback-tensor-comparison`, and `def-coef-ringed-tensor-hom-model`.
No imports, nodes, or modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Server preflight conservatively classified
the scoped proof commands as an interface change; this is documented in
`coord/changes/u4-normalized-rational-evaluation-private-proof.md`. Both affected
name users were checked and need no adaptation. The partial closed structure only records
naturality in the tensor parameter, so pair naturality is derived from its ordinary
counit normalization, rather than assumed as a field of that structure. The completion
unit is the actual adjunction unit followed by the reduction/tensor and Roos comparison;
its naturality follows from those three natural transformations. Equality is tested
using the injective normalized transpose, without assuming that finite reductions
are faithful or that coefficients are torsion-free.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
