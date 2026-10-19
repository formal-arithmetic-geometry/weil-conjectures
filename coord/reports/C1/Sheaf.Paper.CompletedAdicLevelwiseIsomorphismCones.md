## What changed

Proved `AlgebraicGeometry.Scheme.completedAdic_levelwise_isomorphism_cones` in
`Sheaf.Paper.CompletedAdicLevelwiseIsomorphismCones`, with its signature unchanged.
A proved private helper establishes joint conservativity by representing an arrow
as a localized chain map and applying Mathlib's levelwise quasi-isomorphism criterion.
Every functor then preserves the resulting isomorphism, including every derived
inverse-limit pair quantified in the first clause.

For completeness, `reconstructionKoszulIntrinsicComparison` identifies the existing
intrinsic unit with the functorial unit followed by an isomorphism.
`koszulReconstruction` therefore makes `reconstructionCompletionUnit` invertible.
Joint conservativity applied to the zero arrow kills a tower whose evaluations
vanish; `Functor.isZero_rightDerivedFunctor_obj` kills its derived inverse limit.
Naturality of `reconstructionCompletionUnit` proves the final morphism criterion
by cancellation. These arguments use the existing declarations of KoszulReconstruction;
its still-unproved assertions remain dependencies rather than new holes in this delivery.

Added the proof import `Mathlib.Algebra.Homology.Functor` and retained the proof
import `Sheaf.Paper.KoszulReconstruction`. Updated the existing node's proof,
proof dependencies, proof origin, and obsolete tool approvals to match the Lean.
No definitions, statements, public imports, consumers, or target signatures changed.

Validation: the final proof compiled through `lcompile.py` in 7.8 seconds.
The zero-object instance is introduced only inside the theorem proof; the original
module-level scope commands are unchanged. The delivery declaration/axiom probes
are checked by the required dry run. All source lines have at most 100 characters.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Scheme.completedAdic_levelwise_isomorphism_cones`
(node `lem-weil-pbc-levelwise-isomorphism-cones`).

Holes added: zero. Holes left in the delivered module: zero.
No new modules or split-off statements. This is a proof from existing declarations,
not a decomposition. The private helper
`completedAdicEvaluation_jointly_conservative` is fully proved.

## No longer needed

Removed these proof imports:

- `Sheaf.Algebra.Homology.KFlatClosure`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Sheaf.Paper.AdicCoefficientDatum`.
- `Sheaf.Paper.CompletedRlimFunctor`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`.

The first three belong to the obsolete completion-exactness/cone calculation.
The generic datum and intrinsic-completion presentations are unnecessary because
the theorem uses the already imported completed-adic presentation and its
unit-compatible reconstruction API. The Rlim clause needs only functoriality of
its explicitly quantified functor; its realization theorem is unnecessary here.
The explicit triangle argument is replaced by the localization criterion.
The public imports are preserved.

Removed direct proof dependencies `def-weil-triangulated-category`,
`lem-sf-triangle-morphism-iso`, and `prop-weil-pbc-rlim-functoriality`.
Removed the stale top-level tool approvals `lem-pur-derived-change-of-rings`,
`lem-pc-kflat-resolution`, and `lem-pc-kflat-cone-direct-sum`.
Their associated modules are not needed directly by this proof; some remain
transitive dependencies of the reconstruction or coefficient constructions.
No claim is made that those modules are globally unreachable.
The node is not a unit's own statement or realized proof step, and the unit's
reconstruction route remains intact.

## Where the brief, the DAG or earlier work was wrong

The theorem's older docstring describes a longer completion-exactness/cone route.
The reviewed DAG already allowed the natural reconstruction argument; the Lean
now implements it directly, using the existing explicit intrinsic-unit comparison.
The dependency records also include newer coefficient presentations; the theorem's
unchanged completed-adic signatures have all needed corresponding declarations
in `CompletedAdicCoefficientDatum`, `CompletedAdicIntrinsicCompletion`, and
`KoszulReconstruction`, so no interface repair or duplicate definition is needed.

Searches through the prescribed `msearch.py` LeanFinder, Loogle, and grep found
Mathlib's `DerivedCategory.isIso_Q_map_iff_quasiIso` and
`HomologicalComplex.quasiIso_iff_evaluation`, rather than a completed-adic theorem.
Reading the source library also found the existing
`Functor.isZero_rightDerivedFunctor_obj`. These give the shorter proof above.

On resumption the sandbox contained dispatcher metadata only, with no interrupted
delivery or proof packet to repeat. Its existing `.budget` was retained unchanged.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
