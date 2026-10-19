## What changed

Filled eight theorem proofs in `Sheaf.Paper.IntegralHeartLocalModel`: scalar section
unit and multiplication, constant presheaf additivity, local injectivity and
surjectivity of the constant unit, extension functor laws, and additivity of point
and scheme realizations. Existing public signatures, definitions, and public
imports are unchanged.

Retained and checked private proofs of constructibility of zero and its transport
through isomorphisms, cohomology constructibility, truncation constructibility,
exactness of constant module sheafification, the scalar PID property, finiteness
of homology, and conversion of projective local models to finite free models
with the cohomology comparison on the same charts. Added a private proof of the
scalar ring's Noetherianity and complete local coefficient hypotheses, using
`Padic.finite_module_adic_complete_and_hom` and transport along `ULift.ringEquiv`.
These helpers do not close the remaining main theorem.

Proof-only imports added relative to the shared module:
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty`,
`Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`,
`Mathlib.RingTheory.AdicCompletion.Topology`,
`Mathlib.LinearAlgebra.FreeModule.PID`, `Mathlib.RingTheory.Flat.TorsionFree`,
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, and
`Mathlib.RingTheory.Noetherian.Basic`.

The module compiles through the required remote compiler. A separate compilation
of the complete candidate source with `#print axioms` confirms that all eight
closed public theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

## Proved and sorry left

Closed 8 of the 9 original theorem holes:

- `integralHeartScalarSection_one`
- `integralHeartScalarSection_mul`
- `integralHeartConstantPresheaf_additive`
- `integralHeartConstantUnit_isLocallyInjective`
- `integralHeartConstantUnit_isLocallySurjective`
- `integralHeartExtension_laws`
- `integralHeartPointRealization_additive`
- `integralHeartRealization_additive`

No holes were added or split off. The single remaining original hole is
`AlgebraicGeometry.ProEtale.integralHeartLocalModel`
(node `det-lem-int-integral-heart-local-model`). No definition contains `sorry`.
This is a partial delivery, not a proof of the main local-model theorem.

## No longer needed

None. Restored the current shared module's three planned proof-dependency imports
(`Sheaf.Paper.IntegralCohomologicalAdicCriterion`, `Sheaf.Paper.IntegralModels`, and
`Sheaf.SixFunctors.ProEtale.DerivedCompletion`) when checking the retained sandbox
against current sources. No existing import, DAG dependency, or module is pruned.
The main theorem's planned route has not been replaced.

## Where the brief, the DAG or earlier work was wrong

The earlier report omitted several proof-only imports and the retained private
helpers; they are listed above. Provider interruptions left some compile and dry-run
logs empty. Their outcomes have now been checked and the candidate recompiled;
no previous push of this item was found.

The remaining work is a category and coefficient transport, rather than a missing
proof of a declared dependency. `integral_cohomological_adic_criterion` is stated
for inverse-limit ring-sheaf modules, using a coefficient field in the scheme
universe. Here the field may be in an independent universe and coefficients use
its canonical small presentation. `IsSfbStratifiedPerfect` also supplies sieve-local
models in slice module categories, whereas this theorem requires scheme covers
and internal-module realizations. The private projective-to-free helper completes
the scalar freeness and local cohomology computation once exact realization and
the transported projective models are supplied. The other outstanding comparison
must identify the published canonical reduction-limit completeness with
`SmallAdicCompletion.IsDerivedComplete`. None of these identifications has been
assumed, and the remaining theorem and its hypotheses are unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
