## What changed

Proved `AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_boundary` with its
signature unchanged. The existing, proved upstream theorem
`AlgebraicGeometry.Etale.boundedConstructible_of_upperStar_of_rightDerivedLowerStar`
already realizes this blueprint lemma, following the same localization, proper-image,
finite-reflection and final-triangle argument. The wrapper explicitly proves the equivalence
between the two bounded constructibility predicates, packages the coefficient exponent,
and transports the pushforward hypothesis through `rightDerivedFunctorPlusCompatibility`.

Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility`,
and `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`.
Public imports, existing declaration signatures and definitions are unchanged.
The assigned node now records this reuse and its comparison dependency.

Validation: the complete module compiles through `lcompile.py` with exit code 0 and no
warnings (7.4 seconds). Both new nontrivial import directions were checked and are acyclic.
The interval conversion uses min/max and covers empty schemes and reversed chosen bounds;
it requires neither nonemptiness nor an extra coefficient hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isBoundedConstructible_of_finite_boundary`
(node `lem-fin-finite-boundary-reconstruction`).
No holes added, no split-offs, and no `sorry` remains in the delivered module.
This is a proof from an existing source theorem, not a decomposition.
The delivery does not claim to close all transitive assumptions of that theorem.

## No longer needed

Removed these proof imports from the assigned module:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`
- `Sheaf.AlgebraicGeometry.FiniteReflectsBoundedConstructible`
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`
- `Sheaf.AlgebraicGeometry.ProperBoundedConstructible`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`

The old direct proof dependencies below are no longer needed by this wrapper as separate
Sheaf obligations. The existing source theorem carries the localization argument internally;
its source dependencies remain available through its import. This is local pruning, not a
claim that every listed module has become unreachable from all other targets.

- `lem-weil-pbc-finite-type-over-noetherian`
- `def-weil-finite-integral-morphism`
- `lem-cbc-open-closed-recollement`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exact-functor-derived-functor`
- `lem-fin-extension-by-zero`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-exact-functor-complex-cohomology`
- `lem-pc-right-derived-functor-triangulated`
- `def-weil-size-convention`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-dplus-injective-representative`
- `def-weil-pbc-direct-image`
- `lem-weil-derived-direct-image-composition`
- `lem-fin-proper-bounded-constructible`
- `lem-sf-derived-homology-long-exact`
- `prop-constructible-derived-subcategory`
- `lem-fin-finite-reflects-derived`
- `lem-fin-closed-immersion`

All original top-level `tool_uses` approvals have been removed because the wrapper no longer
invokes those separate planned obligations. No UNIT realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan did not record that the source library now already proves this same blueprint lemma
in `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteBoundary`. Reusing it is shorter
than reconstructing its argument from the Sheaf statements. The two constructibility notions
agree for the finite ring by the existing comparison theorem, and the Plus/unbounded derived
pushforwards agree by the existing compatibility isomorphism. No mathematical statement
repair, consumer adaptation or change record is needed.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
