## What changed

Replaced the proof hole in `Sheaf.AlgebraicGeometry.GenericOpenImmersionConstructibility`
without changing its statement or public imports. The proof uses the existing source
Deligne theorem, converts the equivalent constructibility predicates and boundedness
formulations, and proves horizontal pasting of the specified derived exchange maps using
derived pullback coherence and the mates correspondence. Updated the node's proof route,
proof dependencies and proof origin; removed its obsolete tool-use approvals.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.Etale.exists_nonempty_open_isBoundedConstructible_derived_open_pushforward`
(node `thm-fin-deligne-generic-open`). Added zero holes; zero holes remain in the delivered
module. The existing source declaration
`AlgebraicGeometry.Etale.exists_hasConstructibleDirectImageBaseChangeOn` remains admitted in
its upstream module, unchanged by this delivery. This is a proof from an existing admitted
declaration, including a complete proof of the formulation and exchange-map conversions.

## No longer needed

The following proof imports were removed; their role in the geometric induction is supplied
by the existing source Deligne theorem:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`
- `WeilConjectures.SixFunctors.BaseChange.Etale`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.ConstructibleSheaf.OpenClosed`
- `WeilConjectures.SixFunctors.Finite.BaseChange`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Paper.ExchangeIdentityPasting`
- `Sheaf.AlgebraicGeometry.ZeroDimensionalNoetherianFiniteDiscrete`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Sheaf.AlgebraicGeometry.FiniteBoundaryReconstruction`
- `Sheaf.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper`
- `WeilConjectures.AlgebraicGeometry.ChowLemma.ClosedModel`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `Sheaf.AlgebraicGeometry.ProperStability`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `Sheaf.AlgebraicGeometry.OpenClosedRecollement`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `Sheaf.AlgebraicGeometry.CoordinateGenericDimension`
- `Sheaf.AlgebraicGeometry.FiniteBoundaryComparison`
- `Sheaf.AlgebraicGeometry.FiniteGenericRadicialSmoothing`
- `Sheaf.AlgebraicGeometry.FiniteRadicialExchangeDescent`
- `Sheaf.AlgebraicGeometry.ProjectiveCoordinateBoundary`
- `Sheaf.AlgebraicGeometry.SmoothGenericDirectImage`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful`

The old proof-dependency edges below are removed. The statement dependencies remain;
these are removals from this proof, with no claim that another target does not need them.

- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-exchange-forget-coefficients`
- `lem-weil-pbc-etale-underived-exchange-restriction`
- `lem-weil-pbc-etale-restriction-injectives`
- `def-weil-pbc-constructible-complexes` (still a statement dependency)
- `lem-wf-affine-noetherian-components`
- `lem-weil-pbc-exchange-identity-pasting`
- `lem-pqf-qc-immersion-open-closed-factor`
- `lem-fin-closed-immersion`
- `lemma-weil-pbc-finite-exchange`
- `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`
- `lemma-nagata-immersion-open-in-scheme-image`
- `lem-sc-zero-dim-noetherian-finite-discrete`
- `lem-kun-dimension-extension`
- `lem-fin-coordinate-generic-dimension`
- `lem-fin-projective-coordinate-boundary`
- `lem-asd-smooth-generic-direct-image`
- `lem-fin-finite-boundary-reconstruction`
- `lem-kun-projective-implies-proper`
- `lem-chow-closed-model`
- `thm-weil-pbc-bounded-below`
- `lem-kun-proper-stability`
- `lem-fin-finite-boundary-comparison`
- `lem-fin-generic-radicial-smoothing`
- `thm-weil-pbc-universal-homeomorphism-invariance`
- `sbc-def-base-change-map` (still a statement dependency)
- `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`
- `lem-weil-pbc-finite-closed-map-finite-fibres`
- `lem-sf-derived-homology-long-exact`
- `thm-constructible-serre`
- `lem-cbc-open-closed-recollement`
- `lem-sc-open-immersion-pushforward-fully-faithful`
- `lem-sf-derived-truncation-triangle`
- `lem-weil-pbc-derived-direct-image-triangulated`
- `lem-weil-pbc-derived-exchange-triangulated`
- `lem-fin-radicial-exchange-descent`

All old `tool_uses` entries are withdrawn: `prop-weil-pbc-inverse-image-modules-exact`, `lem-weil-pbc-exchange-forget-coefficients`, `lem-weil-pbc-etale-underived-exchange-restriction`, `lem-weil-pbc-etale-restriction-injectives`, `lem-pqf-qc-immersion-open-closed-factor`, `lemma-weil-pbc-finite-exchange`, `lem-weil-pbc-ringed-topoi-derived-pushforward-composition`, `lem-weil-pbc-exchange-identity-pasting`, `thm-weil-pbc-bounded-below`, `lem-kun-proper-stability`, `thm-weil-pbc-universal-homeomorphism-invariance`, `lem-sf-derived-homology-long-exact`, `thm-constructible-serre`, `lem-cbc-open-closed-recollement`, `lem-sf-derived-truncation-triangle`, `lem-weil-pbc-derived-direct-image-triangulated`, `lem-weil-pbc-derived-exchange-triangulated`, `lem-wf-affine-noetherian-components`, `lem-sc-zero-dim-noetherian-finite-discrete`, `lem-kun-projective-implies-proper`, `lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`, `lem-weil-pbc-finite-closed-map-finite-fibres`, `lemma-nagata-immersion-open-in-scheme-image`, `lem-chow-closed-model`, `lem-kun-dimension-extension`, `lem-sc-open-immersion-pushforward-fully-faithful`.

## Where the brief, the DAG or earlier work was wrong

The old route planned a fresh dimension induction and Deligne devissage, while the source
library already contains the geometric theorem in a stronger base-open formulation.
The remaining work is substantive: equivalent constructibility and boundedness predicates,
and equality of the canonical exchange maps under pasting. These conversions are proved
here rather than assumed. No target, definition or public signature is changed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
