## What changed

Proved `AlgebraicGeometry.Scheme.sfOpenTensor` by transporting the existing unbounded
pro-etale derived projection formula through the canonical coefficient equivalences.
The three transport comparisons are constructed from equivalence units and derived
composition comparisons. The theorem and both displayed bifunctors keep their signatures
and definitions. Two proved private functor-composition identities normalize the
bifunctor endpoints without unfolding derived tensor constructions. Updated the item
node to follow this shorter proof.

## Proved and sorry left

Closed the sole original hole, `AlgebraicGeometry.Scheme.sfOpenTensor`
(`lem-trf-open-tensor`): 1 of 1. Added 0 holes. No sorry remains in the delivery.
The existing dependencies of the public exactness/realization interfaces are unchanged.

## No longer needed

The explicit ringed-site reconstruction is unnecessary because the existing proved
`AlgebraicGeometry.ProEtale.derivedOpenImmersionLowerShriekProjectionIso` already
constructs the termwise tensor comparison and descends it to unbounded derived categories.
The blueprint unit route remains: the projection formula is used for the open-extension
Tor-amplitude argument; its implementation is reused, not replaced by another unit route.

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
- `Sheaf.CategoryTheory.LocalizedModuleExactIndependent`
- `Sheaf.CategoryTheory.RingedSliceExtensionTensor`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescent`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

No longer direct proof dependencies of this node (they may still be used elsewhere or
transitively by retained public interfaces):
- `def-weil-pbc-proetale-site`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-proetale-ringed-open-comparison`
- `lem-pur-site-restriction-module-adjunction-exact`
- `def-weil-derived-pullback-tensor-hom`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `lem-weil-pbc-left-adjoint-preserves-colimits`
- `def-pc-tensor-complex-sheaves`
- `def-pc-kflat-complex`
- `def-pc-flat-sheaf-modules`
- `lem-pc-sheaf-modules-tensor-closed`
- `lem-pc-kflat-resolution`
- `def-weil-proetale-inverse-image`
- `def-pur-localized-ringed-site`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `lem-weil-pbc-site-derived-tensor-descent`

Withdrew nine obsolete explicit tool-use approvals for the old reconstruction;
retained `lem-sf-exact-functor-derived-triangulated`, which the transport still uses.
No module is withdrawn; no claim is made that these modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The original search missed the proved fixed-scalar pro-etale formula in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`.
It has a different coefficient presentation, so it requires genuine equivalence
transport, supplied in the proof. The finite-ring hypothesis supplies the Noetherian
hypothesis of the existing flat-pullback instance. Identity/empty opens, zero inputs
and the zero coefficient ring require no extra assumptions: the comparisons are
functorial equivalence units and the existing formula applies uniformly.

The retained report initially claimed completion while the retained item still had
its original hole; the recovered scratch proof had a final type-comparison timeout.
The two private identities proved by reflexivity supply the explicit composition API
needed at that junction. The recovered proof passed the remote compile and axiom probe without warnings.
The preflight interface check required moving private helper variables from a
section into the helper binders; no public command or interface was changed. There are no statement/definition changes, new nodes or forced adaptations.
The required delivery dry run also checks the declaration/axiom inventory.

## Second reading by G5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
