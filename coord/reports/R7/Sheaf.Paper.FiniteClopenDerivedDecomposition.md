## What changed

Partial proof delivery for `Sheaf.Paper.FiniteClopenDerivedDecomposition`.
All public declarations and definitions retain their statements and bodies except for theorem
proofs. Ten of sixteen original holes are closed; six original named theorem holes remain.
No declarations are withdrawn, no new public declarations are introduced, and no holes are added.

The module equivalence uses the existing concrete gluing construction, with a Fin reindexing
that avoids enlarging the published module universe. Its sectionwise scalar, restriction and
morphism equations are proved. The strict Roos comparison uses the additive comparison and
preservation of products by the existing right adjoint. Finite support, constructibility and Tor
bounds are transported along the actual open-square pullback comparison. Finite ranges give
common intervals even for an empty partition. Integral bounds follow by the actual reduction
comparison. The tensor/reduction theorem is assembled from the existing coefficient calculus.

Private proved helpers express transposition of tower complexes, the functorial Roos comparison,
and invariance of support, constructibility and Tor amplitude under isomorphism. The tensor/reduction
theorem is moved before integral bounds so the latter can use it. The new instance-selection commands are scoped per declaration; see
`coord/changes/R7-finite-clopen-local-instance-selection.md`. The node records the implemented
partial route and explicitly preserves the route of the remaining holes. No unit route is bypassed.

Validation: the full delivered module compiled on the compile server, exit 0, without warnings,
in 21.9 seconds with declaration-scoped instance selection. Empty family, empty components, and distinct component bounds
are covered by the finite-union/finite-range arguments; no nonempty-index assumption was added.

## Proved and sorry left

Holes closed (all names have prefix `WeilConjectures.PurityFiniteSetting.`):

- `clopenRestriction_exact`
- `clopenResidue_isUnit`
- `finiteClopen_module_equivalence`
- `finiteClopen_strict_roos`
- `finiteClopen_finite_bounds`
- `finiteClopen_finiteTor_iff`
- `finiteClopen_finite_equivalences`
- `finiteClopen_integral_bounds`
- `finiteClopen_tensor_and_reduction`
- `finiteClopen_empty`

Original holes left, each exactly a named `by sorry` theorem with its original source and proof
docstring, all attached to `lem-pur-finite-clopen-derived-decomposition`:

- `finiteClopen_unbounded_decomposition`
- `finiteClopen_constructible_equivalences`
- `finiteClopen_scalar_extension`
- `finiteClopen_coefficient_units`
- `finiteClopen_finite_restriction_identification`
- `finiteClopen_integral_restriction_identification`

Count: 10 original holes closed, 6 original holes retained, 0 added, 0 split off.
The imported proof-dependency declarations may themselves contain existing holes; this is a proof
from their published statements, as required for this stage, not a claim that their axioms are closed.

## No longer needed

Removed direct proof imports (the public import list is unchanged):

- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.CategoryTheory.SetSheafCoverDescent`
- `Sheaf.CategoryTheory.SiteModuleSheafGluing`
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Limits.HasLimits`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

These lower-level tools are provided behind the selected dependency interfaces where needed;
the delivered proofs do not invoke them directly. No module or node is withdrawn. The five
original declared dependencies remain needed by either the implemented proofs or the six remaining
original holes; no global module pruning is claimed. In particular the unused field-descent and
integral-descent imports are not added to a partial proof merely to restate their planned use.

## Where the brief, the DAG or earlier work was wrong

`Sheaf.Paper.ClopenRoosIntegralDescent` publicly imports this item for `clopenRing`,
`clopenSiteInclusion`, `clopenRestriction` and the associated instances. Thus the node's planned
reverse import is a Lean import cycle. This dependency is currently held by S8; its source was
not adapted. Its stated subcategory equivalences also concern ordinary completed-ring restriction,
whereas this item's equivalence concerns the recorded completed integral pullback; the missing
restriction-identification theorem is needed to connect them. The packet preserves both statements
and reports this interface issue instead of changing another group's module without a forced edit.

The generic finite-clopen derived calculus introduces unconstrained coefficient-universe parameters
when typeclass inference is allowed to choose its maximum-universe instances. Local instance
selection prevents those new imports from changing the existing statements. The delivered proofs
compile without raising the compile or heartbeat limits. Attempts at the two unbounded/scalar
comparison drafts remain in scratch notes only; neither draft is represented as a closed theorem.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
