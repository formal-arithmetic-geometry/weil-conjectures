## What changed

Prove the main restriction theorem and the identity theorem of `Sheaf.Paper.IdentityOpenDerivedRestriction` from the
sectionwise common-open comparison and canonical derived-mate normalization. Expose
proved companion APIs in the existing module-pasting, common-open-sections and
unbounded-adjunction-square modules. No existing statement, data definition or public
import is changed. The same ordinary unbounded derived functors and coefficient actions
are used. The existing DAG proof is updated to match this assembly.

Change record: `coord/changes/C8-identity-open-canonical-mate-normalizations.md`.

Consumer checks passed for `TowerLimitTransposeNormalization`,
`SfExactPullbackQuotientAugmentationSquare`, `OpenStarShriekScalarMateSquare` and the
then-current `RingedRestrictionStrictLimitCoherence`. The last consumer subsequently
received its holder's substantially expanded proof. That new source reaches the same
60-second timeout both with this packet's APIs and against the published dependencies;
no consumer is changed in this packet.

## Proved and sorry left

Closed two of the three original holes, node `lem-sfb-identity-open-derived-restriction`:

- `AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_restriction`.
- `AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_restriction_id`.

The original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.identity_open_derived_restriction_comp`
remains, node `lem-sfb-identity-open-derived-restriction`. Its statement and complete
proof plan are unchanged. A candidate proof was elaborated from underived composition,
representative normalization and module_derived_compositor_normalization, but its kernel
conversion exceeds the file limit; no partial proof is left inside the theorem.

Added zero holes; split off zero holes. The companion APIs and all private helpers are
proved. The canonical mate normalization is proved inside the item; there are no new nodes.
Selecting `CategoryTheory.Abelian.toPreadditive` locally before statement elaboration makes
the complex, abelian and localization instance paths uniform. The isolated normalization
compiled cleanly in 8.5 seconds. No limit is raised and no source-library definition or
public attribute is changed.

## No longer needed

Removed the following private proof imports from the item:

- `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
- `Sheaf.AlgebraicGeometry.CoefficientSectionsLocalization`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`.
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`.

The abstract `lem-sfb-exact-postcomposition-kinjective-descent` is not needed: its chosen
quasi-isomorphism-resolution functor is different from the published functor in the item.
The canonical derived mate already has its general cochain normalization in
`lem-sbc-unbounded-exact-adjunction-square`; together with K-injective representative
extensionality this proves precisely the needed descent, composition and identity.

The item does not directly use `lem-sfb-internal-module-operations-transport`,
`prop-pur-kinjective-resolutions-exist`, `lem-weil-proetale-weakly-etale-localization`,
`lem-sfb-coefficient-sections-localization`, or `lem-weil-pbc-right-adjoint-preserves-kinjective`.
Their relevant exactness and resolution interfaces are already supplied by the published
framework and the sectionwise theorem. The corresponding obsolete top-level `tool_uses`
entries are removed in their original order. These modules remain available to other
consumers; no module or source declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The assigned Lean source has three holes and its canonical mate constructions are real.
The old underived existential interfaces did not explicitly connect their normalized
witnesses to those constructions, despite already proving this privately. The public
companion APIs expose that existing equation. The abstract descent node alone does not
identify the actual derived mate with its normalized comparison; the existing general
cochain-mate theorem supplies exactly that identification.

The rework row records a previous quarantine caused by a transitive ProjectiveLineGenusZero
import. The current readable sources are preserved and restored through the assigned
packet; no archive or module is deleted. There are no new nodes and no forced adaptations
of modules held by another group.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
