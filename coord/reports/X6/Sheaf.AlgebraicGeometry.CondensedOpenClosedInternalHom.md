## What changed

Repaired reviewer C-01d82 point S3.5 from returned head `01d82ebe5`: changed
`Mathlib.CategoryTheory.HomCongr` to a plain proof-only import in
`Sheaf.CategoryTheory.ProjectionInternalHom`. Its only use is in the proof of
`CategoryTheory.projectionInternalHomMap_isIso`.

Proved `AlgebraicGeometry.ProEtale.CondensedRing.openClosedInternalHomFormulas` by a fully proved generic projection/internal-Hom argument in the new module
`Sheaf.CategoryTheory.ProjectionInternalHom`. The retained concrete map definitions remain in `CondensedOpenClosedInternalHomMaps`; the derived localization and support projection arguments are implemented in `CondensedSupportDerivedLocalization` and `CondensedSupportProjectionFormula`. The localization proof lifts the existing abelian closed-support and closed-counit results through module scalar transport, derives joint detection by exact homology, and proves mixed vanishing.

## Proved and sorry left

Closed 1 of 1 original direct holes:
`AlgebraicGeometry.ProEtale.CondensedRing.openClosedInternalHomFormulas`
(node `lem-sfb-open-closed-internal-hom-formulas`). Zero holes added, zero split off.
All new modules have zero direct holes, including
`AlgebraicGeometry.ProEtale.CondensedRing.condensedSupportDerivedLocalization`,
`AlgebraicGeometry.ProEtale.CondensedRing.openClosedSupportProjectionFormula`, and
`CategoryTheory.projectionInternalHomMap_isIso`. Every private helper is proved.
Existing imported holes are unchanged; this is a proof from the stated library interfaces,
not a claim that all transitive axioms are already eliminated.

The repair retry confirmed that the retained sandbox already contains the requested
plain import, which differs from the returned public import. All five delivered modules
were rechecked through `lcompile.py --all` in this repair session on 2026-10-19:
maps 5.4 s, formal argument 0.0 s, localization 4.0 s, projections 5.9 s, and item
7.3 s; exit code 0, no diagnostics. There are zero direct holes across all five modules.
The main theorem signature and
all six relocated definition blocks were compared against current shared sources
and are byte-identical. Every delivered Lean line is at most 100 characters.
Empty strata, zero coefficient ring, and arbitrary unbounded inputs remain allowed.

## No longer needed

The public reexport of `Mathlib.CategoryTheory.HomCongr` was removed as requested
by reviewer C-01d82; the plain import remains needed by the isomorphism proof.

The original proof-only imports below were removed. The proof uses the existing normalized
pullback tensor comparison, so an independent sectionwise-module comparison and K-flat
projection descent are unnecessary. These modules may still occur transitively elsewhere;
no whole module is claimed pruned from the targets' import closure.

- `Sheaf.Paper.ModuleObjects`.
- `Sheaf.CategoryTheory.SheafTensor`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`.
- `Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.

The following explicit imports were also removed because their interfaces are already
publicly available through the common maps module:

- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`.

Pruned direct proof dependencies from the original eleven-step plan (the existing tensor
comparison supplies the tensor construction): `sk-def-sfb-module-objects`,
`sk-def-sfb-sheaf-tensor`, `def-weil-sheaf-of-modules-category`,
`def-sfb-modobj-relative-tensor`, `def-pur-sheaf-tensor-product`,
`lem-weil-pbc-proetale-ringed-open-closed`,
`lem-weil-pbc-proetale-immersion-limit-preservation`,
`lem-weil-pbc-ringed-topoi-module-pullback-tensor`,
`lem-weil-pbc-left-adjoint-preserves-colimits`,
`lem-pur-ringed-site-grothendieck-abelian`, `def-pc-tensor-complex-sheaves`,
`def-pc-kflat-complex`, `def-pc-flat-sheaf-modules`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-exact-functor-derived-factorization`, and
`lem-weil-pbc-site-derived-tensor-descent`. Exactness, scalar transport, adjunctions and
coefficient conventions remain in the imported support and tensor interfaces.
Removed obsolete parent tool-use approvals for the ringed localization, immersion limit
preservation, ringed pullback tensor comparison, ringed-site Grothendieck, K-flat resolution,
and site-derived tensor descent nodes listed above.
No unit statement or unit proof step is bypassed: the unit has no realized statement or
proof-step attachment to this auxiliary node. The removed exploratory
`Mathlib.CategoryTheory.Adjunction.Mates` import is not needed by the formal proof.

## Where the brief, the DAG or earlier work was wrong

The returned version unnecessarily exposed the proof-only `HomCongr` import.
The repair changes its visibility to comply with stage 3 point 5. The resumed dry run also found the two newer tensor-projection consumers missing from the earlier change record; its Users table has been refreshed for the current library.

The earlier split left the derived localization and projection formulas as separate holes. The existing module APIs are sufficient to prove both: exact derived functors commute with homology, and the normalized pullback tensor comparison gives the required restriction calculations. No target statement or existing declaration signature was changed. A fresh downstream scan finds 300 transitive consumers; the change record now lists all of them with current holders. The newer direct importers `Sheaf.SixFunctors.ClosedImmersionTensorProjection` and `Sheaf.SixFunctors.OpenImmersionTensorProjection` use relocated adjunction/projection names. Public reexport preserves their definitions verbatim, so neither needs adaptation. `openSupportHomMap` itself is mentioned only in the original item. Empty strata, the zero ring and unbounded inputs
are covered by the same abstract argument. The delivery does not change definitions used
to interpret any target statement.

## New nodes

`def-sfb-open-closed-internal-hom-comparisons` records the six original concrete definitions
relocated verbatim into their common maps module. The original item publicly reexports them;
all existing consumers retain the same declarations. The change record is
`coord/changes/X6-open-closed-hom-map-relocation.md`.

`lem-sfb-projection-internal-hom-formal` records the proved abstract Yoneda construction,
evaluation transpose, and simultaneous two-variable naturality.

`lem-sfb-condensed-support-derived-localization` records the proved open unit, closed counit,
supported closed unit, mixed vanishing, and joint detection for exact derived module functors.

`lem-sfb-condensed-support-projection-formula` records the proved canonical tensor projections.
Its two proof dependencies are derived localization and normalized pullback tensor comparison.

All four are new to the shared repository, retained from or completed after the interrupted
attempt. None leaves a new hole. DAG proof text and dependencies follow the final Lean proof.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
