# canonicalSinglePullbackMap: restore the canonical source comparison interface

## Reason

The item is absent from lean/ and preserved in quarantine by the 2026-10-20
upstream sync. Its rework row records a duplicate derivedPullback environment
error. The old public Sheaf derived-composition import has since been retired;
the adopted source now supplies the composition data and all three declarations
of this item. Recreating their names would collide with the source declarations
whenever both implementations are imported.

Restore the item as a public compatibility import of the source module and
redirect its existing node attachment to that source module. This restores a
usable public interface, rather than deleting the quarantined mathematical
obligation or introducing another definition. The source construction explicitly
uses AlgebraicGeometry.derivedPullback, distinguishing it from the newer
Scheme.Modules.derivedPullback. Its body is still precisely the chosen composition
counit, localized single-complex identification, and leftAdjointUniq comparison.
A compiled rfl check verifies this exact formula. The source invertibility proof
uses the unchanged flat-module theorem and intrinsic flatness of invertible
modules, as the node's existing plan requires.

All three full declaration names, hypotheses, universes, the pinned construction,
and the node's statement/proof dependencies remain available. The old public
LocallyFree import is exported by the source module. No adopted-source file,
parent statement, target statement, or unit route changes. Quarantined parents
remain quarantined pending their own restoration work; their import of this
module continues to be supported. No parent dependency is pruned.

## Old

The file below is the quarantined implementation; there is no current file at
its lean/ path.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback

/-! # The pinned derived pullback comparison on a single module

Source: Stacks Project, Tags 06YD, 06YJ and 08HY.
(blueprint: lem-pc-canonical-single-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The additive structure used in the canonical derived composition comparisons.
Source: Stacks, Tag 0D5S (blueprint: lem-pc-canonical-single-pullback-comparison). -/
abbrev canonicalTensorPullbackAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (tensorPullback f).Additive :=
  (Classical.choose exists_derivedPullbackComposition) f

/-- The specified derived counit, followed by the single-complex comparison and the
unique comparison of the two left adjoints to module pushforward.
Source: Stacks, Tags 06YJ and 08HY
(blueprint: lem-pc-canonical-single-pullback-comparison). -/
def canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (derivedPullback f).obj ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M) ⟶
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj ((pullback f).obj M) := by
  letI := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  exact ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app M)) ≫
    (DerivedCategory.singleFunctor _ 0).map (t.hom.app M)

/-- The pinned comparison is invertible on an invertible module.
Source: Stacks, Tags 06YD and 06YJ
(blueprint: lem-pc-canonical-single-pullback-comparison).

Proof: An invertible module is quasi-coherent and intrinsically flat, including on
an empty scheme. The single complex is bounded above and termwise flat. The
left-derived counit is therefore invertible on it. Apply the canonical flat-module
comparison theorem to this counit; compose with the single embedding of the unique
adjunction-preserving tensor-pullback comparison, which is an isomorphism. -/
theorem isIso_canonicalSinglePullbackMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    IsIso (canonicalSinglePullbackMap f M) := by
  let := canonicalTensorPullbackAdditive f
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f
  let c := ε.app ((HomotopyCategory.singleFunctor _ 0).obj M) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex
        (tensorPullback f) (ComplexShape.up ℤ) 0).hom.app M))
  have hc : IsDerivedModulePullbackComparison f M c := by
    refine ⟨ε, ?_, rfl⟩
    exact (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f
  have : IsIso c := isIso_modulePullbackComparison_of_isFlatOver_identity f M
    (isFlatOver_of_isInvertible (𝟙 Y) M) c hc
  let t := (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)
  have hi : IsIso (c ≫ (DerivedCategory.singleFunctor _ 0).map (t.hom.app M)) :=
    inferInstance
  simpa only [canonicalSinglePullbackMap, c, t, ε, Category.assoc] using hi

end AlgebraicGeometry.Scheme.Modules
```

## New

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F3
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison

/-! # The pinned derived pullback comparison on a single module

Compatibility import for the adopted source implementation. It provides
`AlgebraicGeometry.Scheme.Modules.canonicalTensorPullbackAdditive`,
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackMap`, and
`AlgebraicGeometry.Scheme.Modules.isIso_canonicalSinglePullbackMap`.

The comparison remains the specified derived counit followed by the single-complex
comparison and the unique tensor-to-ordinary pullback comparison.

Source: Stacks Project, Tags 06YD, 06YJ and 08HY.
(blueprint: lem-pc-canonical-single-pullback-comparison).
-/

@[expose] public section
```

The original node now has existing: true and points to
WeilConjectures.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison,
with the same primary declaration and three-declaration list. Other node fields
are unchanged. The upstream file is not edited.

## Users

The live downstream.py command reports the item as unknown because it is
quarantined. The table includes all direct importers found in lean/ and
quarantine/, all mathematical DAG parents, and the two live source modules
mentioning the canonical map. No consumer needs an adaptation: all use the same
fully qualified declaration names. No existing source declaration is removed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CanonicalSingleBaseChangeComparison | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.CanonicalStructureMapBaseChange | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.FlatDerivedStructureUnitProperties | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalDegreeZeroMateSquare | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackSquare | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeDegreeZeroComparison | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.Picard.TensorSingleBaseChangeSquare | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardAffineProjectiveBaseChange | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardDerivedCoefficientMap | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardDerivedUnitNormalizationComposition | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTranspose | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeFactorization | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposePasting | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageDerivedTransposeSingle | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMap | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardDirectImageSectionMapBijective | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.PicardResidueHomologySourceFibreComparison | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardTermwiseSingleMapComposition | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| Sheaf.AlgebraicGeometry.PicardTermwiseSourceCoherence | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.StandardSingleOpenDerivedArrow | unclaimed | DAG parent retained; same theorem and pinned map; no edit. |
| Sheaf.AlgebraicGeometry.TensorSinglePullbackComposition | unclaimed | Quarantined direct importer; compatibility import restores the original names; no edit. |
| WeilConjectures.AlgebraicGeometry.BaseChangeOpenFixedCounits | unclaimed | Already uses the adopted source comparison; unchanged. |
| WeilConjectures.AlgebraicGeometry.CanonicalModuleBaseChangeOpenComparisonCompat | unclaimed | Already uses the adopted source comparison; unchanged. |

## Status

landed 20261020T211706-L-3489244 2026-10-20 (merge of deliver/F3/Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison)
