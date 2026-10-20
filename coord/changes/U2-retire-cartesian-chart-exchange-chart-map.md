# chartRestrictedMap_eq_rawAffine and cartesianChartRestrictedRawClass

## Reason

Retire the assigned duplicate `Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap`
and its now-unused, unclaimed consumer
`Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation`.
This follows `coord/retire-items.tsv` and the human's 2026-10-20 instruction in
`coord/changes/retire-sheaf-twins-20261020.md` to retire source twins and delete dead
copies. The sole consumer has no importers or external uses of its declarations.

Both item signatures are identical to the source twin, ignoring whitespace, and
both proofs are the same. In the consumer twin the raw-class construction and its
characterizing equation omit three unused parameters U, r, hr. After removing
those binders and their occurrences in applications, and switching the two Sheaf
imports to their source twins, the entire consumer matches the source twin modulo
whitespace. Thus neither node changes mathematical meaning, nor is any proof
route bypassed. No upstream file, statement, definition or target is modified.

## Old

The assigned duplicate, verbatim:

```lean
module

public import WeilConjectures.AlgebraicGeometry.CartesianChartExchangeMapBridge
public import WeilConjectures.AlgebraicGeometry.CartesianHigherImageChartSystem
import all WeilConjectures.AlgebraicGeometry.CartesianChartExchangeObjects

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency true

lemma chartRestrictedMap_eq_rawAffine
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (j : Over i)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (hw : ((cartesianChartCone f D c i).π.app j).left ≫
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) :
    restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V =
    rawAffineRestrictedCohomologyMap ((cartesianChartCone f D c i).π.app j).left
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) hw q
      (((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} ((cartesianChartCone f D c i).π.app j).left
        (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
        (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
        hl₂.symm).inv.app
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V := by
  rfl

lemma chartRestrictedMap_apply_eq_rawAffine
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (j : Over i)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    (hw : ((cartesianChartCone f D c i).π.app j).left ≫
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) :
    restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x =
    rawAffineRestrictedCohomologyMap ((cartesianChartCone f D c i).π.app j).left
      (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom)
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) hw q
      (((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))
      ((upperStarComp AddCommGrpCat.{u + 1} ((cartesianChartCone f D c i).π.app j).left
        (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
        (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
        hl₂.symm).inv.app
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)) V x := by
  exact congrArg (fun t ↦ t x)
    (chartRestrictedMap_eq_rawAffine f D c F q i V j hl₂ hw)

end AlgebraicGeometry.Etale
```

Its now-unused consumer, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyClass
import all Sheaf.AlgebraicGeometry.CartesianChartExchangeEvaluation
import Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap

/-! # Evaluation of the restricted chart cone map

Source: Stacks Project, Tags 0EYM and 03Q8.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

attribute [local irreducible] cohomology upperStar rawAffineComplexPullback
  rightDerivedGlobalSections DerivedCategory.Q

/-- The specified raw pullback of the canonical inverse-evaluation stage class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: def-sc-cartesian-chart-restricted-raw-class). -/
@[irreducible]
noncomputable def cartesianChartRestrictedRawClass
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (_hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
    (abelianHigherDirectImageRawPresheaf
      (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
        pullback.snd f (D.obj i).hom) q
      (((pullback.snd (c.π.app i).left
        (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
        (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V) :=
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  let wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let z := rawRestrictedCohomologyClass h q G V x
  let z' := abelianHigherDirectImageRawPullback l h h' wl q G G' φ V z
  z'

/-- The defining equation of the cached chart raw class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: def-sc-cartesian-chart-restricted-raw-class).

Proof: Unfold the real raw-pullback construction; both sides are identical. -/
theorem cartesianChartRestrictedRawClass_eq
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
    cartesianChartRestrictedRawClass f D c F q i V U r hr j x hl₂ =
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  let wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let z := rawRestrictedCohomologyClass h q G V x
  let z' := abelianHigherDirectImageRawPullback l h h' wl q G G' φ V z
  z' := by
  exact cartesianChartRestrictedRawClass.eq_def f D c F q i V U r hr j x hl₂

attribute [local irreducible] cartesianChartCohomologyIso cartesianChartRawAdjunctionIso
  rawRestrictedCohomologyComparison abelianHigherDirectImageRawPullback
  rawAffineRestrictedCohomologyMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency true in
/-- Evaluation at the apex sends the restricted cohomology cone map to the
raw pullback of the canonical inverse-evaluation class.
Source: Stacks Project, Tags 0EYM and 03Q8.
(blueprint: lem-sc-cartesian-chart-restricted-map-evaluation).

Proof: First identify restrictedOverCohomologyMap with the raw affine map for
l, h and h'. Unfold their literal derived pullback and coefficient formulas. The
coefficient morphisms agree by the displayed second-projection equality and
proof irrelevance. Apply rawRestrictedCohomologyClass_map: the raw affine map
of x is evaluation of z'. Finally apply the proved chartCohomologyIso_eval
from CartesianChartExchangeEvaluation to z'. Its free-source precomposition
is exactly the map displayed here. Combine these two equalities by congruence
and transitivity. This calculation uses neither exchange nor the stage lift,
and holds for degree zero and empty test objects without changes. -/
theorem cartesianChartRestrictedCohomologyMap_eval
    {S X : Scheme.{u}} (f : X ⟶ S)
    {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale)
    (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left)
    (j : Over i)
    (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartDiagram f D i).obj j) V)
    (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫
      pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) =
      pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) :
  (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr).hom
    (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom)
      (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
      (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) =
  (DerivedCategory.Plus.singleFunctor _ 0).map
    (abelianFreeRepresentablePullbackSquareIso (c.π.app i).left V U r hr).hom ≫
    (cartesianChartRawAdjunctionIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V).hom
      (cartesianChartRestrictedRawClass f D c F q i V U r hr j x hl₂) := by
  let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫
    pullback.snd f (D.obj i).hom
  let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶
      pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) :=
    ((cartesianChartCone f D c i).π.app j).left
  have wl : l ≫ h = h' :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂)
  let G := ((pullback.snd (D.map j.hom).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let G' := ((pullback.snd (c.π.app i).left
      (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj
    (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  let φ := (upperStarComp AddCommGrpCat.{u + 1} l
    (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))
    (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))
    hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F)
  have hm := congrArg (fun t ↦ t x) (chartRestrictedMap_eq_rawAffine f D c F q i V j hl₂ wl)
  have hn := rawRestrictedCohomologyClass_map l h h' wl q G G' φ V x
  have he := chartCohomologyIso_eval f (D.obj i).hom (c.π.app i).left c.pt.hom
    (Over.w (c.π.app i)).symm F q V U r hr
    (cartesianChartRestrictedRawClass f D c F q i V U r hr j x hl₂)
  have hz := cartesianChartRestrictedRawClass_eq f D c F q i V U r hr j x hl₂
  dsimp only [] at hz
  have hn' := (hm.trans hn).trans
    (congrArg (fun y ↦ rawRestrictedCohomologyComparison h' q G' V y) hz.symm)
  have hc := congrArg
    (fun y ↦ (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom
      (Over.w (c.π.app i)).symm F q V U r hr).hom y) hn'
  exact hc.trans he

end AlgebraicGeometry.Etale
```

## New

Both copies are withdrawn through `deleted.txt`. Their declarations are retained
in the existing source modules:

- `WeilConjectures.AlgebraicGeometry.CartesianChartExchangeChartMap`:
  `AlgebraicGeometry.Etale.chartRestrictedMap_eq_rawAffine` and
  `AlgebraicGeometry.Etale.chartRestrictedMap_apply_eq_rawAffine`, with exactly the
  same signatures and proofs as above.
- `WeilConjectures.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation`:
  `AlgebraicGeometry.Etale.cartesianChartRestrictedRawClass`, its equation, and
  `AlgebraicGeometry.Etale.cartesianChartRestrictedCohomologyMap_eval`.

The latter source signatures are, verbatim:

```lean
def cartesianChartRestrictedRawClass {S X : Scheme.{u}} (f : X ⟶ S) {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (i : I) (V : (D.obj i).left.Etale) (j : Over i) (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom) (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫ pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) = pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) : (abelianHigherDirectImageRawPresheaf (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫ pullback.snd f (D.obj i).hom) q (((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F))).obj (op V)

theorem cartesianChartRestrictedRawClass_eq {S X : Scheme.{u}} (f : X ⟶ S) {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (i : I) (V : (D.obj i).left.Etale) (j : Over i) (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom) (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫ pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) = pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) : cartesianChartRestrictedRawClass f D c F q i V j x hl₂ = let h := pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) ≫ pullback.snd f (D.obj i).hom let h' := pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom) ≫ pullback.snd f (D.obj i).hom let l : pullback (c.π.app i).left (pullback.snd f (D.obj i).hom) ⟶ pullback (D.map j.hom).left (pullback.snd f (D.obj i).hom) := ((cartesianChartCone f D c i).π.app j).left let wl : l ≫ h = h' := (Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ pullback.snd f (D.obj i).hom) hl₂) let G := ((pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) let G' := ((pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom))^*[AddCommGrpCat.{u + 1}]).obj (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) let φ := (upperStarComp AddCommGrpCat.{u + 1} l (pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom)) (pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) hl₂.symm).inv.app (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) let z := rawRestrictedCohomologyClass h q G V x let z' := abelianHigherDirectImageRawPullback l h h' wl q G G' φ V z z'

theorem cartesianChartRestrictedCohomologyMap_eval {S X : Scheme.{u}} (f : X ⟶ S) {I : Type u} [SmallCategory I] (D : I ⥤ Over S) (c : Cone D) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) (i : I) (V : (D.obj i).left.Etale) (U : c.pt.left.Etale) (r : U.left ⟶ V.left) (hr : IsPullback r U.hom V.hom (c.π.app i).left) (j : Over i) (x : restrictedOverCohomology (pullback.snd f (D.obj i).hom) (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ) ((cartesianChartDiagram f D i).obj j) V) (hl₂ : ((cartesianChartCone f D c i).π.app j).left ≫ pullback.snd (D.map j.hom).left (pullback.snd f (D.obj i).hom) = pullback.snd (c.π.app i).left (pullback.snd f (D.obj i).hom)) : (cartesianChartCohomologyIso f (D.obj i).hom (c.π.app i).left c.pt.hom (Over.w (c.π.app i)).symm F q V U r hr).hom (restrictedOverCohomologyMap (pullback.snd f (D.obj i).hom) (((pullback.fst f (D.obj i).hom)^*[AddCommGrpCat.{u + 1}]).obj F) (q : ℤ) ((cartesianChartCone f D c i).π.app j) V x) = (DerivedCategory.Plus.singleFunctor _ 0).map (abelianFreeRepresentablePullbackSquareIso (c.π.app i).left V U r hr).hom ≫ (cartesianChartRawAdjunctionIso f (D.obj i).hom (c.π.app i).left c.pt.hom (Over.w (c.π.app i)).symm F q V).hom (cartesianChartRestrictedRawClass f D c F q i V j x hl₂)
```

The two consumer DAG records now point at the existing source declarations and
contain their current signatures. Their mathematical statements, proof steps,
proof dependencies, and unit realization remain unchanged. No DAG node points at
the assigned item itself.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap | U2 | Withdraw redundant copy; source twin retains its declarations. |
| Sheaf.AlgebraicGeometry.CartesianChartRestrictedMapEvaluation | unclaimed | Withdraw dead consumer, whose sole reference to the item disappears with it; repoint its two DAG records to its source twin. |

`tools/downstream.py` lists only the consumer below the assigned module and zero
modules below the consumer. Textual searches for the consumer's declaration names
find no uses outside its own file. No source module imports either Sheaf copy.

The first attempted import-only adaptation compiled standalone in 49.9 seconds,
but the delivery compile and profiling attempts reached the 60-second limit.
That adaptation is not delivered. The final packet removes both dead duplicates;
it introduces no replacement definition, file split, unfinished proof, or changed
upstream body. No definition is hollowed, and no Lean file with a slow proof is
added or retained by this delivery.

## Status

landed 20261020T141317-L-2036127 2026-10-20 (merge of deliver/U2/Sheaf.AlgebraicGeometry.CartesianChartExchangeChartMap)
