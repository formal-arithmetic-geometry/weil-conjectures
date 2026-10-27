/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology

/-! # A coefficient API for cohomology pullback of single complexes

Source: Stacks Project, Tags 03Q8 and 0EZM.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
/-- Maps retained with a specified commutation law.
Source: the coefficient square in Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-single-cohomology-square).
Keep the category and its objects as parameters. Formula fields identify all data
with the specified maps, and the final field retains their commutation law. -/
structure CohomologySquareData {C : Type*} [Category* C] {A B : C}
    (ρ : A ⟶ B) (ν : End A) (ν' : End B) where
  sourceAction : End A
  targetAction : End B
  pullbackMap : A ⟶ B
  source_formula : sourceAction = ν
  target_formula : targetAction = ν'
  pullback_formula : pullbackMap = ρ
  commutes : sourceAction ≫ pullbackMap = pullbackMap ≫ targetAction

/-- Retain a specified square and its commutation proof.
Source: the coefficient square in Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-single-cohomology-square).
The maps are the supplied maps and the formula fields are reflexivity. -/
def CohomologySquareData.ofCommutes {C : Type*} [Category* C] {A B : C}
    (ρ : A ⟶ B) (ν : End A) (ν' : End B) (h : ν ≫ ρ = ρ ≫ ν') :
    CohomologySquareData ρ ν ν' where
  sourceAction := ν
  targetAction := ν'
  pullbackMap := ρ
  source_formula := rfl
  target_formula := rfl
  pullback_formula := rfl
  commutes := h

/-- Cohomological pullback, naturally in the coefficient complex.
Source: Stacks Project, Tags 03Q8 and 0EZM.
(blueprint: def-weil-pbc-single-cohomology-pullback).
Retain rawAffineComplexPullback as the component map with its native endpoints.
For naturality, compose the derived-adjunction unit, derived global-sections
comparison and exact inverse-image comparison and apply homology. Its components
expand to the prescribed raw map. -/
@[irreducible] noncomputable def complexCohomologyPullbackTransformation
    {X Y : Scheme.{u}} (b : Y ⟶ X) (q : ℕ) :
    DerivedCategory.Q ⋙ Etale.cohomology AddCommGrpCat.{u + 1} X (q : ℤ) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} b).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q ⋙ Etale.cohomology AddCommGrpCat.{u + 1} Y (q : ℤ) where
  app K := Etale.rawAffineComplexPullback (q : ℤ) b K
  naturality K K' φ := by
    let L := Etale.upperStar AddCommGrpCat.{u + 1} b
    let RX := Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} X
    let RY := Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y
    let c := Functor.rightDerivedFunctorCompIso'
      (Etale.lowerStar AddCommGrpCat.{u + 1} b)
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1})
      (Functor.isoWhiskerLeft (Etale.lowerStar AddCommGrpCat.{u + 1} b)
          (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
            terminalIsTerminal) ≪≫
        Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} b ≪≫
        (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).symm)
    let σ := Functor.whiskerLeft DerivedCategory.Q
        (Functor.whiskerRight
          (Etale.mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).unit RX) ≫
      (Functor.whiskerLeft DerivedCategory.Q
          (Functor.whiskerLeft L.mapDerivedCategory c.hom) ≫
        Functor.whiskerRight L.mapDerivedCategoryFactors.hom RY)
    exact (Functor.whiskerRight σ
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (q : ℤ))).naturality φ

/-- The constructed transformation has the prescribed raw pullback component.
Source: Stacks Project, Tag 0EZM.
(blueprint: def-weil-pbc-single-cohomology-pullback).
Proof: the component is the explicit app field of the transformation. -/
theorem complexCohomologyPullbackTransformation_app {X Y : Scheme.{u}}
    (b : Y ⟶ X) (q : ℕ)
    (K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ) :
    (complexCohomologyPullbackTransformation b q).app K =
      Etale.rawAffineComplexPullback (q : ℤ) b K := by
  unfold complexCohomologyPullbackTransformation
  rfl

private theorem square_comp {C : Type*} [Category* C] {A B D : C}
    {a : A ⟶ B} {b : B ⟶ D} {s : End A} {t : End B} {v : End D}
    (ha : s ≫ a = a ≫ t) (hb : t ≫ b = b ≫ v) :
    s ≫ (a ≫ b) = (a ≫ b) ≫ v := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

private theorem map_square {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {A B : C} {s : End A} {t : End B} {a : A ⟶ B}
    (h : s ≫ a = a ≫ t) : F.map s ≫ F.map a = F.map a ≫ F.map t := by
  rw [← F.map_comp, h, F.map_comp]

/-- Naturality for a coefficient square and a specified transformation component.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-single-cohomology-square).
Proof: compose transformation naturality with the image of the coefficient square,
then substitute the prescribed component formula. -/
theorem coefficientPullback_square {C D K J A : Type*}
    [Category* C] [Category* D] [Category* K] [Category* J] [Category* A]
    (SX : C ⥤ K) (SY : D ⥤ J) (L : C ⥤ D) (LC : K ⥤ J)
    (HX : K ⥤ A) (HY : J ⥤ A) (τ : HX ⟶ LC ⋙ HY)
    (ι : SX ⋙ LC ⟶ L ⋙ SY) {F : C} {F' : D}
    (γ : L.obj F ⟶ F') (ν : End F) (ν' : End F')
    (r : HX.obj (SX.obj F) ⟶ HY.obj (LC.obj (SX.obj F)))
    (hr : τ.app (SX.obj F) = r)
    (hν : L.map ν ≫ γ = γ ≫ ν') :
    HX.map (SX.map ν) ≫ (r ≫ HY.map (ι.app F ≫ SY.map γ)) =
      (r ≫ HY.map (ι.app F ≫ SY.map γ)) ≫ HY.map (SY.map ν') := by
  subst r
  exact square_comp (τ.naturality (SX.map ν))
    (map_square HY (square_comp (ι.naturality ν) (map_square SY hν)))

/-- Retain the cohomology square before instantiating its categories and functors.
Source: Stacks Project, Tag 03Q8.
(blueprint: def-weil-pbc-single-cohomology-square).
All maps are explicit images or composites. The law is coefficientPullback_square. -/
def coefficientCohomologySquare {C D K J A : Type*}
    [Category* C] [Category* D] [Category* K] [Category* J] [Category* A]
    (SX : C ⥤ K) (SY : D ⥤ J) (L : C ⥤ D) (LC : K ⥤ J)
    (HX : K ⥤ A) (HY : J ⥤ A) (τ : HX ⟶ LC ⋙ HY)
    (ι : SX ⋙ LC ⟶ L ⋙ SY) {F : C} {F' : D}
    (γ : L.obj F ⟶ F') (ν : End F) (ν' : End F')
    (r : HX.obj (SX.obj F) ⟶ HY.obj (LC.obj (SX.obj F)))
    (hr : τ.app (SX.obj F) = r) (hν : L.map ν ≫ γ = γ ≫ ν') :
    CohomologySquareData (r ≫ HY.map (ι.app F ≫ SY.map γ))
      (HX.map (SX.map ν)) (HY.map (SY.map ν')) :=
  CohomologySquareData.ofCommutes _ _ _
    (coefficientPullback_square SX SY L LC HX HY τ ι γ ν ν' r hr hν)

end AlgebraicGeometry.Scheme.Modules
