/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawAffineRestrictedCohomology
public import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleData
import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleUnit
import WeilConjectures.AlgebraicGeometry.RestrictedOverSingleComposition

/-! # Coherence of restricted fixed-coefficient single complexes

## References

* [Stacks Project, Tag 09Z1](https://stacks.math.columbia.edu/tag/09Z1)
* [Stacks Project, Tag 0EZM](https://stacks.math.columbia.edu/tag/0EZM)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

private theorem iso_cancel_triangle {C : Type*} [Category C] {X Y Z T : C}
    (e : Y ≅ X) (a : Y ⟶ Z) (b : Z ⟶ T) (d : T ⟶ X)
    (h : e.hom = a ≫ b ≫ d) : 𝟙 X = e.inv ≫ a ≫ b ≫ d := by
  calc
    𝟙 X = e.inv ≫ e.hom := e.inv_hom_id.symm
    _ = e.inv ≫ a ≫ b ≫ d := by rw [h]

attribute [local irreducible] upperStar upperStarComp upperStarId
  rawAffineRestrictedMap restrictedOverSingle restrictedOverSingleIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
private theorem restrictedOverSingle_canonical_coherence
    {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D₀ : I ⥤ Over W) (c₀ : Cone D₀) (U : S.Etale) :
    let D := restrictedOverDiagram k D₀ U
    let c := restrictedOverCone k D₀ c₀ U
    let K := fun i : I ↦ restrictedOverSingle k F (D₀.obj i) U
    let φ := fun {i j : I} (f : j ⟶ i) ↦
      (restrictedOverSingleIso k F (D₀.map f) U).hom
    let G := restrictedOverSingleG k F D₀ c₀ U
    let eG := restrictedOverSingleConeIso k F D₀ c₀ U
    (∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (K i)) ∧
    (∀ (i j l : I) (f : j ⟶ i) (g : l ⟶ j), φ (g ≫ f) =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
          (D.map (g ≫ f)) (D.map_comp g f)) (ComplexShape.up ℤ)).hom.app (K i) ≫
      ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : j ⟶ i),
      G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact restrictedOverSingle_unit k F D₀ U i
  · intro i j l f g
    exact restrictedOverSingle_composition k F (D₀.map f) (D₀.map g)
      (D₀.map (g ≫ f)) (D₀.map_comp g f) U
      ((restrictedOverDiagram k D₀ U).map_comp g f)
  · intro i j f
    dsimp only [restrictedOverSingleG, restrictedOverSingleConeIso,
      restrictedOverCone, restrictedOverDiagram, Functor.const_obj_map, Functor.const_obj_obj,
      Iso.symm_hom, Iso.symm_inv]
    have h := restrictedOverSingle_composition k F
      (A := D₀.obj i) (B := D₀.obj j) (C := c₀.pt) (D₀.map f) (c₀.π.app j)
      (c₀.π.app i) (c₀.w f).symm U ((restrictedOverCone k D₀ c₀ U).w f).symm
    exact iso_cancel_triangle (restrictedOverSingleIso k F
      (A := c₀.pt) (B := D₀.obj i) (c₀.π.app i) U) _ _ _ h

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
/-- Identity, composition, and constant-diagram coherence of the explicit single complexes. -/
theorem restrictedOverSingle_coherence {W S : Scheme.{u}} (k : W ⟶ S)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1})
    {I : Type u} [Category.{u} I] (D₀ : I ⥤ Over W) (c₀ : Cone D₀) (U : S.Etale)
    (D : I ⥤ Scheme.{u}) (c : Cone D)
    (K : ∀ i : I, CochainComplex (Sheaf (D.obj i).smallEtaleTopology
      AddCommGrpCat.{u + 1}) ℤ)
    (φ : ∀ {i j : I} (f : j ⟶ i),
      ((upperStar AddCommGrpCat.{u + 1} (D.map f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i) ⟶ K j)
    (G : Iᵒᵖ ⥤ CochainComplex (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (eG : ∀ i : I, G.obj (op i) ≅
      ((upperStar AddCommGrpCat.{u + 1} (c.π.app i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (K i))
    (_hD : D = restrictedOverDiagram k D₀ U)
    (_hc : HEq c (restrictedOverCone k D₀ c₀ U))
    (_hK : HEq K (fun i ↦ restrictedOverSingle k F (D₀.obj i) U))
    (_hφ : HEq @φ
      (fun {i j : I} (f : j ⟶ i) ↦ (restrictedOverSingleIso k F (D₀.map f) U).hom))
    (_hG : HEq G (restrictedOverSingleG k F D₀ c₀ U))
    (_heG : HEq eG (restrictedOverSingleConeIso k F D₀ c₀ U)) :
    (∀ i : I, φ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{u + 1} (D.obj i))
        (ComplexShape.up ℤ)).hom.app (K i)) ∧
    (∀ (i j l : I) (f : j ⟶ i) (g : l ⟶ j), φ (g ≫ f) =
      (NatIso.mapHomologicalComplex
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g) (D.map f)
          (D.map (g ≫ f)) (D.map_comp g f)) (ComplexShape.up ℤ)).hom.app (K i) ≫
      ((upperStar AddCommGrpCat.{u + 1} (D.map g)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (φ f) ≫ φ g) ∧
    (∀ (i j : I) (f : j ⟶ i),
      G.map f.op =
      (eG i).hom ≫
        (NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{u + 1} (c.π.app j) (D.map f)
            (c.π.app i) (c.w f).symm) (ComplexShape.up ℤ)).hom.app (K i) ≫
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (φ f) ≫ (eG j).inv) := by
  subst D
  cases eq_of_heq _hc
  cases eq_of_heq _hK
  cases eq_of_heq _hφ
  cases eq_of_heq _hG
  cases eq_of_heq _heG
  exact restrictedOverSingle_canonical_coherence k F D₀ c₀ U

end AlgebraicGeometry.Etale
