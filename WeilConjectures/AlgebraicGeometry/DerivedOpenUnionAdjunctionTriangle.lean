/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnionSESPresentation
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-! # Direct-image triangle on an arbitrary open union

Source: Stacks Project, Tag 08BV, applied on the open union and pushed to X.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated
namespace AlgebraicGeometry

private theorem transport_triangle
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Triangle C) (hT : T ∈ distTriang C) {N A B : C}
    (eN : T.obj₁ ≅ N) (eA : T.obj₂ ≅ A) (eB : T.obj₃ ≅ B)
    (b : A ⟶ B) (hb : T.mor₂ ≫ eB.hom = eA.hom ≫ b) :
    ∃ (d : N ⟶ A) (c : B ⟶ N⟦(1 : ℤ)⟧), Triangle.mk d b c ∈ distTriang C := by
  let d := eN.inv ≫ T.mor₁ ≫ eA.hom
  let c := eB.inv ≫ T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧'
  refine ⟨d, c, isomorphic_distinguished T hT _ ?_⟩
  refine (Triangle.isoMk _ _ eN eA eB ?_ hb ?_).symm
  · change T.mor₁ ≫ eA.hom = eN.hom ≫ (eN.inv ≫ T.mor₁ ≫ eA.hom)
    simp only [Iso.hom_inv_id_assoc]
  · change T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧' =
      eB.hom ≫ (eB.inv ≫ T.mor₃ ≫ eN.hom⟦(1 : ℤ)⟧')
    simp only [Iso.hom_inv_id_assoc]

set_option maxHeartbeats 800000 in
-- Comparing localized right adjoints and their composite shift isomorphism.
/-- The inverse rotation of the direct-image Mayer--Vietoris triangle, expressed using
any right adjoints to localized derived restrictions (Stacks, Tags 08BV and 079W). -/
theorem derived_open_union_adjunction_triangle
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ W : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W))]
    (U V : X.Opens)
    (G : ∀ W : X.Opens,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W)) ⥤
        schemeDerivedCategory X)
    (adj : ∀ W : X.Opens,
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory ⊣
        G W)
    (E' : schemeDerivedCategory X) (k : ℤ) :
    let R := fun W : X.Opens ↦
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
    let N := (G (U ⊓ V)).obj ((R (U ⊓ V)).obj (E'⟦k - 1⟧))
    let A := (G (U ⊔ V)).obj ((R (U ⊔ V)).obj (E'⟦k⟧))
    let B := (G U).obj ((R U).obj (E'⟦k⟧)) ⊞ (G V).obj ((R V).obj (E'⟦k⟧))
    let β := ((adj (U ⊔ V)).homEquiv A ((R (U ⊔ V)).obj (E'⟦k⟧))).symm (𝟙 A)
    let b := biprod.lift
      ((adj U).homEquiv A ((R U).obj (E'⟦k⟧))
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_left) β))
      ((adj V).homEquiv A ((R V).obj (E'⟦k⟧))
        (derivedOpenHomRestriction X.toRingedSpace (homOfLE le_sup_right) β))
    ∃ (d : N ⟶ A) (c : B ⟶ N⟦(1 : ℤ)⟧),
      Triangle.mk d b c ∈ distTriang (schemeDerivedCategory X) := by
  classical
  dsimp only
  let R := fun W : X.Opens ↦
    (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory
  let H := R (U ⊓ V) ⋙ G (U ⊓ V)
  let := (adj (U ⊓ V)).rightAdjointCommShift ℤ
  obtain ⟨S, eA, eB, eC, hS, hf⟩ :=
    derived_open_union_ses_presentation X U V G adj (E'⟦k⟧)
  let T := (DerivedCategory.triangleOfSES hS).invRotate
  let eN : T.obj₁ ≅ H.obj (E'⟦k - 1⟧) :=
    (shiftFunctor (schemeDerivedCategory X) (-1 : ℤ)).mapIso eC ≪≫
      (H.commShiftIso (-1 : ℤ)).symm.app (E'⟦k⟧) ≪≫
      H.mapIso ((shiftFunctorAdd' (schemeDerivedCategory X) k (-1) (k - 1)
        (by omega)).symm.app E')
  exact transport_triangle T
    (inv_rot_of_distTriang _ (DerivedCategory.triangleOfSES_distinguished hS))
    eN eA eB _ hf

end AlgebraicGeometry
