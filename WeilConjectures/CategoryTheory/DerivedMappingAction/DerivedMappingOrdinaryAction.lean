/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedMappingAction.HomModel.DerivedMappingCohomologyCycles

/-! # The componentwise action on ordinary linear mapping complexes

Source: Stacks Project, Differential Graded Algebra, Example 09L9; Step 2 of
lem-sf-derived-functor-mapping-complex-action.
(blueprint: lem-sf-derived-mapping-ordinary-action)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingAction

variable {B : Type b} [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
  {A A' : Type u} [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A] [Category.{v} A'] [Abelian A'] [Linear B A']
  [HasDerivedCategory.{w} A']

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))] in
omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} A'] in
/-- Applying F to cochains commutes with removing a target shift, after the canonical
termwise shift comparison.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-action).
Proof: evaluate each family component. The shift comparison is the identity in every
degree, and the remaining degree transport is preserved by F. -/
theorem cochainMap_rightUnshift (F : A ⥤ A') [F.Additive]
    (X Y : CochainComplex A ℤ) (a n m : ℤ) (hm : n + a = m)
    (γ : Cochain X (Y⟦a⟧) n) :
    (((γ.map F).comp (Cochain.ofHom
      (((F.mapHomologicalComplex (.up ℤ)).commShiftIso a).hom.app Y)) (add_zero n)).rightUnshift
        m hm) = (γ.rightUnshift m hm).map F := by
  ext p q hpq
  obtain rfl : q = (p + n) + a := by omega
  simp only [Cochain.rightUnshift_v _ m hm p ((p + n) + a) hpq (p + n) rfl,
    Cochain.map_v,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  change (F.map (γ.v p (p + n) rfl) ≫ 𝟙 _) ≫ 𝟙 _ = F.map (γ.v p (p + n) rfl ≫ 𝟙 _)
  simp

/-- Ordinary postcomposition is postcomposition of the represented cochain family.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-action).
Proof: evaluate every family component and use ordinary naturality. -/
theorem HomModel.ordinary_postcomp (S : HomModel (B := B) A)
    (X Y Y' : CochainComplex A ℤ) (g : Y ⟶ Y') (n : ℤ)
    (x : (S.ordinary.obj (op X, Y)).X n) :
    ((S.degree X Y' n).hom
      ((S.ordinary.map (X := (op X, Y)) (Y := (op X, Y')) ((𝟙 X).op, g)).f n x)).down =
      (((S.degree X Y n).hom x).down).comp (Cochain.ofHom g) (add_zero n) := by
  ext p q hpq
  rw [S.ordinary_naturality, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  simp

omit [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} A'] in
/-- The cocycle of a map into a shift is sent to the cocycle of the termwise image map.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-ordinary-action).
Proof: rewrite the cocycle as the right-unshift of the degree-zero cochain of the map,
and apply the componentwise right-unshift identity. -/
theorem cochainMap_equivHomShift (F : A ⥤ A') [F.Additive]
    (X Y : CochainComplex A ℤ) (n : ℤ) (f : X ⟶ Y⟦n⟧) :
    (Cocycle.equivHomShift
      ((F.mapHomologicalComplex (.up ℤ)).map f ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app Y)).val =
      ((Cocycle.equivHomShift f).val).map F := by
  change (Cochain.ofHom ((F.mapHomologicalComplex (.up ℤ)).map f ≫
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso n).hom.app Y)).rightUnshift n
      (zero_add n) = ((Cochain.ofHom f).rightUnshift n (zero_add n)).map F
  rw [Cochain.ofHom_comp, ← Cochain.map_ofHom]
  exact cochainMap_rightUnshift F X Y n 0 n (zero_add n) (Cochain.ofHom f)

end CategoryTheory.DerivedMappingAction
