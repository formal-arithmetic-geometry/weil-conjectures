/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Comparing a geometric mate with an inverse scalar mate

Consider two pairs of adjunctions `L_E ⊣ G_E`, `L_F ⊣ G_F` (pullback/direct image) and two
scalar adjunctions `Ext_Y ⊣ Res_Y`, `Ext_X ⊣ Res_X`, together with a pullback comparison
`θ : Ext_Y ⋙ L_F ≅ L_E ⋙ Ext_X`. Suppose the restriction/direct-image comparison `δ` is the
mate of a restriction/pullback comparison `b` for other left adjoints `L'_E`, `L'_F` of the
same direct images, and suppose `θ` corresponds to `b` under the scalar units. Then the mate
of `θ` is the inverse scalar mate of `δ.inv`.
-/

@[expose] public section

namespace CategoryTheory

open Functor

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  {LE LE' : A ⥤ C} {GE : C ⥤ A} (PE : LE ⊣ GE) (PE' : LE' ⊣ GE)
  {LF LF' : B ⥤ D} {GF : D ⥤ B} (PF : LF ⊣ GF) (PF' : LF' ⊣ GF)
  {EY : A ⥤ B} {RY : B ⥤ A} (SY : EY ⊣ RY) {EX : C ⥤ D} {RX : D ⥤ C} (SX : EX ⊣ RX)

/-- The mate of a pullback comparison `θ` with respect to the pullback adjunctions equals the
inverse scalar mate of a restriction/direct-image comparison `δ`, once `δ` is the mate of a
restriction/pullback comparison `b` (for other left adjoints identified with the given ones by
`oE`, `oF`) and `θ` corresponds to `b` under the scalar units. -/
theorem mateEquiv_eq_mateEquiv_symm_of_unit
    (oE : LE ≅ LE') (oF : LF ≅ LF')
    (hoE : ∀ (M : A) (N : C) (t : LE.obj M ⟶ N),
      PE.homEquiv M N t = PE'.homEquiv M N (oE.inv.app M ≫ t))
    (hoF : ∀ (M : B) (N : D) (t : LF.obj M ⟶ N),
      PF.homEquiv M N t = PF'.homEquiv M N (oF.inv.app M ≫ t))
    (θ : EY ⋙ LF ≅ LE ⋙ EX) (b : LF' ⋙ RX ≅ RY ⋙ LE') (δ : GF ⋙ RY ≅ RX ⋙ GE)
    (hδ : ∀ (M : B) (N : D) (t : LF'.obj M ⟶ N),
      PE'.homEquiv _ _ (b.inv.app M ≫ RX.map t) =
        RY.map (PF'.homEquiv M N t) ≫ δ.hom.app N)
    (h : ∀ M : A, SX.unit.app (LE.obj M) ≫ RX.map (θ.inv.app M) =
      LE.map (SY.unit.app M) ≫ oE.hom.app _ ≫ b.inv.app (EY.obj M) ≫
        RX.map (oF.inv.app (EY.obj M))) :
    (mateEquiv PE PF (TwoSquare.mk _ _ _ _ θ.hom)).natTrans =
      ((mateEquiv SX SY).symm (TwoSquare.mk _ _ _ _ δ.inv)).natTrans := by
  have key (X : A) (N : D) (c : LF.obj (EY.obj X) ⟶ N) :
      PE.homEquiv _ _ (SX.homEquiv _ _ (θ.inv.app X ≫ c)) =
        SY.unit.app X ≫ RY.map (PF.homEquiv _ _ c) ≫ δ.hom.app N := by
    rw [hoE, hoF, ← hδ]
    erw [← PE'.homEquiv_naturality_left]
    rw [SX.homEquiv_unit, Functor.map_comp, reassoc_of% (h X)]
    simp
  have hconj : conjugateEquiv (SY.comp PF) (PE.comp SX) θ.inv = δ.hom := by
    ext N
    simpa [Adjunction.homEquiv_unit] using
      key _ N (LF.map (SY.counit.app (GF.obj N)) ≫ PF.counit.app N)
  have hconj' : conjugateEquiv (PE.comp SX) (SY.comp PF) θ.hom = δ.inv := by
    rw [← δ.comp_hom_eq_id, ← hconj]
    exact conjugateEquiv_comm _ _ θ.inv_hom_id
  rw [← hconj', ← iterated_mateEquiv_conjugateEquiv PE PF SY SX (TwoSquare.mk _ _ _ _ θ.hom)]
  exact (congrArg TwoSquare.natTrans ((mateEquiv SX SY).symm_apply_apply _)).symm

end CategoryTheory
