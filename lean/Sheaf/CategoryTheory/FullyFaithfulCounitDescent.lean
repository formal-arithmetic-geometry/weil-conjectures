/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Descent of a counit-defined coefficient isomorphism through full embeddings

Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/lem-coef-finite-dualizing.md, Proof, closed-immersion step:
full-faithfulness lift and descent
(blueprint: lem-coef-fully-faithful-counit-descent).
-/

@[expose] public section

set_option autoImplicit false

universe uCA vCA uCB vCB uDA vDA uDB vDB
  uCpA vCpA uCpB vCpB uDpA vDpA uDpB vDpB

namespace CategoryTheory

/--
The local full-faithfulness lift and counit descent used in the closed-immersion step.

Source: literature/blueprint/master/blueprint/sec-six-functors/
sk-prop-sf-biduality-general/lem-coef-finite-dualizing.md, Proof, closed-immersion counit descent.
Proof (the eight elementary steps of the node):
1. Set `X = T_C N`, `Y = I_B M_B`, `u = t_C,N ≫ T'_C(α_A)` and
   `v = α_B ≫ J_B(t_D,M)`. Functors preserve inverses, so `h = u ≫ b' ≫ v⁻¹` is an iso.
2. Full faithfulness on `P` lifts `h` and its inverse. Injectivity on endomorphisms proves
   the inverse identities; injectivity on `Hom(X,Y)` proves uniqueness.
3. Naturality of `δ_B` at the lift `b` applies because `C0` is full and contains `X,Y`.
   In `L = S_D,B(c ≫ F_B(b) ≫ e_B)`, replace `S_D,B(e_B)` using `hCounitB`, then use
   this naturality to move the image of `b` past `δ_B`.
4. Substitute the defining image of `b`. Naturality `hE` along `t_D,M` moves the inverse
   of `J_B(t_D,M)` past `E_B`, giving a postcomposition by `t_D,M⁻¹`.
5. Substitute `hcoef` and the primed counit equation `hb'`.
6. Naturality `hc'` along `α_A` cancels the inverse component at `Q_A`.
7. Substitute `hCounitA`, and use naturality of `t_D` at `e_A,M`. The resulting adjacent
   factors `t_D,M` and its inverse cancel, leaving `S_D,B(T_D(e_A,M))`.
8. Precompose with `S_D,B(c⁻¹)` and cancel `c`. Both resulting preimages lie in
   `Hom(F_B X,M_B)`, so `hSD` reflects the desired original counit identity.
(blueprint: lem-coef-fully-faithful-counit-descent)
-/
theorem fully_faithful_counit_descent
    {C_A : Type uCA} [Category.{vCA, uCA} C_A]
    {C_B : Type uCB} [Category.{vCB, uCB} C_B]
    {D_A : Type uDA} [Category.{vDA, uDA} D_A]
    {D_B : Type uDB} [Category.{vDB, uDB} D_B]
    {Cp_A : Type uCpA} [Category.{vCpA, uCpA} Cp_A]
    {Cp_B : Type uCpB} [Category.{vCpB, uCpB} Cp_B]
    {Dp_A : Type uDpA} [Category.{vDpA, uDpA} Dp_A]
    {Dp_B : Type uDpB} [Category.{vDpB, uDpB} Dp_B]
    (F_A : C_A ⥤ D_A) (I_A : D_A ⥤ C_A)
    (F_B : C_B ⥤ D_B) (I_B : D_B ⥤ C_B)
    (adj_A : F_A ⊣ I_A) (adj_B : F_B ⊣ I_B)
    (S_C_A : C_A ⥤ Cp_A) (S_C_B : C_B ⥤ Cp_B)
    (S_D_A : D_A ⥤ Dp_A) (S_D_B : D_B ⥤ Dp_B)
    (F'p_A : Cp_A ⥤ Dp_A) (F'p_B : Cp_B ⥤ Dp_B)
    (T_C : C_A ⥤ C_B) (T_D : D_A ⥤ D_B)
    (T'C : Cp_A ⥤ Cp_B) (T'D : Dp_A ⥤ Dp_B)
    (t_C : T_C ⋙ S_C_B ≅ S_C_A ⋙ T'C)
    (t_D : T_D ⋙ S_D_B ≅ S_D_A ⋙ T'D)
    (M : D_A)
    (C0 : ObjectProperty C_B)
    (hX : C0 (T_C.obj (I_A.obj M))) (hY : C0 (I_B.obj (T_D.obj M)))
    (δ_B : ∀ X : C0.FullSubcategory,
      S_D_B.obj (F_B.obj X.obj) ⟶ F'p_B.obj (S_C_B.obj X.obj))
    (hδ_B : ∀ (X Y : C0.FullSubcategory) (f : X ⟶ Y),
      S_D_B.map (F_B.map f.hom) ≫ δ_B Y =
        δ_B X ≫ F'p_B.map (S_C_B.map f.hom))
    (δ_A : S_D_A.obj (F_A.obj (I_A.obj M)) ⟶ F'p_A.obj (S_C_A.obj (I_A.obj M)))
    (Q_A : Cp_A)
    (V : ObjectProperty Dp_B)
    (hW : V (S_D_B.obj (T_D.obj M)))
    (hZ : V (T'D.obj (S_D_A.obj M)))
    (J_B : V.FullSubcategory ⥤ Cp_B)
    (E_B : ∀ Q : V.FullSubcategory,
      F'p_B.obj (J_B.obj Q) ⟶ Q.obj)
    (E_A : F'p_A.obj Q_A ⟶ S_D_A.obj M)
    (α_A : S_C_A.obj (I_A.obj M) ≅ Q_A)
    (α_B : S_C_B.obj (I_B.obj (T_D.obj M)) ≅
      J_B.obj ⟨S_D_B.obj (T_D.obj M), hW⟩)
    (hE : E_B ⟨S_D_B.obj (T_D.obj M), hW⟩ ≫ (t_D.app M).hom =
      F'p_B.map (J_B.map (ObjectProperty.homMk (P := V) (t_D.app M).hom)) ≫
        E_B ⟨T'D.obj (S_D_A.obj M), hZ⟩)
    (hCounitA : δ_A ≫ F'p_A.map α_A.hom ≫ E_A = S_D_A.map (adj_A.counit.app M))
    (hCounitB : δ_B ⟨I_B.obj (T_D.obj M), hY⟩ ≫ F'p_B.map α_B.hom ≫
      E_B ⟨S_D_B.obj (T_D.obj M), hW⟩ = S_D_B.map (adj_B.counit.app (T_D.obj M)))
    (hδA : IsIso δ_A)
    (hδBX : IsIso (δ_B ⟨T_C.obj (I_A.obj M), hX⟩))
    (hδBY : IsIso (δ_B ⟨I_B.obj (T_D.obj M), hY⟩))
    (c : T_D.obj (F_A.obj (I_A.obj M)) ≅ F_B.obj (T_C.obj (I_A.obj M)))
    (c' : ∀ Q : Cp_A,
      T'D.obj (F'p_A.obj Q) ⟶ F'p_B.obj (T'C.obj Q))
    (hc' : c' (S_C_A.obj (I_A.obj M)) ≫ F'p_B.map (T'C.map α_A.hom) =
      T'D.map (F'p_A.map α_A.hom) ≫ c' Q_A)
    (hc'U : IsIso (c' (S_C_A.obj (I_A.obj M))))
    [hc'Q : IsIso (c' Q_A)]
    (hcoef :
      (t_D.app (F_A.obj (I_A.obj M))).hom ≫ T'D.map δ_A ≫ c' (S_C_A.obj (I_A.obj M)) =
        S_D_B.map c.hom ≫ δ_B ⟨T_C.obj (I_A.obj M), hX⟩ ≫
          F'p_B.map (t_C.app (I_A.obj M)).hom)
    (b' : T'C.obj Q_A ≅
      J_B.obj ⟨T'D.obj (S_D_A.obj M), hZ⟩)
    (hb' : F'p_B.map b'.hom ≫ E_B ⟨T'D.obj (S_D_A.obj M), hZ⟩ =
      inv (c' Q_A) ≫ T'D.map E_A)
    (P : ObjectProperty C_B)
    (hPX : P (T_C.obj (I_A.obj M))) (hPY : P (I_B.obj (T_D.obj M)))
    (hFF : (P.ι ⋙ S_C_B).FullyFaithful)
    (hSD : Function.Injective
      (fun f : F_B.obj (T_C.obj (I_A.obj M)) ⟶ T_D.obj M ↦ S_D_B.map f)) :
    ∃ b : T_C.obj (I_A.obj M) ⟶ I_B.obj (T_D.obj M),
      IsIso b ∧
      S_C_B.map b =
        ((t_C.app (I_A.obj M) ≪≫ T'C.mapIso α_A).hom ≫
          b'.hom ≫
          (α_B ≪≫ J_B.mapIso (ObjectProperty.isoMk (P := V)
            (X := (⟨S_D_B.obj (T_D.obj M), hW⟩ : V.FullSubcategory))
            (Y := (⟨T'D.obj (S_D_A.obj M), hZ⟩ : V.FullSubcategory))
            (t_D.app M))).symm.hom) ∧
      F_B.map b ≫ adj_B.counit.app (T_D.obj M) =
        c.inv ≫ T_D.map (adj_A.counit.app M) ∧
      ∀ b'' : T_C.obj (I_A.obj M) ⟶ I_B.obj (T_D.obj M),
        IsIso b'' →
        S_C_B.map b'' =
          ((t_C.app (I_A.obj M) ≪≫ T'C.mapIso α_A).hom ≫
            b'.hom ≫
            (α_B ≪≫ J_B.mapIso (ObjectProperty.isoMk (P := V)
              (X := (⟨S_D_B.obj (T_D.obj M), hW⟩ : V.FullSubcategory))
              (Y := (⟨T'D.obj (S_D_A.obj M), hZ⟩ : V.FullSubcategory))
              (t_D.app M))).symm.hom) →
        b'' = b := by
  have _ := And.intro hδA (And.intro hδBX (And.intro hδBY hc'U))
  let q : S_C_B.obj (T_C.obj (I_A.obj M)) ⟶
      S_C_B.obj (I_B.obj (T_D.obj M)) :=
    (t_C.app (I_A.obj M) ≪≫ T'C.mapIso α_A).hom ≫
      b'.hom ≫
      (α_B ≪≫ J_B.mapIso (ObjectProperty.isoMk (P := V)
        (X := (⟨S_D_B.obj (T_D.obj M), hW⟩ : V.FullSubcategory))
        (Y := (⟨T'D.obj (S_D_A.obj M), hZ⟩ : V.FullSubcategory))
        (t_D.app M))).symm.hom
  let bb : (⟨T_C.obj (I_A.obj M), hPX⟩ : P.FullSubcategory) ⟶
      (⟨I_B.obj (T_D.obj M), hPY⟩ : P.FullSubcategory) :=
    hFF.preimage q
  let b : T_C.obj (I_A.obj M) ⟶ I_B.obj (T_D.obj M) := bb.hom
  have hq : IsIso q := by
    dsimp [q]
    infer_instance
  have : IsIso ((P.ι ⋙ S_C_B).map bb) := by
    rw [hFF.map_preimage (X := ⟨T_C.obj (I_A.obj M), hPX⟩)
      (Y := ⟨I_B.obj (T_D.obj M), hPY⟩) q]
    infer_instance
  have : IsIso bb := hFF.isIso_of_isIso_map bb
  have : IsIso b := by
    dsimp [b]
    infer_instance
  have hb : S_C_B.map b = q := by
    change (P.ι ⋙ S_C_B).map bb = q
    exact hFF.map_preimage (X := ⟨T_C.obj (I_A.obj M), hPX⟩)
      (Y := ⟨I_B.obj (T_D.obj M), hPY⟩) q
  let j : (⟨S_D_B.obj (T_D.obj M), hW⟩ : V.FullSubcategory) ≅
      ⟨T'D.obj (S_D_A.obj M), hZ⟩ :=
    ObjectProperty.isoMk (P := V)
      (X := (⟨S_D_B.obj (T_D.obj M), hW⟩ : V.FullSubcategory))
      (Y := (⟨T'D.obj (S_D_A.obj M), hZ⟩ : V.FullSubcategory))
      (t_D.app M)
  have hcomp : S_C_B.map b ≫ α_B.hom =
      (t_C.app (I_A.obj M) ≪≫ T'C.mapIso α_A).hom ≫
        b'.hom ≫ (J_B.mapIso j).inv := by
    rw [hb]
    dsimp [q, j]
    simp
  have hEinv : F'p_B.map (J_B.mapIso j).inv ≫
      E_B ⟨S_D_B.obj (T_D.obj M), hW⟩ =
        E_B ⟨T'D.obj (S_D_A.obj M), hZ⟩ ≫ (t_D.app M).inv := by
    apply (cancel_mono (t_D.app M).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hE]
    change F'p_B.map (J_B.map j.inv) ≫
        F'p_B.map (J_B.map j.hom) ≫ E_B ⟨T'D.obj (S_D_A.obj M), hZ⟩ = _
    rw [← F'p_B.map_comp_assoc, ← J_B.map_comp, j.inv_hom_id,
      J_B.map_id, F'p_B.map_id, Category.id_comp]
  let b0 :
      (⟨T_C.obj (I_A.obj M), hX⟩ : C0.FullSubcategory) ⟶
        (⟨I_B.obj (T_D.obj M), hY⟩ : C0.FullSubcategory) :=
    ⟨b⟩
  have hδ := hδ_B _ _ b0
  refine ⟨b, inferInstance, ?_, ?_, ?_⟩
  · exact hb
  · apply hSD
    apply (cancel_epi (S_D_B.map c.hom)).1
    simp only [Functor.map_comp]
    rw [← hCounitB, reassoc_of% hδ]
    rw [← F'p_B.map_comp_assoc, hcomp]
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [hEinv, reassoc_of% hb', ← reassoc_of% hcoef, reassoc_of% hc']
    simp only [IsIso.hom_inv_id_assoc]
    rw [← T'D.map_comp_assoc (F'p_A.map α_A.hom) E_A,
      ← T'D.map_comp_assoc δ_A, hCounitA]
    have ht := t_D.hom.naturality (adj_A.counit.app M)
    change S_D_B.map (T_D.map (adj_A.counit.app M)) ≫ (t_D.app M).hom =
      (t_D.app (F_A.obj (I_A.obj M))).hom ≫
        T'D.map (S_D_A.map (adj_A.counit.app M)) at ht
    rw [← reassoc_of% ht]
    simp [← Functor.map_comp]
  · intro b'' _ hb''
    have hbb : (ObjectProperty.homMk (P := P) (X := ⟨_, hPX⟩)
        (Y := ⟨_, hPY⟩) b'') = bb := by
      apply hFF.map_injective
      change S_C_B.map b'' = S_C_B.map b
      exact hb''.trans hb.symm
    exact congrArg (fun f ↦ f.hom) hbb

end CategoryTheory
