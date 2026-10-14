/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTotal
public import Mathlib.Algebra.Homology.Homotopy
import Sheaf.AlgebraicGeometry.PreorderBarTotalHomotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-! # A preorder unit contracts its bar reindexing

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar
variable {I : Type u} [Preorder I] (f : I →o I) (hf : ∀ i, i ≤ f i)

def prism {n : ℕ} (σ : Fin (n + 1) →o I) (a : Fin (n + 1)) :
    Fin (n + 2) →o I where
  toFun k := if k ≤ a.castSucc then σ (a.predAbove k) else f (σ (a.predAbove k))
  monotone' := by
    intro k l hkl
    dsimp only
    split_ifs with hk hl hl
    · exact σ.monotone (Fin.predAbove_right_monotone a hkl)
    · exact (σ.monotone (Fin.predAbove_right_monotone a hkl)).trans (hf _)
    · exact False.elim (hk (hkl.trans hl))
    · exact f.monotone (σ.monotone (Fin.predAbove_right_monotone a hkl))

@[simp] lemma prism_zero {n : ℕ} (σ : Fin (n + 1) →o I) (a : Fin (n + 1)) :
    prism f hf σ a 0 = σ 0 := by
  simp [prism, Fin.predAbove]

lemma prism_face_zero {n : ℕ} (σ : Fin (n + 1) →o I) :
    (prism f hf σ 0).comp (Fin.succAboveOrderEmb 0).toOrderHom = f.comp σ := by
  ext k
  simp [prism, Fin.predAbove, Fin.succAboveOrderEmb]

lemma prism_face_last {n : ℕ} (σ : Fin (n + 1) →o I) :
    (prism f hf σ (Fin.last n)).comp
      (Fin.succAboveOrderEmb (Fin.last (n + 1))).toOrderHom = σ := by
  ext k
  simp [prism, Fin.predAbove, Fin.succAboveOrderEmb]
  simp only [dif_neg (not_lt.mpr (Fin.le_last k)), if_pos (Fin.le_last k)]

lemma predAbove_val {n : ℕ} (a : Fin n) (k : Fin (n + 1)) :
    (a.predAbove k).val = if k.val ≤ a.val then k.val else k.val - 1 := by
  simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred]
  split_ifs <;> omega

lemma succAbove_val {n : ℕ} (i : Fin (n + 1)) (k : Fin n) :
    (i.succAbove k).val = if k.val < i.val then k.val else k.val + 1 := by
  simp only [Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_ite Fin.val,
    Fin.val_succ]


lemma prism_face_before {n : ℕ} (σ : Fin (n + 2) →o I)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    (prism f hf σ j.succ).comp (Fin.succAboveOrderEmb i.castSucc).toOrderHom =
      prism f hf (σ.comp (Fin.succAboveOrderEmb i).toOrderHom) j := by
  ext k
  have hflag : (i.castSucc.succAbove k ≤ j.succ.castSucc) ↔ (k ≤ j.castSucc) := by
    simp only [Fin.le_def, succAbove_val,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        Fin.val_castSucc] at *
    all_goals omega
  have hindex : j.succ.predAbove (i.castSucc.succAbove k) = i.succAbove (j.predAbove k) := by
    apply Fin.ext
    simp only [predAbove_val, succAbove_val, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        Fin.val_castSucc, Fin.val_succ, succAbove_val] at *
    all_goals omega
  change (if i.castSucc.succAbove k ≤ j.succ.castSucc then
    σ (j.succ.predAbove (i.castSucc.succAbove k)) else
    f (σ (j.succ.predAbove (i.castSucc.succAbove k)))) =
    (if k ≤ j.castSucc then
      σ (i.succAbove (j.predAbove k)) else
      f (σ (i.succAbove (j.predAbove k))))
  simp only [hflag, hindex]

lemma prism_face_pivot {n : ℕ} (σ : Fin (n + 2) →o I) (j : Fin (n + 1)) :
    (prism f hf σ j.succ).comp (Fin.succAboveOrderEmb j.castSucc.succ).toOrderHom =
      (prism f hf σ j.castSucc).comp (Fin.succAboveOrderEmb j.castSucc.succ).toOrderHom := by
  ext k
  have hflag : (j.castSucc.succ.succAbove k ≤ j.succ.castSucc) ↔
      (j.castSucc.succ.succAbove k ≤ j.castSucc.castSucc) := by
    simp only [Fin.le_def, succAbove_val,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def, Fin.lt_def,
        Fin.val_castSucc, Fin.val_succ, predAbove_val, succAbove_val] at *
    all_goals omega
  have hindex : j.succ.predAbove (j.castSucc.succ.succAbove k) =
      j.castSucc.predAbove (j.castSucc.succ.succAbove k) := by
    apply Fin.ext
    simp only [predAbove_val, succAbove_val, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        Fin.val_castSucc, Fin.val_succ, succAbove_val] at *
    all_goals omega
  change (if j.castSucc.succ.succAbove k ≤ j.succ.castSucc then
    σ (j.succ.predAbove (j.castSucc.succ.succAbove k)) else
    f (σ (j.succ.predAbove (j.castSucc.succ.succAbove k)))) =
    (if j.castSucc.succ.succAbove k ≤ j.castSucc.castSucc then
      σ (j.castSucc.predAbove (j.castSucc.succ.succAbove k)) else
      f (σ (j.castSucc.predAbove (j.castSucc.succ.succAbove k))))
  simp only [hflag, hindex]

lemma prism_face_after {n : ℕ} (σ : Fin (n + 2) →o I)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    (prism f hf σ j.castSucc).comp (Fin.succAboveOrderEmb i.succ).toOrderHom =
      prism f hf (σ.comp (Fin.succAboveOrderEmb i).toOrderHom) j := by
  ext k
  have hflag : (i.succ.succAbove k ≤ j.castSucc.castSucc) ↔ (k ≤ j.castSucc) := by
    simp only [Fin.le_def, succAbove_val,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.lt_def,
        Fin.val_castSucc] at *
    all_goals omega
  have hindex : j.castSucc.predAbove (i.succ.succAbove k) = i.succAbove (j.predAbove k) := by
    apply Fin.ext
    simp only [predAbove_val, succAbove_val, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def, Fin.lt_def,
        Fin.val_castSucc, Fin.val_succ, succAbove_val] at *
    all_goals omega
  change (if i.succ.succAbove k ≤ j.castSucc.castSucc then
    σ (j.castSucc.predAbove (i.succ.succAbove k)) else
    f (σ (j.castSucc.predAbove (i.succ.succAbove k)))) =
    (if k ≤ j.castSucc then
      σ (i.succAbove (j.predAbove k)) else
      f (σ (i.succAbove (j.predAbove k))))
  simp only [hflag, hindex]

lemma prism_degeneracy_before {n : ℕ} (σ : Fin (n + 1) →o I)
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    (prism f hf σ j).comp (Fin.predAboveOrderHom i.castSucc) =
      prism f hf (σ.comp (Fin.predAboveOrderHom i)) j.succ := by
  ext k
  have hflag : (i.castSucc.predAbove k ≤ j.castSucc) ↔ (k ≤ j.succ.castSucc) := by
    simp only [Fin.le_def, predAbove_val,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        ] at *
    all_goals omega
  have hindex : j.predAbove (i.castSucc.predAbove k) = i.predAbove (j.succ.predAbove k) := by
    apply Fin.ext
    simp only [predAbove_val, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        Fin.val_castSucc, Fin.val_succ, predAbove_val] at *
    all_goals omega
  change (if i.castSucc.predAbove k ≤ j.castSucc then
    σ (j.predAbove (i.castSucc.predAbove k)) else
    f (σ (j.predAbove (i.castSucc.predAbove k)))) =
    (if k ≤ j.succ.castSucc then
      σ (i.predAbove (j.succ.predAbove k)) else
      f (σ (i.predAbove (j.succ.predAbove k))))
  simp only [hflag, hindex]

lemma prism_degeneracy_after {n : ℕ} (σ : Fin (n + 1) →o I)
    (i j : Fin (n + 1)) (hji : j ≤ i) :
    (prism f hf σ j).comp (Fin.predAboveOrderHom i.succ) =
      prism f hf (σ.comp (Fin.predAboveOrderHom i)) j.castSucc := by
  ext k
  have hflag : (i.succ.predAbove k ≤ j.castSucc) ↔ (k ≤ j.castSucc.castSucc) := by
    simp only [Fin.le_def, predAbove_val,
      Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        ] at *
    all_goals omega
  have hindex : j.predAbove (i.succ.predAbove k) = i.predAbove (j.castSucc.predAbove k) := by
    apply Fin.ext
    simp only [predAbove_val, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;>
      try simp only [Fin.le_def,
        Fin.val_castSucc, Fin.val_succ, predAbove_val] at *
    all_goals omega
  change (if i.succ.predAbove k ≤ j.castSucc then
    σ (j.predAbove (i.succ.predAbove k)) else
    f (σ (j.predAbove (i.succ.predAbove k)))) =
    (if k ≤ j.castSucc.castSucc then
      σ (i.predAbove (j.castSucc.predAbove k)) else
      f (σ (i.predAbove (j.castSucc.predAbove k))))
  simp only [hflag, hindex]

variable {C : Type w} [Category.{v} C] [HasCoproducts.{u} C] (D : I ⥤ C)

noncomputable def unitMap : D ⟶ orderFunctor f ⋙ D where
  app i := D.map (homOfLE (hf i))
  naturality {i j} g := by
    simp only [Functor.comp_map, orderFunctor]
    rw [← D.map_comp, ← D.map_comp]
    congr 1

noncomputable def unitH {n : ℕ} (a : Fin (n + 1)) :
    (simplicial D).obj (op ⦋n⦌) ⟶ (simplicial D).obj (op ⦋n + 1⦌) :=
  Sigma.desc (fun σ : Fin (n + 1) →o I ↦
    eqToHom (by rw [prism_zero]) ≫
      Sigma.ι (fun τ : Fin (n + 2) →o I ↦ D.obj (τ 0)) (prism f hf σ a))

@[reassoc (attr := simp)]
lemma ι_unitH {n : ℕ} (σ : Fin (n + 1) →o I) (a : Fin (n + 1)) :
    Sigma.ι (fun τ : Fin (n + 1) →o I ↦ D.obj (τ 0)) σ ≫ unitH f hf D a =
      eqToHom (by rw [prism_zero]) ≫
        Sigma.ι (fun τ : Fin (n + 2) →o I ↦ D.obj (τ 0)) (prism f hf σ a) := by
  simp [unitH]

lemma component_congr {n : ℕ} {σ τ : Fin (n + 1) →o I} {x : I}
    (α : x ⟶ σ 0) (β : x ⟶ τ 0) (e : σ = τ) :
    D.map α ≫ Sigma.ι (fun ρ : Fin (n + 1) →o I ↦ D.obj (ρ 0)) σ =
      D.map β ≫ Sigma.ι (fun ρ : Fin (n + 1) →o I ↦ D.obj (ρ 0)) τ := by
  subst τ
  rw [Subsingleton.elim α β]

noncomputable def unitSimplicialHomotopy :
    SimplicialObject.Homotopy (𝟙 (simplicial D))
      (reindex D D f (unitMap f hf D)) where
  h := unitH f hf D
  h_zero_comp_δ_zero n := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.δ, simplicial, ι_map,
      reindex, Sigma.ι_desc, unitMap]
    have he := prism_face_zero f hf σ
    rw [← eqToHom_map D (prism_zero f hf σ 0).symm, ← D.map_comp_assoc]
    exact component_congr D _ _ he
  h_last_comp_δ_last n := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.δ, simplicial, ι_map,
      NatTrans.id_app]
    rw [← eqToHom_map D (prism_zero f hf σ (Fin.last n)).symm,
      ← D.map_comp_assoc]
    simp only [obj, Category.comp_id]
    change _ = Sigma.ι (fun τ : Fin (n + 1) →o I ↦ D.obj (τ 0)) σ
    rw [← Category.id_comp (Sigma.ι (fun τ : Fin (n + 1) →o I ↦ D.obj (τ 0)) σ),
      ← D.map_id (σ 0)]
    exact component_congr D _ _ (prism_face_last f hf σ)
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.δ, simplicial, ι_map_assoc,
      ι_map, ι_unitH]
    rw [← eqToHom_map D (prism_zero f hf σ j.succ).symm,
      ← eqToHom_map D (prism_zero f hf (σ.comp ((Fin.succAboveOrderEmb i).toOrderHom)) j).symm]
    simp only [← D.map_comp_assoc]
    exact component_congr D _ _ (prism_face_before f hf σ i j hij)
  h_succ_comp_δ_castSucc_succ j := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.δ, simplicial, ι_map]
    simp only [← eqToHom_map D (prism_zero f hf σ j.succ).symm]
    simp only [← D.map_comp_assoc]
    exact component_congr D _ _ (prism_face_pivot f hf σ j)
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.δ, simplicial, ι_map_assoc,
      ι_map, ι_unitH]
    rw [← eqToHom_map D (prism_zero f hf σ j.castSucc).symm,
      ← eqToHom_map D (prism_zero f hf (σ.comp ((Fin.succAboveOrderEmb i).toOrderHom)) j).symm]
    simp only [← D.map_comp_assoc]
    exact component_congr D _ _ (prism_face_after f hf σ i j hji)
  h_comp_σ_castSucc_of_le i j hij := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.σ, simplicial, ι_map_assoc,
      ι_map, ι_unitH]
    simp only [← eqToHom_map D (prism_zero f hf σ j).symm]
    simp only [← D.map_comp_assoc]
    exact component_congr D _ _ (prism_degeneracy_before f hf σ i j hij)
  h_comp_σ_succ_of_lt i j hji := by
    apply Sigma.hom_ext
    intro σ
    simp only [ι_unitH_assoc, SimplicialObject.σ, simplicial, ι_map_assoc,
      ι_map, ι_unitH]
    simp only [← eqToHom_map D (prism_zero f hf σ j).symm]
    simp only [← D.map_comp_assoc]
    exact component_congr D _ _ (prism_degeneracy_after f hf σ i j hji)
variable {A : Type w} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasCoproducts.{u} A] [HasCoproducts.{0} A]

omit [HasZeroObject A] in
/-- A preorder unit contracts its bar reindexing.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-preorder-bar-unit-homotopy).

Proof: For insertion position a, duplicate the vertex σ(a), retain vertices before it, and apply f
to the
vertices after it. The inequality σ(a)≤f(σ(a)) makes this a monotone string. The coefficient map
is the identity, since the first vertex is unchanged. Check all face and degeneracy identities by
deleting or repeating vertices before, at, and after the insertion. This gives a simplicial
homotopy from identity to unit reindexing. Mathlib turns its alternating sum into a horizontal
chain homotopy; horizontalHomotopy totalizes it. -/
theorem totalUnitHomotopy (D' : I ⥤ CochainComplex A ℤ) :
    Nonempty (Homotopy (totalMap D' D' f (unitMap f hf D')) (𝟙 (total D'))) := by
  have h := (unitSimplicialHomotopy f hf D').toChainHomotopy
  let H := horizontalHomotopy h.symm
  exact ⟨by simpa [totalMap, total, bicomplex, AlgebraicTopology.alternatingFaceMapComplex] using H⟩

end CategoryTheory.PreorderBar
