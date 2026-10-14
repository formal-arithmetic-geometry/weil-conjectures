/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module
public import Sheaf.AlgebraicGeometry.PreorderBarTerminalAugmentation
public import Mathlib.Data.Fin.Tuple.Basic

/-! # An explicit extra degeneracy for bars of partial sums

Explicit constructions and proved properties for the bar-union argument.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite Simplicial
namespace CategoryTheory.PreorderBar.PartialSum
variable {C : Type w} [Category.{v} C] [HasCoproducts.{0} C]
  [HasCoproducts.{u} C] (F : ℕ → C) (r : ℕ)

noncomputable def sum (n : ℕ) := ∐ (fun k : Fin (n + r + 1) ↦ F k)

noncomputable def inclusion {n m : ℕ} (h : n ≤ m) : sum F r n ⟶ sum F r m :=
  Sigma.desc (fun k : Fin (n + r + 1) ↦ Sigma.ι (fun j : Fin (m + r + 1) ↦ F j)
    ⟨k, by omega⟩)

noncomputable def diagram : ULift.{u} ℕ ⥤ C where
  obj n := sum F r n.down
  map {n m} g := inclusion F r (by
    have h : n ≤ m := leOfHom g
    exact h)
  map_id n := by
    apply Sigma.hom_ext
    intro k
    simp only [inclusion, Sigma.ι_desc]
    simp [sum]
  map_comp g h := by
    apply Sigma.hom_ext
    intro k
    simp [inclusion]

noncomputable def cocone : Cocone (diagram.{u} F r) where
  pt := ∐ F
  ι := { app n := Sigma.desc (fun k : Fin (n.down + r + 1) ↦ Sigma.ι F k)
         naturality {n m} g := by
           apply Sigma.hom_ext
           intro k
           simp [diagram, inclusion] }

def prepend {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ) (b : ℕ)
    (hb : b ≤ (σ 0).down) : Fin (n + 2) →o ULift.{u} ℕ where
  toFun := Fin.cons ⟨b⟩ σ
  monotone' := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j => exact hb.trans (σ.monotone (Fin.zero_le j))
    | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (by simp at hij)
      | succ j => exact σ.monotone (by simpa using hij)

@[simp] lemma prepend_zero {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (b : ℕ) (hb : b ≤ (σ 0).down) : prepend σ b hb 0 = ⟨b⟩ := rfl

@[simp] lemma prepend_succ {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (b : ℕ) (hb : b ≤ (σ 0).down) (k : Fin (n + 1)) :
    prepend σ b hb k.succ = σ k := rfl

noncomputable def sectionMap : ∐ F ⟶ (simplicial (diagram.{u} F r)).obj (op ⦋0⦌) :=
  Sigma.desc (fun k : ℕ ↦
    Sigma.ι (fun j : Fin (k - r + r + 1) ↦ F j) ⟨k, by omega⟩ ≫
      Sigma.ι (fun σ : Fin 1 →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (σ 0))
        (OrderHom.const _ ⟨k - r⟩))

noncomputable def extra (n : ℕ) :
    (simplicial (diagram.{u} F r)).obj (op ⦋n⦌) ⟶
      (simplicial (diagram.{u} F r)).obj (op ⦋n + 1⦌) :=
  Sigma.desc (fun σ : Fin (n + 1) →o ULift.{u} ℕ ↦
    Sigma.desc (fun k : Fin ((σ 0).down + r + 1) ↦
      Sigma.ι (fun j : Fin (k.val - r + r + 1) ↦ F j) ⟨k, by omega⟩ ≫
        Sigma.ι (fun τ : Fin (n + 2) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0))
          (prepend σ (k.val - r) (by have := k.isLt; omega))))

@[reassoc (attr := simp)]
lemma ι_extra (n : ℕ) (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (k : Fin ((σ 0).down + r + 1)) :
    Sigma.ι (fun j : Fin ((σ 0).down + r + 1) ↦ F j) k ≫
      Sigma.ι (fun τ : Fin (n + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0)) σ ≫
        extra F r n =
      Sigma.ι (fun j : Fin (k.val - r + r + 1) ↦ F j) ⟨k, by omega⟩ ≫
        Sigma.ι (fun τ : Fin (n + 2) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0))
          (prepend σ (k.val - r) (by have := k.isLt; omega)) := by
  simp [extra]

@[reassoc (attr := simp)]
lemma ι_barMap {n m : SimplexCategory} (α : m ⟶ n)
    (σ : Fin (n.len + 1) →o ULift.{u} ℕ) (k : Fin ((σ 0).down + r + 1)) :
    Sigma.ι (fun j : Fin ((σ 0).down + r + 1) ↦ F j) k ≫
      Sigma.ι (fun τ : Fin (n.len + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0)) σ ≫
        PreorderBar.map (diagram.{u} F r) α =
      Sigma.ι (fun j : Fin ((σ (α.toOrderHom 0)).down + r + 1) ↦ F j)
        ⟨k, by
          have h : (σ 0).down ≤ (σ (α.toOrderHom 0)).down :=
            σ.monotone (Fin.zero_le (α.toOrderHom 0))
          omega⟩ ≫
      Sigma.ι (fun τ : Fin (m.len + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0))
        (σ.comp α.toOrderHom) := by
  rw [PreorderBar.ι_map]
  simp only [diagram, inclusion, Sigma.ι_desc_assoc]

lemma prepend_face_zero {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (b : ℕ) (hb : b ≤ (σ 0).down) :
    (prepend σ b hb).comp (Fin.succAboveOrderEmb 0).toOrderHom = σ := by
  ext k
  rfl

lemma prepend_face_succ {n : ℕ} (σ : Fin (n + 2) →o ULift.{u} ℕ)
    (b : ℕ) (hb : b ≤ (σ 0).down) (i : Fin (n + 2)) :
    (prepend σ b hb).comp (Fin.succAboveOrderEmb i.succ).toOrderHom =
      prepend (σ.comp (Fin.succAboveOrderEmb i).toOrderHom) b
        (hb.trans (σ.monotone (Fin.zero_le (i.succAbove 0)))) := by
  ext k
  cases k using Fin.cases with
  | zero => simp [Fin.succAboveOrderEmb]
  | succ k => simp [Fin.succAboveOrderEmb]

lemma prepend_degeneracy_succ {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (b : ℕ) (hb : b ≤ (σ 0).down) (i : Fin (n + 1)) :
    (prepend σ b hb).comp (Fin.predAboveOrderHom i.succ) =
      prepend (σ.comp (Fin.predAboveOrderHom i)) b
        (hb.trans (σ.monotone (Fin.zero_le (i.predAbove 0)))) := by
  ext k
  cases k using Fin.cases with
  | zero => simp [Fin.predAboveOrderHom, Fin.predAbove]
  | succ k => simp [Fin.predAboveOrderHom]

lemma double_ι_congr {n : ℕ} {σ τ : Fin (n + 1) →o ULift.{u} ℕ} {k : ℕ}
    (h : k < (σ 0).down + r + 1) (h' : k < (τ 0).down + r + 1) (e : σ = τ) :
    Sigma.ι (fun j : Fin ((σ 0).down + r + 1) ↦ F j) ⟨k, h⟩ ≫
      Sigma.ι (fun ρ : Fin (n + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (ρ 0)) σ =
    Sigma.ι (fun j : Fin ((τ 0).down + r + 1) ↦ F j) ⟨k, h'⟩ ≫
      Sigma.ι (fun ρ : Fin (n + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (ρ 0)) τ := by
  subst τ
  rfl

noncomputable def gen {n : SimplexCategory} (σ : Fin (n.len + 1) →o ULift.{u} ℕ)
    (k : Fin ((σ 0).down + r + 1)) : F k ⟶ obj (diagram.{u} F r) n :=
  Sigma.ι (fun j : Fin ((σ 0).down + r + 1) ↦ F j) k ≫
    Sigma.ι (fun τ : Fin (n.len + 1) →o ULift.{u} ℕ ↦ (diagram.{u} F r).obj (τ 0)) σ

@[reassoc]
lemma gen_map {n m : SimplexCategory} (α : m ⟶ n)
    (σ : Fin (n.len + 1) →o ULift.{u} ℕ) (k : Fin ((σ 0).down + r + 1)) :
    gen F r σ k ≫ PreorderBar.map (diagram.{u} F r) α =
      gen F r (σ.comp α.toOrderHom) ⟨k, by
        have h : (σ 0).down ≤ (σ (α.toOrderHom 0)).down :=
          σ.monotone (Fin.zero_le (α.toOrderHom 0))
        change k.val < (σ (α.toOrderHom 0)).down + r + 1
        omega⟩ := by
  exact (Category.assoc _ _ _).trans (ι_barMap F r α σ k)

@[reassoc]
lemma gen_extra {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (k : Fin ((σ 0).down + r + 1)) :
    gen F r (n := ⦋n⦌) σ k ≫ extra F r n =
      gen F r (n := ⦋n + 1⦌)
        (prepend σ (k.val - r) (by have := k.isLt; omega))
        ⟨k, by change k.val < k.val - r + r + 1; omega⟩ := by
  exact (Category.assoc _ _ _).trans (ι_extra F r n σ k)

lemma gen_congr {n : SimplexCategory} {σ τ : Fin (n.len + 1) →o ULift.{u} ℕ} {k : ℕ}
    (h : k < (σ 0).down + r + 1) (h' : k < (τ 0).down + r + 1) (e : σ = τ) :
    gen F r σ ⟨k, h⟩ = gen F r τ ⟨k, h'⟩ := by subst τ; rfl

@[reassoc]
lemma gen_augmentation {n : ℕ} (σ : Fin (n + 1) →o ULift.{u} ℕ)
    (k : Fin ((σ 0).down + r + 1)) :
    gen F r (n := ⦋n⦌) σ k ≫ (augmentation (diagram.{u} F r) (cocone F r)).app (op ⦋n⦌) =
      Sigma.ι F k := by
  simp [gen, augmentation, cocone, Category.assoc]

lemma ι_section (k : ℕ) : Sigma.ι F k ≫ sectionMap F r =
    gen F r (n := ⦋0⦌) (OrderHom.const _ ⟨k - r⟩) ⟨k, by change k < k - r + r + 1; omega⟩ := by
  simp only [sectionMap, Sigma.ι_desc]
  rfl

/-- An explicit extra degeneracy for bars of partial sums.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: def-sc-partial-sum-bar-extra-degeneracy).

Proof: On the summand F(k) of a string beginning at n, prepend the first stage k-r containing it,
using
truncated natural subtraction. Since k<n+r+1, k-r≤n, and since k<k-r+r+1, the same summand exists
there. The augmentation section includes F(k) at the constant zero-simplex k-r. Deleting the new
vertex is identity; deleting an old vertex or repeating a vertex commutes with prepending.
Deleting the other vertex in degree one gives section after augmentation. Verify these identities
on the two levels of coproduct generators. Thus every extra-degeneracy field is proved and all its
data is constructed directly. -/
noncomputable def extraDegeneracy :
    SimplicialObject.Augmented.ExtraDegeneracy (augmented (diagram.{u} F r) (cocone F r)) where
  s' := sectionMap F r
  s := extra F r
  s'_comp_ε := by
    apply Sigma.hom_ext
    intro k
    simp [sectionMap, augmented, augmentation, cocone, Sigma.ι_desc]
  s₀_comp_δ₁ := by
    apply Sigma.hom_ext
    intro σ
    apply Sigma.hom_ext
    intro k
    simp only [← Category.assoc]
    change (gen F r σ k ≫ extra F r 0) ≫ map (diagram.{u} F r) (SimplexCategory.δ 1) =
      (gen F r σ k ≫ (augmentation (diagram.{u} F r) (cocone F r)).app (op ⦋0⦌)) ≫
        sectionMap F r
    rw [gen_extra, gen_map, gen_augmentation, ι_section]
    apply gen_congr F r
    ext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    apply Sigma.hom_ext
    intro σ
    apply Sigma.hom_ext
    intro k
    simp only [← Category.assoc]
    change (gen F r σ k ≫ extra F r n) ≫ map (diagram.{u} F r) (SimplexCategory.δ 0) =
      gen F r σ k ≫ 𝟙 _
    rw [gen_extra, gen_map, Category.comp_id]
    exact gen_congr F r _ _ (prepend_face_zero σ _ _)
  s_comp_δ n i := by
    apply Sigma.hom_ext
    intro σ
    apply Sigma.hom_ext
    intro k
    simp only [← Category.assoc]
    change (gen F r σ k ≫ extra F r (n + 1)) ≫
      map (diagram.{u} F r) (SimplexCategory.δ i.succ) =
        (gen F r σ k ≫ map (diagram.{u} F r) (SimplexCategory.δ i)) ≫ extra F r n
    rw [gen_extra, gen_map, gen_map, gen_extra]
    exact gen_congr F r _ _ (prepend_face_succ σ _ _ i)
  s_comp_σ n i := by
    apply Sigma.hom_ext
    intro σ
    apply Sigma.hom_ext
    intro k
    simp only [← Category.assoc]
    change (gen F r σ k ≫ extra F r n) ≫
      map (diagram.{u} F r) (SimplexCategory.σ i.succ) =
        (gen F r σ k ≫ map (diagram.{u} F r) (SimplexCategory.σ i)) ≫ extra F r (n + 1)
    rw [gen_extra, gen_map, gen_map, gen_extra]
    exact gen_congr F r _ _ (prepend_degeneracy_succ σ _ _ i)

variable {A : Type w} [Category.{v} A] [Preadditive A] [HasZeroObject A]
  [HasCoproducts.{u} A] [HasCoproducts.{0} A]

noncomputable def totalEquiv (E : ℕ → CochainComplex A ℤ) (r : ℕ) :
    HomotopyEquiv (total (diagram.{u} E r)) (∐ E) := by
  let h : SimplicialObject.Augmented.ExtraDegeneracy
      (augmented (diagram.{u} E r) (cocone E r)) := extraDegeneracy.{u} E r
  let e := totalizeHomotopyEquiv h.homotopyEquiv
  haveI := collapse_isIso (∐ E)
  exact e.trans (HomotopyEquiv.ofIso (asIso (collapse (∐ E))))

lemma totalEquiv_hom (E : ℕ → CochainComplex A ℤ) (r : ℕ) :
    (totalEquiv.{u} E r).hom = totalAugmentation (diagram.{u} E r) (cocone E r) := rfl

/-- Partial-sum bar augmentation is a homotopy isomorphism.

Source: the source-bar and finite-cone-block argument in
`lem-sc-compact-flat-bar-union-augmentation`.
(blueprint: lem-sc-partial-sum-bar-augmentation).

Proof: Use the constructed extra degeneracy and Mathlib ExtraDegeneracy.homotopyEquiv to contract
the
alternating face-map complex to its single column. Totalize its explicit homotopy equivalence
using horizontalHomotopy. Compose with the single-column collapse isomorphism. The resulting hom
map is definitionally the canonical total augmentation, hence its quotient map is an isomorphism. -/
theorem augmentation_isIsoHomotopy (E : ℕ → CochainComplex A ℤ) (r : ℕ) :
    IsIso ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      (totalAugmentation (diagram.{u} E r) (cocone E r))) := by
  rw [← totalEquiv_hom.{u} E r]
  exact (HomotopyCategory.isoOfHomotopyEquiv (totalEquiv.{u} E r)).isIso_hom

end CategoryTheory.PreorderBar.PartialSum
