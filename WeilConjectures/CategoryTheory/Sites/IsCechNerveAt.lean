/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Objects identified with the objects of a Čech nerve

Let `g : V ⟶ U` be a morphism whose Čech nerve `V ×_U ⋯ ×_U V` exists. The structure
`CategoryTheory.IsCechNerveAt g n P` records projections `P ⟶ V`, a structure map `P ⟶ U` and an
isomorphism of `P` with the `n`-th object of the Čech nerve of `g` compatible with them. It
allows to build the objects of a Čech nerve by iterated binary pullbacks
(`CategoryTheory.IsCechNerveAt.succ`), and to transport the face maps and the Čech differential
on sections of a presheaf (`CategoryTheory.IsCechNerveAt.faceD`) along such identifications.

This is a port, for presheaves with values in an arbitrary preadditive category, of the
corresponding part of `Proetale/Topology/Comparison/CechColimit.lean` of the `proetale`
package.
-/

@[expose] public section

universe w₁ w₂ v u

open CategoryTheory Limits Opposite Simplicial

namespace CategoryTheory

namespace Arrow

variable {D : Type*} [Category* D] {X Y : D} (g : X ⟶ Y)
    [∀ n : ℕ, HasWidePullback (Arrow.mk g).right
      (fun _ : Fin (n + 1) ↦ (Arrow.mk g).left) fun _ ↦ (Arrow.mk g).hom]

@[reassoc (attr := simp)]
lemma cechNerve_map_comp_base {m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m') :
    (Arrow.mk g).cechNerve.map θ ≫ WidePullback.base _ = WidePullback.base _ := by
  dsimp [Arrow.cechNerve]
  rw [WidePullback.lift_base]

@[reassoc (attr := simp)]
lemma cechNerve_map_comp_π {m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m')
    (j : Fin (m'.unop.len + 1)) :
    (Arrow.mk g).cechNerve.map θ ≫ WidePullback.π _ j =
      WidePullback.π _ (θ.unop.toOrderHom j) := by
  dsimp [Arrow.cechNerve]
  rw [WidePullback.lift_π]

end Arrow

section CechIter

variable {D : Type w₂} [Category.{w₁} D] {V U : D}

variable (g : V ⟶ U) [∀ k : ℕ, HasWidePullback (Arrow.mk g).right
    (fun _ : Fin (k + 1) ↦ (Arrow.mk g).left) fun _ ↦ (Arrow.mk g).hom]

/-- Data exhibiting `P` as the `n`-th object of the Čech nerve of `g`. -/
structure IsCechNerveAt (n : ℕ) (P : D) where
  /-- The projections to `V`. -/
  π : Fin (n + 1) → (P ⟶ V)
  /-- The structure map to `U`. -/
  base : P ⟶ U
  wπ : ∀ j, π j ≫ g = base
  /-- The comparison isomorphism with the wide pullback. -/
  iso : P ≅ (Arrow.mk g).cechNerve.obj (op ⦋n⦌)
  iso_π : ∀ j, iso.hom ≫ WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j = π j
  iso_base : iso.hom ≫ WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) = base

/-- Forgetting the last projection of a Čech nerve object. -/
noncomputable def cechNerveForgetLast (k : ℕ) :
    (Arrow.mk g).cechNerve.obj (op ⦋k + 1⦌) ⟶ (Arrow.mk g).cechNerve.obj (op ⦋k⦌) :=
  WidePullback.lift (WidePullback.base _)
    (fun j : Fin (k + 1) ↦ WidePullback.π (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) j.castSucc)
    (fun _ ↦ WidePullback.π_arrow _ _)

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_π (k : ℕ) (j : Fin (k + 1)) :
    cechNerveForgetLast g k ≫ WidePullback.π (fun _ : Fin (k + 1) ↦ (Arrow.mk g).hom) j =
      WidePullback.π (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) j.castSucc :=
  WidePullback.lift_π _ _ _ _ j

@[reassoc (attr := simp)]
lemma cechNerveForgetLast_base (k : ℕ) :
    cechNerveForgetLast g k ≫ WidePullback.base (fun _ : Fin (k + 1) ↦ (Arrow.mk g).hom) =
      WidePullback.base (fun _ : Fin (k + 2) ↦ (Arrow.mk g).hom) :=
  WidePullback.lift_base _ _ _ _

namespace IsCechNerveAt

variable {g} {n : ℕ} {P : D}

@[reassoc]
lemma inv_π (h : IsCechNerveAt g n P) (j : Fin (n + 1)) :
    h.iso.inv ≫ h.π j = WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j := by
  rw [← h.iso_π, Iso.inv_hom_id_assoc]

@[reassoc]
lemma inv_base (h : IsCechNerveAt g n P) :
    h.iso.inv ≫ h.base = WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) := by
  rw [← h.iso_base, Iso.inv_hom_id_assoc]

lemma hom_ext (h : IsCechNerveAt g n P) {Z : D} {t₁ t₂ : Z ⟶ P}
    (hπ : ∀ j, t₁ ≫ h.π j = t₂ ≫ h.π j) (hbase : t₁ ≫ h.base = t₂ ≫ h.base) :
    t₁ = t₂ := by
  rw [← cancel_mono h.iso.hom]
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, Category.assoc, h.iso_π, hπ]
  · rw [Category.assoc, Category.assoc, h.iso_base, hbase]

variable (g) in
/-- `V` itself is the `0`-th object of the Čech nerve of `g`. -/
noncomputable def zero : IsCechNerveAt g 0 V where
  π _ := 𝟙 V
  base := g
  wπ _ := Category.id_comp g
  iso :=
    { hom := WidePullback.lift g (fun _ : Fin 1 ↦ 𝟙 V) (fun _ ↦ Category.id_comp g)
      inv := WidePullback.π (fun _ : Fin 1 ↦ (Arrow.mk g).hom) 0
      hom_inv_id := WidePullback.lift_π _ _ _ _ 0
      inv_hom_id := by
        apply WidePullback.hom_ext
        · intro j
          rw [Category.assoc, WidePullback.lift_π, Category.comp_id, Category.id_comp]
          exact congrArg (WidePullback.π fun _ : Fin 1 ↦ (Arrow.mk g).hom)
            (Subsingleton.elim (0 : Fin 1) j)
        · rw [Category.assoc, WidePullback.lift_base, Category.id_comp]
          exact WidePullback.π_arrow _ 0 }
  iso_π j := WidePullback.lift_π _ _ _ _ j
  iso_base := WidePullback.lift_base _ _ _ _

@[simp]
lemma zero_π (j : Fin 1) : (zero g).π j = 𝟙 V := rfl

@[simp]
lemma zero_base : (zero g).base = g := rfl

/-- Extend Čech nerve data one degree up along a binary pullback. The new projections,
base map and the comparison equations are supplied as data to avoid definitional
unfolding issues at use sites. -/
noncomputable def succ (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    IsCechNerveAt g (n + 1) P' := by
  have wπ' : ∀ j : Fin (n + 2), π' j ≫ g = base' := by
    intro j
    induction j using Fin.lastCases with
    | last => rw [hlast, hbase]
    | cast j => rw [hπ, hbase, Category.assoc, h.wπ, sq.w]
  have hcomm : (cechNerveForgetLast g n ≫ h.iso.inv) ≫ h.base =
      WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) (Fin.last (n + 1)) ≫ g := by
    rw [Category.assoc, h.inv_base, cechNerveForgetLast_base]
    exact (WidePullback.π_arrow _ _).symm
  have hfst : WidePullback.lift (arrows := fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
      base' π' wπ' ≫ cechNerveForgetLast g n = fst ≫ h.iso.hom := by
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.assoc, cechNerveForgetLast_π, WidePullback.lift_π,
        h.iso_π, hπ]
    · rw [Category.assoc, Category.assoc, cechNerveForgetLast_base, WidePullback.lift_base,
        h.iso_base, hbase, sq.w]
  refine
    { π := π'
      base := base'
      wπ := wπ'
      iso :=
        { hom := WidePullback.lift (arrows := fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
            base' π' wπ'
          inv := sq.lift (cechNerveForgetLast g n ≫ h.iso.inv)
            (WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) (Fin.last (n + 1)))
            hcomm
          hom_inv_id := ?_
          inv_hom_id := ?_ }
      iso_π := fun j ↦ WidePullback.lift_π _ _ _ _ j
      iso_base := WidePullback.lift_base _ _ _ _ }
  · apply sq.hom_ext
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, hfst, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, IsPullback.lift_snd, WidePullback.lift_π, hlast, Category.id_comp]
  · apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, Category.id_comp]
      induction j using Fin.lastCases with
      | last => rw [WidePullback.lift_π, hlast, IsPullback.lift_snd]
      | cast j =>
        rw [WidePullback.lift_π, hπ, ← Category.assoc, IsPullback.lift_fst,
          Category.assoc, h.inv_π, cechNerveForgetLast_π]
    · rw [Category.assoc, Category.id_comp, WidePullback.lift_base, hbase,
        ← Category.assoc, IsPullback.lift_snd]
      exact WidePullback.π_arrow _ _

@[simp]
lemma succ_π (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) (j : Fin (n + 2)) :
    (h.succ sq π' base' hπ hlast hbase).π j = π' j := rfl

@[simp]
lemma succ_base (h : IsCechNerveAt g n P) {P' : D} {fst : P' ⟶ P} {snd : P' ⟶ V}
    (sq : IsPullback fst snd h.base g) (π' : Fin (n + 2) → (P' ⟶ V)) (base' : P' ⟶ U)
    (hπ : ∀ j : Fin (n + 1), π' j.castSucc = fst ≫ h.π j)
    (hlast : π' (Fin.last (n + 1)) = snd) (hbase : base' = snd ≫ g) :
    (h.succ sq π' base' hπ hlast hbase).base = base' := rfl

/-- The `i`-th face map between objects carrying Čech nerve data. -/
noncomputable def face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) : P' ⟶ P :=
  h'.iso.hom ≫ (Arrow.mk g).cechNerve.δ i ≫ h.iso.inv

@[reassoc]
lemma face_π {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) (j : Fin (n + 1)) :
    h'.face h i ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j) := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.π (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) j =
        WidePullback.π (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom)
          ((SimplexCategory.δ i).toOrderHom j) :=
    Arrow.cechNerve_map_comp_π g ((SimplexCategory.δ i).op) j
  rw [face, Category.assoc, Category.assoc, h.inv_π, hδ, h'.iso_π]

@[reassoc]
lemma face_base {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) :
    h'.face h i ≫ h.base = h'.base := by
  have hδ : (Arrow.mk g).cechNerve.δ i ≫
      WidePullback.base (fun _ : Fin (n + 1) ↦ (Arrow.mk g).hom) =
        WidePullback.base (fun _ : Fin (n + 2) ↦ (Arrow.mk g).hom) :=
    Arrow.cechNerve_map_comp_base g ((SimplexCategory.δ i).op)
  rw [face, Category.assoc, Category.assoc, h.inv_base, hδ, h'.iso_base]

/-- A morphism satisfying the simplicial identities of the `i`-th face map is the `i`-th
face map. -/
lemma eq_face {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (i : Fin (n + 2)) {t : P' ⟶ P}
    (htπ : ∀ j, t ≫ h.π j = h'.π ((SimplexCategory.δ i).toOrderHom j))
    (htbase : t ≫ h.base = h'.base) :
    t = h'.face h i :=
  h.hom_ext (fun j ↦ by rw [htπ, face_π]) (by rw [htbase, face_base])

section Preadditive

variable {A : Type*} [Category* A] [Preadditive A]

/-- The alternating sum of the face maps, on sections of a presheaf with values in a
preadditive category. -/
noncomputable def faceD {P' P : D} (h' : IsCechNerveAt g (n + 1) P')
    (h : IsCechNerveAt g n P) (F : Dᵒᵖ ⥤ A) :
    F.obj (op P) ⟶ F.obj (op P') :=
  ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((h'.face h i).op)

/-- The alternating sum of the face maps is conjugate to the alternating sum of the face maps
of the Čech nerve. -/
lemma faceD_eq {P' P : D} (h' : IsCechNerveAt g (n + 1) P') (h : IsCechNerveAt g n P)
    (F : Dᵒᵖ ⥤ A) :
    h'.faceD h F = F.map (h.iso.inv.op) ≫
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • F.map ((Arrow.mk g).cechNerve.δ i).op) ≫
        F.map (h'.iso.hom.op) := by
  rw [faceD, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  congr 1
  rw [face, op_comp, op_comp, Functor.map_comp, Functor.map_comp, Category.assoc]

end Preadditive

end IsCechNerveAt

end CechIter

end CategoryTheory
