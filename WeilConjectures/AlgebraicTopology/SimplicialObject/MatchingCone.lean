/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicTopology.SimplicialObject.AttachCells
public import WeilConjectures.CategoryTheory.SimplicialBoundaryFaces
public import WeilConjectures.CategoryTheory.SimplicialMatchingObject
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Matching objects of simplicial objects

For a simplicial object `W` in a category `C`, a boundary cone `c : BoundaryCone W n M`
(a compatible family of maps from `M` to the simplices of `W` on the boundary of the
`n`-simplex) is a *matching cone* if every boundary cone factors uniquely through it.

## Main definitions and results

- `CategoryTheory.SimplicialObject.IsMatchingCone`: the universal property.
- `CategoryTheory.SimplicialObject.matchingObj`: a matching object, when `C` has finite limits,
  built as the terminal object (`n = 0`), the product of two copies of `W _⦋0⦌` (`n = 1`)
  and a multiequalizer of faces (`n ≥ 2`).
- `CategoryTheory.SimplicialObject.isMatchingCone_map_matchingObjCone`: functors preserving
  finite limits preserve this matching object.
- `CategoryTheory.SimplicialObject.IsMatchingCone.postcomp`: matching cones can be transported
  along maps of simplicial objects which are isomorphisms in degrees `< n`.
-/

@[expose] public section

noncomputable section

universe v u v' u'

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace BoundaryCone

variable {W : SimplicialObject C} {n : ℕ} {N : C}

/-- The image of a boundary cone under a functor. -/
@[simps]
def map (c : BoundaryCone W n N) {D : Type u'} [Category.{v'} D] (G : C ⥤ D) :
    BoundaryCone (W ⋙ G) n (G.obj N) where
  π Δ h θ := G.map (c.π Δ h θ)
  w Δ Δ' h h' α θ := by
    simp only [Functor.comp_map, ← G.map_comp]
    rw [c.w]

/-- Boundary cones in degree `0` are unique (there is nothing to specify). -/
lemma eq_of_zero (c d : BoundaryCone W 0 N) : c = d :=
  ext' fun _ hΔ _ ↦ absurd hΔ (Nat.not_lt_zero _)

/-- A map `Δ ⟶ ⦋n + 1⦌` factoring through a face `δ j` is not an epimorphism. -/
lemma _root_.SimplexCategory.not_epi_comp_δ {n : ℕ} {Δ : SimplexCategory} (a : Δ ⟶ ⦋n⦌)
    (j : Fin (n + 2)) : ¬ Epi (a ≫ SimplexCategory.δ j) := fun h ↦ by
  have := epi_of_epi a (SimplexCategory.δ j)
  have := SimplexCategory.len_le_of_epi (SimplexCategory.δ j)
  simp at this

/-- The pullback of a face of a boundary cone along `a` is given by `descApp`. -/
lemma π_δ_comp_map {n : ℕ} (c : BoundaryCone W (n + 1) N) {Δ : SimplexCategory}
    (a : Δ ⟶ ⦋n⦌) (j : Fin (n + 2)) (hs : ¬ Epi (a ≫ SimplexCategory.δ j)) :
    c.π ⦋n⦌ (by simp) (SimplexCategory.δ j) ≫ W.map a.op = c.descApp _ hs := by
  have hlt : (image a).len < n + 1 :=
    Nat.lt_succ_of_le (SimplexCategory.len_le_of_mono (image.ι a))
  rw [c.descApp_eq hs (e := factorThruImage a) (i := image.ι a ≫ SimplexCategory.δ j)
    (image.fac_assoc _ _)]
  conv_lhs => rw [← image.fac a]
  rw [op_comp, W.map_comp, ← Category.assoc, c.w ⦋n⦌ (image a) (by simp) hlt]

/-- The faces of a boundary cone of degree `n + 1` form a boundary family. -/
lemma isBoundaryFamily_faces {n : ℕ} (c : BoundaryCone W (n + 1) N) :
    W.IsBoundaryFamily (fun j : Fin (n + 2) ↦ c.π ⦋n⦌ (by simp) (SimplexCategory.δ j)) := by
  intro Δ a b j k h
  rw [c.π_δ_comp_map a j (SimplexCategory.not_epi_comp_δ a j),
    c.π_δ_comp_map b k (SimplexCategory.not_epi_comp_δ b k)]
  congr 1

/-- Two boundary cones of degree `n + 1` with the same faces are equal. -/
lemma ext_of_faces {n : ℕ} {c d : BoundaryCone W (n + 1) N}
    (h : ∀ j : Fin (n + 2), c.π ⦋n⦌ (by simp) (SimplexCategory.δ j) =
      d.π ⦋n⦌ (by simp) (SimplexCategory.δ j)) : c = d := by
  refine ext' fun Δ hΔ θ ↦ ?_
  obtain ⟨i, θ', rfl⟩ := SimplexCategory.exists_eq_comp_δ_of_len_lt hΔ θ
  rw [← c.w ⦋n⦌ Δ (by simp) hΔ θ' (SimplexCategory.δ i),
    ← d.w ⦋n⦌ Δ (by simp) hΔ θ' (SimplexCategory.δ i), h]

/-- The boundary cone of degree `n + 1` determined by a boundary family of faces. -/
def ofFaces {n : ℕ} (x : Fin (n + 2) → (N ⟶ W _⦋n⦌)) (hx : W.IsBoundaryFamily x) :
    BoundaryCone W (n + 1) N where
  π := (W.exists_boundary_extension x hx).choose
  w := (W.exists_boundary_extension x hx).choose_spec.1

@[simp]
lemma ofFaces_π_δ {n : ℕ} (x : Fin (n + 2) → (N ⟶ W _⦋n⦌)) (hx : W.IsBoundaryFamily x)
    (j : Fin (n + 2)) : (ofFaces x hx).π ⦋n⦌ (by simp) (SimplexCategory.δ j) = x j :=
  (W.exists_boundary_extension x hx).choose_spec.2 j

end BoundaryCone

/-- A boundary cone `c` on `M` is a *matching cone* if every boundary cone factors uniquely
through it. -/
def IsMatchingCone (W : SimplicialObject C) (n : ℕ) {M : C} (c : BoundaryCone W n M) :
    Prop :=
  ∀ (T : C) (p : BoundaryCone W n T), ∃! f : T ⟶ M, c.precomp f = p

namespace IsMatchingCone

variable {W : SimplicialObject C} {n : ℕ} {M : C} {c : BoundaryCone W n M}

/-- The factorisation of a boundary cone through a matching cone. -/
def lift (hc : IsMatchingCone W n c) {T : C} (p : BoundaryCone W n T) : T ⟶ M :=
  (hc T p).exists.choose

@[simp]
lemma precomp_lift (hc : IsMatchingCone W n c) {T : C} (p : BoundaryCone W n T) :
    c.precomp (hc.lift p) = p :=
  (hc T p).exists.choose_spec

lemma hom_ext (hc : IsMatchingCone W n c) {T : C} {f g : T ⟶ M}
    (h : c.precomp f = c.precomp g) : f = g :=
  (hc T (c.precomp g)).unique h rfl

lemma eq_lift (hc : IsMatchingCone W n c) {T : C} {p : BoundaryCone W n T} {f : T ⟶ M}
    (h : c.precomp f = p) : f = hc.lift p :=
  hc.hom_ext (by rw [h, precomp_lift])

/-- Matching cones can be transported along maps of simplicial objects which are isomorphisms
in degrees `< n`. -/
theorem postcomp {W' : SimplicialObject C} (f : W ⟶ W')
    (hf : ∀ k : SimplexCategory, k.len < n → IsIso (f.app (op k)))
    (hc : IsMatchingCone W n c) : IsMatchingCone W' n (c.postcomp f) := by
  intro T p
  let q : BoundaryCone W n T :=
    { π Δ h θ := p.π Δ h θ ≫ @inv _ _ _ _ (f.app (op Δ)) (hf Δ h)
      w Δ Δ' h h' α θ := by
        have := hf Δ h
        have := hf Δ' h'
        rw [Category.assoc, ← p.w Δ Δ' h h' α θ, Category.assoc]
        congr 1
        rw [IsIso.inv_comp_eq, ← f.naturality_assoc, IsIso.hom_inv_id, Category.comp_id] }
  refine ⟨hc.lift q, ?_, fun g hg ↦ hc.eq_lift ?_⟩
  · refine BoundaryCone.ext' fun Δ h θ ↦ ?_
    have := hf Δ h
    have hq : hc.lift q ≫ c.π Δ h θ = p.π Δ h θ ≫ inv (f.app (op Δ)) :=
      congrArg (fun d ↦ d.π Δ h θ) (hc.precomp_lift q)
    rw [BoundaryCone.precomp_π, BoundaryCone.postcomp_π, ← Category.assoc, hq,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · refine BoundaryCone.ext' fun Δ h θ ↦ ?_
    have := hf Δ h
    have hg' := congrArg (fun d ↦ d.π Δ h θ) hg
    simp only [BoundaryCone.precomp_π, BoundaryCone.postcomp_π] at hg'
    dsimp only [q]
    rw [BoundaryCone.precomp_π, ← hg', Category.assoc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]

end IsMatchingCone

section Criteria

variable {W : SimplicialObject C} {M : C}

/-- A boundary cone of degree `n + 1` is a matching cone if boundary families of faces factor
uniquely through its faces. -/
lemma isMatchingCone_of_faces {n : ℕ} (c : BoundaryCone W (n + 1) M)
    (h : ∀ (T : C) (x : Fin (n + 2) → (T ⟶ W _⦋n⦌)), W.IsBoundaryFamily x →
      ∃! f : T ⟶ M, ∀ j, f ≫ c.π ⦋n⦌ (by simp) (SimplexCategory.δ j) = x j) :
    IsMatchingCone W (n + 1) c := by
  intro T p
  obtain ⟨f, hf, hu⟩ := h T _ p.isBoundaryFamily_faces
  refine ⟨f, BoundaryCone.ext_of_faces fun j ↦ ?_, fun g hg ↦ hu g fun j ↦ ?_⟩
  · rw [BoundaryCone.precomp_π, hf]
  · rw [← hg, BoundaryCone.precomp_π]

/-- A boundary cone of degree `0` on a terminal object is a matching cone. -/
lemma isMatchingCone_of_isTerminal (c : BoundaryCone W 0 M) (hM : IsTerminal M) :
    IsMatchingCone W 0 c :=
  fun T _ ↦ ⟨hM.from T, BoundaryCone.eq_of_zero _ _, fun _ _ ↦ hM.hom_ext _ _⟩

/-- A boundary cone of degree `1` whose two faces form a product is a matching cone. -/
lemma isMatchingCone_of_isLimit_fan (c : BoundaryCone W 1 M) {x : Fin 2 → (M ⟶ W _⦋0⦌)}
    (hx : IsLimit (Fan.mk M x)) (hc : ∀ j, c.π ⦋0⦌ (by simp) (SimplexCategory.δ j) = x j) :
    IsMatchingCone W 1 c := by
  refine isMatchingCone_of_faces (n := 0) c fun T y _ ↦
    ⟨Fan.IsLimit.lift hx y, fun j ↦ ?_, fun g hg ↦ Fan.IsLimit.hom_ext hx _ _ fun j ↦ ?_⟩
  · rw [hc]
    exact Fan.IsLimit.fac hx y j
  · rw [Fan.IsLimit.fac, ← hg j, hc j]
    rfl

/-- For `a < b`, the simplicial identity `δ (b - 1) ≫ δ a = δ a ≫ δ b`. -/
lemma _root_.SimplexCategory.δ_pred_comp_δ_of_lt {n : ℕ} {a b : Fin (n + 3)} (h : a < b) :
    SimplexCategory.δ (b.pred (Fin.ne_zero_of_lt h)) ≫ SimplexCategory.δ a =
      SimplexCategory.δ (a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt))) ≫
        SimplexCategory.δ b := by
  have H : a.castLT (Nat.lt_of_lt_of_le h (Nat.le_of_lt_succ b.isLt)) ≤
      b.pred (Fin.ne_zero_of_lt h) := by
    rw [Fin.le_iff_val_le_val]
    have h' : a.val < b.val := h
    simp only [Fin.val_castLT, Fin.val_pred]
    omega
  have := SimplexCategory.δ_comp_δ H
  rw [Fin.succ_pred, Fin.castSucc_castLT] at this
  exact this.symm

/-- A boundary cone of degree `n + 2` whose faces form a multiequalizer of the face maps is a
matching cone. -/
lemma isMatchingCone_of_isLimit_multifork {n : ℕ} {K : Multifork (matchingBoundaryIndex W n)}
    (hK : IsLimit K) (c : BoundaryCone W (n + 2) K.pt)
    (hc : ∀ j, c.π ⦋n + 1⦌ (by simp) (SimplexCategory.δ j) = K.ι j) :
    IsMatchingCone W (n + 2) c := by
  refine isMatchingCone_of_faces (n := n + 1) c fun T x hx ↦
    ⟨Multifork.IsLimit.lift hK x ?_, fun j ↦ ?_, fun g hg ↦
      Multifork.IsLimit.hom_ext hK fun j ↦ ?_⟩
  · rintro ⟨⟨a, b⟩, h⟩
    exact hx _ _ _ _ _ (SimplexCategory.δ_pred_comp_δ_of_lt h)
  · rw [hc]
    exact Multifork.IsLimit.fac hK x _ j
  · rw [Multifork.IsLimit.fac, ← hg j, hc j]

end Criteria

section MatchingObj

variable [HasFiniteLimits C]

instance (W : SimplicialObject C) (n : ℕ) :
    HasMultiequalizer (matchingBoundaryIndex W n) := by
  have : Fintype (matchingBoundaryShape n).L :=
    inferInstanceAs (Fintype (Fin (n + 3)))
  have : Fintype (matchingBoundaryShape n).R :=
    inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  have : DecidableEq (matchingBoundaryShape n).L :=
    inferInstanceAs (DecidableEq (Fin (n + 3)))
  have : DecidableEq (matchingBoundaryShape n).R :=
    inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  infer_instance

/-- The `n`-th matching object of a simplicial object in a category with finite limits. -/
def matchingObj (W : SimplicialObject C) : ℕ → C
  | 0 => ⊤_ C
  | 1 => ∏ᶜ fun _ : Fin 2 ↦ W _⦋0⦌
  | n + 2 => multiequalizer (matchingBoundaryIndex W n)

/-- The universal boundary cone on the `n`-th matching object. -/
def matchingObjCone (W : SimplicialObject C) : ∀ n : ℕ, BoundaryCone W n (matchingObj W n)
  | 0 => ⟨fun _ h _ ↦ absurd h (Nat.not_lt_zero _), fun _ _ h ↦ absurd h (Nat.not_lt_zero _)⟩
  | 1 => BoundaryCone.ofFaces (n := 0) (fun j ↦ Pi.π (fun _ : Fin 2 ↦ W _⦋0⦌) j)
      (W.isBoundaryFamily_zero _)
  | n + 2 => BoundaryCone.ofFaces (n := n + 1) (Multiequalizer.ι (matchingBoundaryIndex W n))
      (W.isBoundaryFamily_succ _ fun i j hij ↦ by
        have := Multiequalizer.condition (matchingBoundaryIndex W n)
          ⟨(i.castSucc, j.succ), Fin.castSucc_lt_succ_iff.2 hij⟩
        dsimp [matchingBoundaryIndex, matchingBoundaryShape] at this
        exact this.symm)

@[simp]
lemma matchingObjCone_one_π_δ (W : SimplicialObject C) (j : Fin 2) :
    (matchingObjCone W 1).π ⦋0⦌ (by simp) (SimplexCategory.δ j) =
      Pi.π (fun _ : Fin 2 ↦ W _⦋0⦌) j := by
  rw [matchingObjCone]
  exact BoundaryCone.ofFaces_π_δ (n := 0) _ _ j

@[simp]
lemma matchingObjCone_succ_succ_π_δ (W : SimplicialObject C) (n : ℕ) (j : Fin (n + 3)) :
    (matchingObjCone W (n + 2)).π ⦋n + 1⦌ (by simp) (SimplexCategory.δ j) =
      Multiequalizer.ι (matchingBoundaryIndex W n) j := by
  rw [matchingObjCone]
  exact BoundaryCone.ofFaces_π_δ (n := n + 1) _ _ j

instance (n : ℕ) : FinCategory (WalkingMulticospan (matchingBoundaryShape n)) := by
  have : Fintype (matchingBoundaryShape n).L :=
    inferInstanceAs (Fintype (Fin (n + 3)))
  have : Fintype (matchingBoundaryShape n).R :=
    inferInstanceAs (Fintype {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  have : DecidableEq (matchingBoundaryShape n).L :=
    inferInstanceAs (DecidableEq (Fin (n + 3)))
  have : DecidableEq (matchingBoundaryShape n).R :=
    inferInstanceAs (DecidableEq {p : Fin (n + 3) × Fin (n + 3) // p.1 < p.2})
  infer_instance

theorem isMatchingCone_matchingObjCone (W : SimplicialObject C) (n : ℕ) :
    IsMatchingCone W n (matchingObjCone W n) :=
  match n with
  | 0 => isMatchingCone_of_isTerminal _ terminalIsTerminal
  | 1 => isMatchingCone_of_isLimit_fan _ (productIsProduct _) (matchingObjCone_one_π_δ W)
  | n + 2 => isMatchingCone_of_isLimit_multifork (limit.isLimit _) _
      (matchingObjCone_succ_succ_π_δ W n)

/-- Functors preserving finite limits preserve the matching objects. -/
theorem isMatchingCone_map_matchingObjCone {D : Type u'} [Category.{v'} D]
    (G : C ⥤ D) [PreservesFiniteLimits G] (W : SimplicialObject C) (n : ℕ) :
    IsMatchingCone (W ⋙ G) n ((matchingObjCone W n).map G) :=
  match n with
  | 0 => isMatchingCone_of_isTerminal _ (terminalIsTerminal.isTerminalObj G _)
  | 1 => isMatchingCone_of_isLimit_fan _ (isLimitOfHasProductOfPreservesLimit G _)
      fun j ↦ by rw [BoundaryCone.map_π, matchingObjCone_one_π_δ]
  | n + 2 => isMatchingCone_of_isLimit_multifork (W := W ⋙ G) (n := n)
      (K := (Multiequalizer.multifork (matchingBoundaryIndex W n)).map G)
      (Multifork.isLimitMapOfPreserves _ G (limit.isLimit _)) _
      fun j ↦ by
        rw [BoundaryCone.map_π, matchingObjCone_succ_succ_π_δ]
        rfl

end MatchingObj

end CategoryTheory.SimplicialObject
