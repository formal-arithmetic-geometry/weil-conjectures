/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Finite data and finite relations descend in a filtered colimit of rings

Let `c` be a colimit cocone over a filtered diagram `F` of commutative rings. Finitely many
elements `x : σ → c.pt` of the colimit satisfying finitely many polynomial identities
`P l (x) = Q l (x)` (with `P l, Q l : MvPolynomial σ ℤ`) lift to a common stage `F.obj j` such
that the identities already hold there, and hence after every transition `F.obj j ⟶ F.obj k`.

## Main results

- `CommRingCat.exists_map_eq_zero_of_ι_app_eq_zero`: finitely many elements of a stage that
  vanish in the colimit vanish at a later stage.
- `CommRingCat.exists_lift_forall_aeval_eq`: the statement above.
-/

@[expose] public section

universe vJ uJ u

open CategoryTheory Limits

namespace CommRingCat

variable {J : Type uJ} [Category.{vJ} J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}}
  {c : Cocone F} [PreservesColimit F (forget CommRingCat)]

/-- Polynomial expressions over `ℤ` commute with ring homomorphisms. -/
lemma aeval_comp_hom {R S : CommRingCat.{u}} (f : R ⟶ S) {σ : Type*} (y : σ → R)
    (P : MvPolynomial σ ℤ) : MvPolynomial.aeval (fun a ↦ f (y a)) P = f (MvPolynomial.aeval y P) :=
  (MvPolynomial.comp_aeval_apply (f := y) f.hom.toIntAlgHom P).symm

/-- Two elements of a stage of a filtered colimit of rings with the same image in the colimit
agree at a later stage. -/
lemma exists_map_eq_of_ι_app_eq (hc : IsColimit c) {j : J} {a b : F.obj j}
    (h : c.ι.app j a = c.ι.app j b) : ∃ (k : J) (f : j ⟶ k), F.map f a = F.map f b := by
  obtain ⟨k, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc a b h
  refine ⟨IsFiltered.coeq f g, f ≫ IsFiltered.coeqHom f g, ?_⟩
  nth_rw 2 [IsFiltered.coeq_condition f g]
  rw [F.map_comp, F.map_comp, CommRingCat.comp_apply, CommRingCat.comp_apply, hfg]

/-- Finitely many elements of a stage of a filtered colimit of rings that vanish in the colimit
vanish at a common later stage. -/
lemma exists_map_eq_zero_of_ι_app_eq_zero (hc : IsColimit c) {ι : Type*} [Finite ι] {j : J}
    (e : ι → F.obj j) (he : ∀ l, c.ι.app j (e l) = 0) :
    ∃ (k : J) (f : j ⟶ k), ∀ l, F.map f (e l) = 0 := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ s : Finset ι, ∃ (k : J) (f : j ⟶ k), ∀ l ∈ s, F.map f (e l) = 0 by
    obtain ⟨k, f, hf⟩ := H Finset.univ
    exact ⟨k, f, fun l ↦ hf l (Finset.mem_univ l)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨j, 𝟙 j, by simp⟩
  | insert l s _ ih =>
    obtain ⟨k, f, hf⟩ := ih
    obtain ⟨k', g, hg⟩ := exists_map_eq_of_ι_app_eq hc (a := F.map f (e l)) (b := 0) (by
      rw [map_zero, ← CommRingCat.comp_apply, c.w]
      exact he l)
    refine ⟨k', f ≫ g, fun l' hl' ↦ ?_⟩
    rw [F.map_comp, CommRingCat.comp_apply]
    rcases Finset.mem_insert.mp hl' with rfl | hl'
    · rw [hg, map_zero]
    · rw [hf l' hl', map_zero]

/-- Blueprint `lemma-nagata-filtered-colimit-finite-data`: Finite data and finite relations
descend in a filtered colimit.

Let `c` be a colimit of a filtered diagram `F` of commutative rings. Given finitely many
elements `x : σ → c.pt` and finitely many equalities `P l (x) = Q l (x)` between ring
expressions `P l, Q l : MvPolynomial σ ℤ` in them, there is a stage `j` and lifts
`y : σ → F.obj j` of the `x` such that all the equalities hold for `y`, and after every
transition `F.obj j ⟶ F.obj k`. -/
theorem exists_lift_forall_aeval_eq (hc : IsColimit c) {σ ι : Type*} [Finite σ] [Finite ι]
    (x : σ → c.pt) (P Q : ι → MvPolynomial σ ℤ)
    (h : ∀ l, MvPolynomial.aeval x (P l) = MvPolynomial.aeval x (Q l)) :
    ∃ (j : J) (y : σ → F.obj j), (∀ a, c.ι.app j (y a) = x a) ∧
      ∀ (k : J) (f : j ⟶ k) (l : ι), MvPolynomial.aeval (fun a ↦ F.map f (y a)) (P l) =
        MvPolynomial.aeval (fun a ↦ F.map f (y a)) (Q l) := by
  classical
  have := Fintype.ofFinite σ
  -- Lift all the elements to a common stage.
  obtain ⟨j₀, hj₀⟩ := exists_forall_mem_range_ι_app F c hc (Finset.univ.image x)
  choose y₀ hy₀ using fun a ↦ hj₀ (x a) (Finset.mem_image_of_mem x (Finset.mem_univ a))
  obtain rfl : (fun a ↦ c.ι.app j₀ (y₀ a)) = x := funext hy₀
  -- The relations hold in the colimit, hence at a later stage.
  obtain ⟨j, f₀, hf₀⟩ := exists_map_eq_zero_of_ι_app_eq_zero hc
    (fun l ↦ MvPolynomial.aeval y₀ (P l) - MvPolynomial.aeval y₀ (Q l)) (fun l ↦ by
      rw [map_sub, ← aeval_comp_hom, ← aeval_comp_hom, sub_eq_zero]
      exact h l)
  refine ⟨j, fun a ↦ F.map f₀ (y₀ a), fun a ↦ ?_, fun k f l ↦ ?_⟩
  · rw [← CommRingCat.comp_apply, c.w]
    rfl
  · have hcomp : (fun a ↦ F.map f (F.map f₀ (y₀ a))) = fun a ↦ F.map (f₀ ≫ f) (y₀ a) := by
      funext a
      rw [F.map_comp, CommRingCat.comp_apply]
    rw [hcomp, aeval_comp_hom, aeval_comp_hom, F.map_comp, CommRingCat.comp_apply,
      CommRingCat.comp_apply, ← sub_eq_zero, ← map_sub, ← map_sub, hf₀ l, map_zero]

omit [IsFiltered J] [PreservesColimit F (forget CommRingCat)] in
/-- Polynomial identities between elements of a stage persist along every transition. -/
lemma aeval_map_eq_of_aeval_eq {σ : Type*} {j k : J} (f : j ⟶ k) (y : σ → F.obj j)
    {P Q : MvPolynomial σ ℤ} (h : MvPolynomial.aeval y P = MvPolynomial.aeval y Q) :
    MvPolynomial.aeval (fun a ↦ F.map f (y a)) P = MvPolynomial.aeval (fun a ↦ F.map f (y a)) Q :=
  by rw [aeval_comp_hom, aeval_comp_hom, h]

end CommRingCat
