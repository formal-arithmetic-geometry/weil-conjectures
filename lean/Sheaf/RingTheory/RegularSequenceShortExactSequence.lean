/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences and short exact sequences

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0F1T
(blueprint: lem-weil-pbc-regular-sequence-short-exact-sequence).
-/

@[expose] public section

universe u v₁ v₂ v₃

namespace RingTheory.Sequence

/-- (blueprint: lem-weil-pbc-regular-sequence-short-exact-sequence) Let `R` be a
commutative ring, let `0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of
`R`-modules, and let `f` be a finite sequence in `R`. If every entry is a
nonzerodivisor on the corresponding quotients of `M₁` and `M₃`, then it is a
nonzerodivisor on the corresponding quotients of `M₂`, and all induced
quotient sequences are exact; consequently regularity on the two outer terms
implies regularity on the middle term.

Source: Stacks Project, Algebra, Tag 0F1T.

Proof:
1. Construct the induced maps with `Submodule.mapQ`; their values on representatives
   are definitionally the classes of `α x` and `β x`.
2. Use the snake-lemma consequence
   `map_first_exact_on_four_term_right_exact_of_isSMulRegular_last` on
   `0 → M₁ → M₂ → M₃ → 0`. Weak regularity on `M₃` gives injectivity of the
   first quotient map. Applying the same result to `M₁ → M₂ → M₃ → 0 → 0`
   gives exactness at the middle quotient, since every sequence is weakly
   regular on the zero module. Surjectivity follows by lifting representatives.
   This reuses Mathlib's induction instead of constructing a snake diagram.
3. Weak regularity of `f` on `M₃` restricts to every prefix, by the append
   characterization. Apply Step 2 to each prefix, then apply
   `isSMulRegular_of_range_eq_ker` to its short exact row and the two outer
   scalar regularity hypotheses. This proves part (a).
4. For part (b), apply part (a) to the weak regularity of both outer terms.
   If `M₂ = (f)M₂`, applying the surjection `β` gives `M₃ = (f)M₃`, contrary
   to `IsRegular.top_ne_smul` on `M₃`. -/
theorem isRegular_of_shortExact
    (R : Type u) [CommRing R]
    (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (α : M₁ →ₗ[R] M₂) (β : M₂ →ₗ[R] M₃)
    (hα : Function.Injective α) (hβ : Function.Surjective β)
    (hex : Function.Exact α β)
    (f : List R) :
    (((∀ (i : Fin f.length) (x : M₁ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁))),
        f.get i • x = 0 → x = 0) ∧
      ∀ (i : Fin f.length) (x : M₃ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₃))),
        f.get i • x = 0 → x = 0) →
      (∀ (i : Fin f.length) (x : M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂))),
          f.get i • x = 0 → x = 0) ∧
      ∀ (i : Fin (f.length + 1)),
        ∃ (a : M₁ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁)) →ₗ[R]
              M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)))
          (b : M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)) →ₗ[R]
              M₃ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₃))),
          Function.Exact a b ∧ Function.Injective a ∧ Function.Surjective b ∧
          (∀ x : M₁, a (((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁)).mkQ x) =
            ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)).mkQ (α x))) ∧
          (∀ x : M₂, b (((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)).mkQ x) =
            ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₃)).mkQ (β x)))) ∧
      ((IsRegular M₁ f ∧ IsRegular M₃ f) → IsRegular M₂ f) := by
  -- Quotient rows only require weak regularity on the right.
  have rows (rs : List R) (h₃ : IsWeaklyRegular M₃ rs) :
      ∃ (a : M₁ ⧸ (Ideal.ofList rs • (⊤ : Submodule R M₁)) →ₗ[R]
            M₂ ⧸ (Ideal.ofList rs • (⊤ : Submodule R M₂)))
        (b : M₂ ⧸ (Ideal.ofList rs • (⊤ : Submodule R M₂)) →ₗ[R]
            M₃ ⧸ (Ideal.ofList rs • (⊤ : Submodule R M₃))),
        Function.Exact a b ∧ Function.Injective a ∧ Function.Surjective b ∧
        (∀ x : M₁, a ((Ideal.ofList rs • (⊤ : Submodule R M₁)).mkQ x) =
          (Ideal.ofList rs • (⊤ : Submodule R M₂)).mkQ (α x)) ∧
        (∀ x : M₂, b ((Ideal.ofList rs • (⊤ : Submodule R M₂)).mkQ x) =
          (Ideal.ofList rs • (⊤ : Submodule R M₃)).mkQ (β x)) := by
    let a := Submodule.mapQ _ _ α (Submodule.smul_top_le_comap_smul_top
      (Ideal.ofList rs) α)
    let b := Submodule.mapQ _ _ β (Submodule.smul_top_le_comap_smul_top
      (Ideal.ofList rs) β)
    have hzero : IsWeaklyRegular PUnit.{1} rs :=
      ⟨fun _ _ => Function.injective_of_subsingleton _⟩
    -- Append the zero module to obtain exactness at the middle quotient.
    have hab : Function.Exact a b :=
      map_first_exact_on_four_term_right_exact_of_isSMulRegular_last hex
        ((LinearMap.exact_zero_iff_surjective PUnit.{1} β).mpr hβ)
        (show Function.Surjective (0 : M₃ →ₗ[R] PUnit.{1}) from
          fun _ => ⟨0, Subsingleton.elim _ _⟩) hzero
    -- Prepend a zero map to obtain injectivity at the left quotient.
    have ha : Function.Injective a := by
      have H := map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
        ((LinearMap.exact_zero_iff_injective M₁ α).mpr hα) hex hβ h₃
      simpa only [Submodule.mapQ_zero, LinearMap.exact_zero_iff_injective] using H
    have hb : Function.Surjective b := by
      intro y
      obtain ⟨y, rfl⟩ := (Ideal.ofList rs • (⊤ : Submodule R M₃)).mkQ_surjective y
      obtain ⟨x, rfl⟩ := hβ y
      exact ⟨(Ideal.ofList rs • (⊤ : Submodule R M₂)).mkQ x, rfl⟩
    exact ⟨a, b, hab, ha, hb, fun _ => rfl, fun _ => rfl⟩
  have partA :
      ((∀ (i : Fin f.length) (x : M₁ ⧸
          (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₁))),
          f.get i • x = 0 → x = 0) ∧
        ∀ (i : Fin f.length) (x : M₃ ⧸
          (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₃))),
          f.get i • x = 0 → x = 0) →
      (∀ (i : Fin f.length) (x : M₂ ⧸
          (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂))),
          f.get i • x = 0 → x = 0) ∧
      ∀ (i : Fin (f.length + 1)),
        ∃ (a : M₁ ⧸ (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₁)) →ₗ[R]
              M₂ ⧸ (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)))
          (b : M₂ ⧸ (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)) →ₗ[R]
              M₃ ⧸ (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₃))),
          Function.Exact a b ∧ Function.Injective a ∧ Function.Surjective b ∧
          (∀ x : M₁, a ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₁)).mkQ x) =
            (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)).mkQ (α x)) ∧
          (∀ x : M₂, b ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)).mkQ x) =
            (Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₃)).mkQ (β x)) := by
    rintro ⟨h₁, h₃⟩
    have reg₃ : IsWeaklyRegular M₃ f := (isWeaklyRegular_iff_Fin M₃ f).mpr
      fun i => (isSMulRegular_iff_right_eq_zero_of_smul).mpr (h₃ i)
    have hrows (n : ℕ) := rows (f.take n)
      ((isWeaklyRegular_append_iff M₃ (f.take n) (f.drop n)).mp
        (by simpa only [List.take_append_drop] using reg₃)).1
    refine ⟨?_, fun i => hrows i.1⟩
    intro i
    obtain ⟨a, b, hab, ha, _, _, _⟩ := hrows i.1
    exact (isSMulRegular_iff_right_eq_zero_of_smul).mp
      (isSMulRegular_of_range_eq_ker ha hab.linearMap_ker_eq.symm
        ((isSMulRegular_iff_right_eq_zero_of_smul).mpr (h₁ i))
        ((isSMulRegular_iff_right_eq_zero_of_smul).mpr (h₃ i)))
  refine ⟨partA, ?_⟩
  rintro ⟨h₁, h₃⟩
  have hm := (partA ⟨fun i =>
      (isSMulRegular_iff_right_eq_zero_of_smul).mp
        ((isWeaklyRegular_iff_Fin M₁ f).mp h₁.toIsWeaklyRegular i), fun i =>
      (isSMulRegular_iff_right_eq_zero_of_smul).mp
        ((isWeaklyRegular_iff_Fin M₃ f).mp h₃.toIsWeaklyRegular i)⟩).1
  refine ⟨(isWeaklyRegular_iff_Fin M₂ f).mpr (fun i =>
    (isSMulRegular_iff_right_eq_zero_of_smul).mpr (hm i)), ?_⟩
  intro heq
  apply h₃.top_ne_smul
  have H := congrArg (Submodule.map β) heq
  simpa only [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hβ] using H

end RingTheory.Sequence
