/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationStepRetraction
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationCokernelEven
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationCokernelOdd

/-!
# Splittings and free quotients of the alternating column filtration

## References

* Stacks Project, Tag 09KP, filtration construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.TotalFreeFiltration

variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- The explicitly constructed stage inclusions split degreewise, and their
cokernels are coproducts of single-degree copies of the ring. -/
theorem quotients
    (h_exact : ∀ j, (S j).ShortExact)
    (h_split : ∀ j (k : ℤ), Nonempty
      ((S j).map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting)
    (h_free : ∀ j, ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
      Nonempty ((S j).X₁ ≅ ∐ (fun i : I₁ ↦
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
          (ModuleCat.of A A))) ∧ Nonempty ((S j).X₃ ≅ ∐ (fun i : I₃ ↦
        (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
          (ModuleCat.of A A)))) :
    (∀ (n : ℕ) (k : ℤ),
      ∃ r : (complex K S e h_positive (n + 1)).X k ⟶
        (complex K S e h_positive n).X k,
        (step K S e h_positive n).f k ≫ r =
          𝟙 ((complex K S e h_positive n).X k)) ∧
    (∀ n, ∃ (I : Type u) (degree : I → ℤ), Nonempty
      (cokernel (step K S e h_positive n) ≅
        ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
          (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of A A)))) := by
  constructor
  · exact step_retraction K S e h_positive h_split
  · intro n
    obtain ⟨I₁, I₃, d₁, d₃, h₁, h₃⟩ := h_free (n / 2)
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hn : n = 2 * (n / 2) := by omega
      refine ⟨I₁, fun i ↦ d₁ i - (n / 2 : ℕ), ?_⟩
      have hc := cokernel_even K S e h_positive h_exact (n / 2) I₁ d₁ h₁
      rw [← hn] at hc
      exact hc
    · have hn : n = 2 * (n / 2) + 1 := by omega
      refine ⟨I₃, fun i ↦ d₃ i - (n / 2 : ℕ), ?_⟩
      have hc := cokernel_odd K S e h_positive h_exact (n / 2) I₃ d₃ h₃
      rw [← hn] at hc
      exact hc

end CochainComplex.TotalFreeFiltration
