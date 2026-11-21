/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationExhaustive
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationQuotients

/-!
# A free filtration on a direct-sum total complex

## References

* Stacks Project, Tag 09KP, construction of the filtration of the total complex.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- The total complex of nonpositive columns with split free two-step filtrations
has an exhaustive, degreewise split filtration with free zero-differential quotients. -/
theorem exists_totalFreeFiltration {A : Type u} [CommRing A]
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_columns : ∀ p : ℤ, p ≤ 0 →
      ∃ S : ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ),
        Nonempty (S.X₂ ≅ K.X p) ∧ S.ShortExact ∧
        (∀ k : ℤ,
          Nonempty
            (S.map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting) ∧
        ∃ (I₁ I₃ : Type u) (d₁ : I₁ → ℤ) (d₃ : I₃ → ℤ),
          Nonempty (S.X₁ ≅ ∐ (fun i : I₁ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₁ i)).obj
              (ModuleCat.of A A))) ∧
          Nonempty (S.X₃ ≅ ∐ (fun i : I₃ ↦
            (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (d₃ i)).obj
              (ModuleCat.of A A)))) :
      ∃ (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ)
        (ι : ∀ n, F n ⟶ K.total (ComplexShape.up ℤ)) (step : ∀ n, F n ⟶ F (n + 1)),
        IsZero (F 0) ∧
        (∀ n, Mono (ι n)) ∧
        (∀ n, step n ≫ ι (n + 1) = ι n) ∧
        (∀ (k : ℤ) (x : (K.total (ComplexShape.up ℤ)).X k),
          ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x) ∧
        (∀ (n : ℕ) (k : ℤ),
          ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
            (step n).f k ≫ r = 𝟙 ((F n).X k)) ∧
      (∀ n, ∃ (I : Type u) (degree : I → ℤ),
          Nonempty (cokernel (step n) ≅
            ∐ (fun i : I ↦
              (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) (degree i)).obj
                (ModuleCat.of A A)))) := by
  classical
  have hc (j : ℕ) := h_columns (-(j : ℤ)) (by omega)
  choose S he h_exact h_split h_free using hc
  let e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)) := fun j ↦ (he j).some
  let F := TotalFreeFiltration.complex K S e h_positive
  let ι := TotalFreeFiltration.inclusion K S e h_positive
  let step := TotalFreeFiltration.step K S e h_positive
  obtain ⟨hretract, hcoker⟩ :=
    TotalFreeFiltration.quotients K S e h_positive h_exact h_split h_free
  refine ⟨F, ι, step, ?_, ?_, ?_, ?_, hretract, hcoker⟩
  · exact TotalFreeFiltration.restrict_zero _ _ _
      (TotalFreeFiltration.term_zero K S e)
  · intro n
    exact TotalFreeFiltration.restrict_mono _ _ _
  · intro n
    exact TotalFreeFiltration.restrict_comp _ _ _ _ _ _
  · exact TotalFreeFiltration.restrict_surjective _ _ _
      (TotalFreeFiltration.exhaustive K S e h_positive)

end CochainComplex
