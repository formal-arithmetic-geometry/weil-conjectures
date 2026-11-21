/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationCokernelOddAux

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

/-- The odd successive quotient has the prescribed endpoint basis in shifted degrees. -/
theorem cokernel_odd
    (h_exact : ∀ j, (S j).ShortExact)
    (j : ℕ) (I : Type u) (degree : I → ℤ)
    (h_endpoint : Nonempty ((S j).X₃ ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of A A)))) :
    Nonempty (cokernel (step K S e h_positive (2 * j + 1)) ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i - (j : ℤ))).obj (ModuleCat.of A A))) := by
  rcases h_endpoint with ⟨h_endpoint⟩
  exact cokernel_odd_core K S e h_positive h_exact j I degree h_endpoint

end CochainComplex.TotalFreeFiltration
