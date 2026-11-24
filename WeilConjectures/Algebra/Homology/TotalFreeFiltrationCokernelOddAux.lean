/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.TotalFreeFiltrationTerms
import WeilConjectures.Algebra.Homology.TotalFreeFiltrationOddQuotientBijective
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# The odd filtration quotient with a specified free endpoint

## References

* Stacks Project, Tag 09KP.
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

/-- Core odd filtration quotient calculation, with a specified endpoint isomorphism. -/
theorem cokernel_odd_core
    (h_exact : ∀ j, (S j).ShortExact)
    (j : ℕ) (I : Type u) (degree : I → ℤ)
    (h_endpoint : (S j).X₃ ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of A A))) :
    Nonempty (cokernel (step K S e h_positive (2 * j + 1)) ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i - (j : ℤ))).obj (ModuleCat.of A A))) := by
  classical
  let q := oddQuotientMap K S e h_positive h_exact j
  have (k : ℤ) : IsIso (q.f k) :=
    (ConcreteCategory.isIso_iff_bijective (q.f k)).mpr
      (oddQuotientMap_bijective K S e h_positive h_exact j k)
  have : IsIso q := HomologicalComplex.Hom.isIso_of_components q
  let F := CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (j : ℤ)
  exact ⟨(asIso q).symm ≪≫ F.mapIso h_endpoint ≪≫
    PreservesCoproduct.iso F _ ≪≫ Sigma.mapIso (fun i ↦
      ((CochainComplex.singleFunctors (ModuleCat.{u} A)).shiftIso
        (j : ℤ) (degree i - (j : ℤ)) (degree i) (by omega)).app (ModuleCat.of A A))⟩

end CochainComplex.TotalFreeFiltration
