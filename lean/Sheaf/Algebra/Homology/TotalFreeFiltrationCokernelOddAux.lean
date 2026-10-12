module

public import Sheaf.Algebra.Homology.TotalFreeFiltrationTerms

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex.TotalFreeFiltration
variable {A : Type u} [CommRing A]
variable (K : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
variable (S : ℕ → ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ))
variable (e : ∀ j : ℕ, (S j).X₂ ≅ K.X (-(j : ℤ)))
variable (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))

/-- Core odd filtration quotient calculation, with a specified endpoint isomorphism.
Source: Stacks Project, Tag 09KP, proof, alternating two-step column filtration.
(blueprint: lem-pc-derived-total-filtration-cokernel-odd-core)
The degreewise cokernel calculation identifies the quotient with the reindexed
third endpoint; compatibility with the total differential and the universal
property then gives the displayed complex isomorphism. -/
theorem cokernel_odd_core
    (h_exact : ∀ j, (S j).ShortExact)
    (j : ℕ) (I : Type u) (degree : I → ℤ)
    (h_endpoint : (S j).X₃ ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i)).obj (ModuleCat.of A A))) :
    Nonempty (cokernel (step K S e h_positive (2 * j + 1)) ≅
      ∐ (fun i : I ↦ (HomologicalComplex.single (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (degree i - (j : ℤ))).obj (ModuleCat.of A A))) := by
  sorry

end CochainComplex.TotalFreeFiltration
