/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Sheaf.Algebra.Homology.TotalFreeFiltrationTerms

/-!
# Degreewise retractions of the alternating column filtration

Source: Stacks Project, Tag 09KP, filtration construction.
(blueprint: lem-pc-derived-total-filtration-step-retraction)
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

/-- Each filtration inclusion has a left inverse in each degree.
Source: Stacks Project, Tag 09KP, alternating column filtration.
(blueprint: lem-pc-derived-total-filtration-step-retraction)

Proof. Decompose the total module in degree k as the coproduct of its column
terms. At stage 2j the submodule is the sum of full columns -i for i<j;
at stage 2j+1 it also includes the image of the first arrow of S j.
Projection onto the preceding full columns retracts the even inclusion.
For the odd inclusion, project onto the preceding columns and apply the
retraction of the first arrow supplied by the splitting of S j in degree k+j,
transported through e j. Directness of the column summands proves that these
maps restrict to the indicated submodules and compose with the inclusions to
identity. Every n is even or odd. For j=0 the preceding sum is zero, so the
same constructions apply. No exactness or freeness hypothesis is needed. -/
theorem step_retraction
    (h_split : ∀ j (k : ℤ), Nonempty
      ((S j).map (HomologicalComplex.eval (ModuleCat.{u} A) (ComplexShape.up ℤ) k)).Splitting)
    (n : ℕ) (k : ℤ) :
    ∃ r : (complex K S e h_positive (n + 1)).X k ⟶
      (complex K S e h_positive n).X k,
      (step K S e h_positive n).f k ≫ r =
        𝟙 ((complex K S e h_positive n).X k) := by sorry

end CochainComplex.TotalFreeFiltration
