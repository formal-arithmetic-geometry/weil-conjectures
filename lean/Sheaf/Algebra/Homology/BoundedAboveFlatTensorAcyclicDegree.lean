module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Homology.KFlat
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits

namespace CochainComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}

/-- The bounded-above flat tensor argument vanishes in one fixed degree.
The proof is the finite truncation and first-quadrant spectral-sequence argument
of Stacks Project, Cohomology on Sites, Lemma 21.17.8 (Tag 06YQ).
(blueprint: lem-pc-bounded-above-flat-tensor-acyclic-degree)

Proof: truncate both bounded-above complexes to the finite range affecting degree n,
translate to a first-quadrant double complex, and use the convergent spectral sequence.
Flatness makes every column acyclic, so the E1 page and the finite filtration vanish. -/
theorem isZero_homology_mapBifunctor_of_boundedAbove_flat_sheaf
    (A P : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (hAbounded : ∃ a : ℤ, ∀ i : ℤ, a < i → IsZero (A.X i))
    (hPbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (P.X i))
    (hPflat : ∀ i : ℤ, SheafOfModules.IsFlat (P.X i))
    (hA : A.Acyclic) (n : ℤ) :
    (letI := SheafOfModules.monoidalCategory R
     HomologicalComplex.ExactAt (mapBifunctor A P (curriedTensor _)) n) := by
  sorry

end CochainComplex
