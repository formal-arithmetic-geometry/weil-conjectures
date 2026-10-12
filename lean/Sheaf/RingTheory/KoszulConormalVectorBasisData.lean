module

public import Sheaf.RingTheory.KoszulConormalComparison
public import Sheaf.RingTheory.KoszulRegularSequence

/-! Auxiliary linear independence and spanning result for conormal generators.
(blueprint: lem-sc-koszul-conormal-basis-data)
-/

@[expose] public section

universe u

namespace ExteriorAlgebra

/-- The conormal classes of a Koszul-regular generating sequence are linearly
independent and span the cotangent module.

Source: Stacks Project, More on Algebra, Tag 062I, first paragraph of the proof.
The proof identifies the cotangent module with the cokernel of the second
Koszul differential after tensoring with `A ⧸ I`; regularity makes the kernel
of the generator map equal to that image, while every coefficient of that
differential lies in `I`, so the induced map has zero source differential.
(blueprint: lem-sc-koszul-conormal-basis-data)
-/
theorem koszulConormalVector_linearIndependent_and_span
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (hf : Ideal.span (Set.range f) = I) :
    LinearIndependent (A ⧸ I)
        (fun i => koszulConormalVector A I r f hf (Finsupp.single i 1)) ∧
      ⊤ ≤ Submodule.span (A ⧸ I)
        (Set.range (fun i => koszulConormalVector A I r f hf (Finsupp.single i 1))) := by
  sorry

end ExteriorAlgebra
