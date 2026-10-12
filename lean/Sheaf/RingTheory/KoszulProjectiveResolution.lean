module

public import Sheaf.RingTheory.KoszulRegularSequence
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # The Koszul resolution of a quotient

Source: Stacks Project, Tags 0623, 062E and 0BQZ.
(blueprint: new-j3-koszul-projective-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace ExteriorAlgebra

/-- The Koszul complex of a Koszul-regular sequence resolves its quotient.
Source: Stacks Project, Tag 0623 (the Koszul complex), Tag 062E (Koszul
regularity), and Tag 0BQZ (the finite free resolution used in the Ext calculation).
(blueprint: new-j3-koszul-projective-resolution).

Proof: In degree zero use the exterior-power isomorphism wedge^0(A^r) = A
and the quotient map A -> A/I; in higher degrees use zero. Contraction in degree
one sends the standard basis vector e_i to f_i, so its image in degree zero is
span(range f) = I. The quotient map therefore kills d_1 and defines the chain
augmentation. Its degree-zero homology map is an isomorphism by the cokernel
universal property. In positive degrees source homology is zero by hreg and
homology of the single complex is zero, so the augmentation is a
quasi-isomorphism in every degree. Finally, the exterior basis induced by the
standard basis of Fin r ->_0 A makes every term free, hence projective. Bundle
these data as a ProjectiveResolution with exactly the original chain complex.
For r = 0 the augmentation is the isomorphism A -> A/(0); no properness of I
is needed, so the construction also applies when A/I is zero. -/
theorem exists_koszul_projective_resolution
    (A : Type u) [CommRing A] (I : Ideal A) (r : ℕ) (f : Fin r → A)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) (hf : Ideal.span (Set.range f) = I) :
    ∃ P : ProjectiveResolution (ModuleCat.of A (A ⧸ I)),
      P.complex = koszulComplex A r f := by sorry

end ExteriorAlgebra
