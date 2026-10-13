module

public import Sheaf.RingTheory.IsStrictHenselization

@[expose] public section
universe u
namespace Algebra

/-- The residue-field and quotient-algebra structures needed for strict henselization
under a surjective local quotient exist. Source: Stacks Project, Tag 05WS.
(blueprint: lem-sbc-strict-henselization-surjective-quotient-data)
-/
theorem strictHenselization_surjective_quotient_data
    (A K C B : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C]
    [CommRing B] [IsLocalRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I) :
    ∃ (L : Type u) (_ : Field L)
      (_ : Algebra (IsLocalRing.ResidueField B) L)
      (_ : IsSepClosure (IsLocalRing.ResidueField B) L)
      (_ : Algebra B L) (_ : IsScalarTower B (IsLocalRing.ResidueField B) L)
      (_ : Algebra B (C ⧸ I.map (algebraMap A C))), True := by
  sorry

end Algebra
