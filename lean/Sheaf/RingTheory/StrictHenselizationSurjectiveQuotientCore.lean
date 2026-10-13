module

public import Sheaf.RingTheory.IsStrictHenselization

@[expose] public section
universe u
namespace Algebra

/-- Base-change of the pointed etale colimit along a surjective local quotient.
Source: Stacks Project, Tag 05WS.
(blueprint: lem-sbc-strict-henselization-surjective-quotient-core)
-/
theorem strictHenselization_surjective_quotient_core
    (A K C B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] (hC : IsStrictHenselization A K C)
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hI : I ≤ IsLocalRing.maximalIdeal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))] :
    IsStrictHenselization B L (C ⧸ I.map (algebraMap A C)) := by
  sorry

end Algebra
