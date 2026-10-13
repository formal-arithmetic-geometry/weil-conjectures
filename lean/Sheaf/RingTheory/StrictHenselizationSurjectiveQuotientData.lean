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
  have _ := hI
  let L := SeparableClosure (IsLocalRing.ResidueField B)
  let : Field L := inferInstance
  let : Algebra (IsLocalRing.ResidueField B) L := inferInstance
  let : IsSepClosure (IsLocalRing.ResidueField B) L := inferInstance
  let : Algebra B L := RingHom.toAlgebra
    ((algebraMap (IsLocalRing.ResidueField B) L).comp (IsLocalRing.residue B))
  let : IsScalarTower B (IsLocalRing.ResidueField B) L :=
    IsScalarTower.of_algebraMap_eq' (R := B) (S := IsLocalRing.ResidueField B) (A := L)
      (by ext; rfl)
  let J := I.map (algebraMap A C)
  let f : A →+* C ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap A C)
  have hf : RingHom.ker π ≤ RingHom.ker f := by
    intro a ha
    apply RingHom.mem_ker.mpr
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap A C) (hker ▸ ha))
  let hC : Algebra B (C ⧸ J) := (π.liftOfSurjective hπ ⟨f, hf⟩).toAlgebra
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hC, trivial⟩

end Algebra
