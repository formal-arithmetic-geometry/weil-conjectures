module
public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
universe u
/-- Geometric regularity of a generic formal fibre is invariant under replacing the
canonical fraction field by any chosen fraction field.
Source: Stacks Project, More on Algebra, Proposition 07PS.
(blueprint: lem-weil-pbc-generic-formal-fibre-fraction-field-transport).
Proof: Use the universal property of fraction fields to identify the chosen field with the
canonical residue field, then transport geometric regularity across the induced tensor
isomorphism. -/
theorem genericFormalFiber_geometricallyRegular_of_fractionField_transport
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (P : Ideal A) [P.IsPrime]
    (h :
      let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
        ((⊥ : Ideal A).Fiber C)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  sorry
