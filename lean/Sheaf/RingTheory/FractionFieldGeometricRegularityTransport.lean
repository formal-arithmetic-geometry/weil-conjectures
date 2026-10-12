module
public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
universe u
/-- Geometric regularity over a domain is preserved after changing the chosen
fraction field. Source: Stacks Project, More on Algebra, Proposition 07PS.
(blueprint: lem-weil-pbc-fraction-field-geometric-regularity-transport).
Proof: construct the unique A-algebra equivalence between K and the canonical
fraction field using the universal property of IsFractionRing. Transport finite
purely inseparable extensions and regularity across this equivalence, and identify
the resulting tensor products by the induced tensor equivalence.
-/
theorem fractionField_geometricallyRegular_tensorProduct_transport
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (C : Type u) [CommRing C] [Algebra A C]
    (h : Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber C)) :
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  sorry
