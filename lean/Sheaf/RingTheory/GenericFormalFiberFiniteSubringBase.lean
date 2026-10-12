module
public import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
universe u
/-- Generic formal-fibre regularity over the canonical generic residue field, obtained by
applying quasi-finite formal-fibre ascent to a finite subring.
Source: Stacks Project, More on Algebra, Proposition 07PS and Lemma 07PP.
(blueprint: lem-weil-pbc-generic-formal-fibre-finite-subring-base).
Proof: Apply the quasi-finite formal-fibre ascent theorem to the finite subring inclusion
and the zero prime contained in P. -/
theorem genericFormalFiber_bot_geometricallyRegular_of_finite_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (A₀ : Subring A) [IsNoetherianRing A₀] [Module.Finite A₀ A]
    (P : Ideal A) [P.IsPrime]
    (hbase :
      let P₀ := P.comap (algebraMap A₀ A)
      let C₀ := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P₀))
        (Localization.AtPrime P₀)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A₀).ResidueField
        ((⊥ : Ideal A₀).Fiber C₀)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField
      ((⊥ : Ideal A).Fiber C) := by
  sorry
