module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.FlatCompletion
import Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres
import Sheaf.RingTheory.QuotientGRing
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.RegularPermanence

/-! Auxiliary formal-fibre step for finite type algebras over G-rings.

Source: Stacks Project, More on Algebra, Proposition 07PV (blueprint:
lem-weil-pbc-finite-type-over-g-ring), the maximal-ideal and completion steps.
-/

@[expose] public section

universe u v

/-- If `R` is a G-ring and `S` is finite type over `R`, then every prime-local
completion map of `S` is regular.  This is the formal-fibre part of the proof of
Proposition 07PV: write `S` as a quotient of a polynomial algebra, reduce to a
maximal ideal, localize the base at its contraction, and use regular base change,
the complete-local polynomial case, composition, and faithfully-flat descent.
(blueprint: lem-weil-pbc-finite-type-over-g-ring-formal-fibres)
-/
theorem finiteType_completion_regular
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (hR : IsGRing R) [Algebra.FiniteType R S] :
    ∀ (p : Ideal S) [p.IsPrime],
      RingHom.IsRegular
        (algebraMap (Localization.AtPrime p)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
            (Localization.AtPrime p))) := by
  sorry
