module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.CompletionRegularLocal
import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
import Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.RegularRingSmoothAscent

@[expose] public section

open scoped TensorProduct
universe u

namespace Polynomial

/-- The regularity part of the generic formal fibre argument.
Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraphs 3--5.
(blueprint: lem-weil-pbc-polynomial-complete-local-generic-fibre-regular-part)
Proof: Choose a regular complete local subring A₀ with A finite over A₀ (032D).
The map A₀[X] → A[X] is finite and injective. The contraction q₀ is maximal;
it lies over the maximal ideal of A₀. The zero prime contracts to zero.
Finite maps are quasi-finite, so 07PP(1) reduces geometric regularity of this
fibre to the corresponding fibre for A₀[X]. The polynomial ring A₀[X] is regular
by smooth ascent, and its localization at q₀ and completion are regular by 07NY.
The generic fibre is a localization of the completion, hence regular.
If the fraction field has characteristic zero, each finite purely inseparable
extension is trivial, so its base changes remain regular. In positive
characteristic, the injective coefficient map excludes the Cohen-ring model:
its nonzero prime-number uniformizer forces characteristic zero. Thus A₀ is a
power series ring over a field. Apply 07PR with one polynomial variable and
transport along the coefficient-ring and univariate/multivariate polynomial
isomorphisms. Quasi-finite ascent then gives regularity after every finite
purely inseparable extension of the original fraction field. This proves the
displayed regularity component. All choices are used only in a proposition;
no definition chooses arbitrary data from an unproved existence theorem. -/
theorem completeLocalGenericFibre_regularPart
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A) :
    ∀ (k' : Type (max u u)) [Field k']
      [Algebra (⊥ : Ideal (Polynomial A)).ResidueField k']
      [Module.Finite (⊥ : Ideal (Polynomial A)).ResidueField k']
      [IsPurelyInseparable (⊥ : Ideal (Polynomial A)).ResidueField k'],
      IsRegularRing
        (k' ⊗[(⊥ : Ideal (Polynomial A)).ResidueField]
          ((⊥ : Ideal (Polynomial A)).Fiber
            (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
              (Localization.AtPrime q)))) := by
  sorry

end Polynomial
