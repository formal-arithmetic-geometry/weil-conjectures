/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.GRing
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.Submodule
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.PolynomialCompleteLocalGenericFibreRegularPart

/-!
# Generic polynomial formal fibres of complete local domains

Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraphs 3--5.
(blueprint: lem-weil-pbc-polynomial-complete-local-generic-fibre)
-/

@[expose] public section

universe u

namespace Polynomial

/-- The generic formal fibre over a complete local domain is geometrically regular.
Source: Stacks Project, More on Algebra, proof of Proposition 07PV, paragraphs 3--5.
(blueprint: lem-weil-pbc-polynomial-complete-local-generic-fibre)

Proof:
1. Choose a regular complete local subring A₀ of A with A finite over A₀, by 032D.
   The polynomial extension is finite too. The contraction q₀ of q is maximal and
   lies over the maximal ideal of A₀: finite integral extensions contract maximal
   ideals to maximal ideals. The finite polynomial map is quasi-finite at q.
2. Apply 07PP(1) to the zero primes of A₀[X] and A[X]; injectivity gives contraction
   zero. It reduces this fibre to the generic formal fibre for A₀ at q₀.
3. A₀[X] is regular by smooth ascent (07NF). Its local ring at q₀ and its completion
   are regular, by regular local localization and completion regularity (07NY).
   Its generic fibre is a localization of that completion, so is regular and
   Noetherian. In characteristic zero, finite purely inseparable field extensions
   are trivial, giving geometric regularity.
4. In positive characteristic the coefficient subring cannot be a power series
   ring over a Cohen ring, whose nonzero prime-number uniformizer forces
   characteristic zero. Thus A₀ is a finite-variable power series ring over a field.
   Apply 07PR with one polynomial variable, and transport the result along the
   coefficient and univariate/multivariate polynomial isomorphisms. Then 07PP(1)
   gives the original generic fibre. This covers both characteristics. -/
theorem completeLocalGenericFibre
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap (Polynomial.C : A →+* Polynomial A) = IsLocalRing.maximalIdeal A) :
    Algebra.IsGeometricallyRegular (⊥ : Ideal (Polynomial A)).ResidueField
      ((⊥ : Ideal (Polynomial A)).Fiber
        (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q))) := by
  have : IsNoetherianRing (Localization.AtPrime q) := inferInstance
  have := AdicCompletion.isNoetherianRing
    (IsLocalRing.maximalIdeal (Localization.AtPrime q))
  refine ⟨Ideal.isNoetherianRing_fiber (⊥ : Ideal (Polynomial A)), ?_⟩
  intro k' _ _ _ _
  exact completeLocalGenericFibre_regularPart A q hq k'

end Polynomial
