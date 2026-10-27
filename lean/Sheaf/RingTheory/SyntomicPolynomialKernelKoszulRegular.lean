/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import WeilConjectures.RingTheory.SyntomicAtPrimeRelativeGlobalCompleteIntersection
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Syntomic polynomial presentation kernels are locally Koszul-regular

Source: Stacks Project, More on Algebra, Tag 07D3 (forward implication),
with Tags 07D2, 07D1 and 07CZ
(blueprint: lem-sfb-syntomic-polynomial-kernel-koszul-regular).
-/

@[expose] public section

universe u v

set_option autoImplicit false

namespace Algebra

/-- Every finite polynomial presentation of a syntomic algebra has locally
Koszul-regular kernel. Source: Stacks Project, More on Algebra, Tag 07D3,
forward implication, and Tag 07CZ (independence of presentation).
(blueprint: lem-sfb-syntomic-polynomial-kernel-koszul-regular).

Proof:
1. For each prime s of E, the flat-local-ring-maps lemma gives a flat local map
R_p → E_s. The local complete intersection fibre hypothesis supplies a principal
neighbourhood of the corresponding fibre prime that is a global complete intersection.
Apply lem-weil-pbc-syntomic-at-prime-relative-global-complete-intersection, using
finite presentation with g = 1, to obtain g_s outside s and a specified relative
global complete intersection presentation of E[1/g_s].
2. By lem-sfb-relative-global-ci-koszul-regular, each chart's equations are
Koszul-regular. Taking the principal neighbourhood D(1) gives a presentation
with locally Koszul-regular kernel on that chart.
3. By lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact, finitely many of
these chart elements generate the unit ideal. The supplied surjection β gives
finite type. Apply lem-sfb-koszul-polynomial-presentation-principal-gluing to
obtain some finite polynomial presentation α of E with locally Koszul-regular
kernel. The empty cover covers the zero algebra, so that case is included.
4. Apply lem-sfb-koszul-polynomial-presentation-independence to α and β, and
unpack local Koszul regularity at q to obtain the displayed witnesses.
The natural-number indexing permits both zero variables and the empty equation
sequence; no nontriviality or Noetherian hypothesis is imposed. -/
theorem exists_koszulRegular_kernel_generators_of_syntomic
    {R : Type u} {E : Type v} [CommRing R] [CommRing E] [Algebra R E]
    [Module.Flat R E] [FinitePresentation R E]
    (hci : ∀ p : PrimeSpectrum R,
      IsLocalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber E))
    (m : ℕ) (β : MvPolynomial (Fin m) R →ₐ[R] E) (hβ : Function.Surjective β)
    (q : PrimeSpectrum (MvPolynomial (Fin m) R)) (hq : RingHom.ker β.toRingHom ≤ q.asIdeal) :
    ∃ h : MvPolynomial (Fin m) R, h ∉ q.asIdeal ∧
      ∃ (r : ℕ) (f : Fin r → Localization.Away h),
        (RingHom.ker β.toRingHom).map
            (algebraMap (MvPolynomial (Fin m) R) (Localization.Away h)) =
          Ideal.span (Set.range f) ∧
        RingTheory.Sequence.IsKoszulRegular f := by
  sorry

end Algebra
