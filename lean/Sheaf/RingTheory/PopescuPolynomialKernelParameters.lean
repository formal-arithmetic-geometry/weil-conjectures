/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularSequencePolynomialVariables
import Sheaf.RingTheory.RegularSequencePowers
import Sheaf.AlgebraicGeometry.Ogoma

/-!
# Polynomial parameters with stable multiplication kernels

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, items 10--12.
(blueprint: lem-weil-pbc-popescu-polynomial-kernel-parameters).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Select polynomial representatives of the parameters and equalize the polynomial
multiplication kernels. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ,
items `item-choose-pii` and `item-modify-pii`.
(blueprint: lem-weil-pbc-popescu-polynomial-kernel-parameters).

Proof: The field and its polynomial algebra are regular. Geometric regularity makes
L regular. The flat height formula applied to the local map with maximal ideal
extending to the maximal ideal of L gives dimension d for the source localization.
Choose d generators of its maximal ideal and write them as fractions. Their numerators
are in the contracted prime and still generate, since their denominators are units.
Their images generate the maximal ideal of L and are a regular sequence there.
All permutations of the source parameters are regular. Multiplying them by distinct
polynomial variables gives a regular sequence over the localized source polynomial
ring. Induct on the index i. Powers of the earlier terms followed by the current term
are regular after localization. Ogoma on the quotient by the earlier e-th powers
supplies a factor outside the contracted prime that equalizes the first and square
kernels before localization. Multiply only the current parameter by this factor.
Earlier kernels are unchanged, and the localized parameter ideals and regularity
are unchanged because the factor is a unit. For d=0 the parameter families are empty;
the dimension formula makes both maximal ideals zero and all kernel claims vacuous. -/
theorem exists_popescu_polynomial_kernel_parameters
    {k : Type u} {Λ : Type w}
    [Field k] [CommRing Λ] [Algebra k Λ] [IsNoetherianRing Λ]
    (q : PrimeSpectrum Λ) (hreg : IsGeometricallyRegular k Λ)
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (e : ℕ) (he : 0 < e)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat) :
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let L := Localization.AtPrime q.asIdeal
    ∃ uP : Fin d → P,
      (∀ i, uP i ∈ p₀) ∧
      Ideal.span (Set.range (fun i ↦ algebraMap P (Localization.AtPrime p₀) (uP i))) =
        p₀.map (algebraMap P (Localization.AtPrime p₀)) ∧
      RingTheory.Sequence.IsRegular L
        (List.ofFn (fun i ↦ algebraMap Λ L (φ₀ (uP i)))) ∧
      (∀ (i : Fin d)
        (x : MvPolynomial (Fin d) P ⧸ Ideal.span
          {y | ∃ j : Fin d, j.val < i.val ∧
            y = (MvPolynomial.C (uP j) * MvPolynomial.X j) ^ e}),
        (MvPolynomial.C (uP i) * MvPolynomial.X i) • x = 0 ↔
          (MvPolynomial.C (uP i) * MvPolynomial.X i) ^ 2 • x = 0) := by sorry

end Algebra
