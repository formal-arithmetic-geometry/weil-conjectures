/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Principal-ideal Elkik approximation along a smooth open

Source: Elkik, Solutions d'équations à coefficients dans un anneau hensélien (1973),
II, Lemma 4, printed pp. 564–566 (blueprint: lem-per-elkik-principal-section-approximation).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-- A formal section whose punctured image lies in a smooth open can be approximated
by an algebraic section to every positive order. No regularity assumption is made on `t`.
Source: Elkik (1973), II, Lemma 4, printed pp. 564–566
(blueprint: lem-per-elkik-principal-section-approximation).

Proof plan, following the node's eight steps:
1. Henselianity puts `t` in the Jacobson radical. Apply
   `lem-per-jacobson-adic-completion-faithfully-flat`,
   `lem-weil-pbc-faithfully-flat-ideal-contraction`, and
   `lem-weil-pbc-adic-completion-mod-power` to identify reduction and contraction.
   For nilpotent `t` the completion is `A`, and the section already suffices.
2. Artin–Rees (`lem-weil-pbc-artin-rees`) bounds the intersection of the `t`-power
   torsion ideal with sufficiently high powers of `t` by zero.
3. Use `lem-per-elkik-conormal-smooth-open-chart` to replace `B` by a retract with
   a polynomial presentation whose conormal is free on the inverse image of `W`.
4. Radical containment (`lem-weil-pbc-zero-locus-eq-iff-radical-eq`) and approximation
   of coefficients select a principal open containing the punctured formal image.
   The resulting factor `1 + t*z` is invertible in the completion by geometric sums.
5. The chart and radical containment give power certificates for its denominator
   and its maximal Jacobian minors, evaluated on the formal section.
6. Approximate the section and certificate coefficients to order `L`, with
   `L > 2*g` and `R = L-g` exceeding the denominator, torsion, and requested bounds.
   Contract the residual errors to `A` and use
   `lem-weil-pbc-jacobson-radical-one-plus-units` to preserve the Jacobian certificate.
7. Apply `lem-per-tougeron-henselian-jacobian-correction` with orders `L,g` over
   the original henselian pair, obtaining an exact solution of the chart equations
   congruent to the formal section modulo `t^R`.
8. Transfer the denominator certificate to `A`. All remaining relations are then
   both `t`-power torsion and divisible by `t^R`, so step 2 kills them. Evaluation
   factors through the chart algebra; restricting along the retract gives `v`.
   Reduction to order `m` is the asserted equality of ring homomorphisms.
-/
theorem exists_algHom_elkik_principal_section_approximation
    {A B : Type u} [CommRing A] [IsNoetherianRing A]
    (t : A) [HenselianRing A (Ideal.span {t})]
    [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (W : (Spec (CommRingCat.of B)).Opens)
    (hW : Smooth (W.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (u : B →ₐ[A] AdicCompletion (Ideal.span {t}) A)
    (hu : ∀ x : PrimeSpectrum (AdicCompletion (Ideal.span {t}) A),
      algebraMap A (AdicCompletion (Ideal.span {t}) A) t ∉ x.asIdeal →
        (Spec.map (CommRingCat.ofHom u.toRingHom)) x ∈ W) :
    ∀ m : ℕ, 1 ≤ m → ∃ v : B →ₐ[A] A,
      (Ideal.Quotient.mk ((Ideal.span {t}) ^ m)).comp v.toRingHom =
        (AdicCompletion.evalₐ (Ideal.span {t}) m).toRingHom.comp u.toRingHom := by
  sorry
