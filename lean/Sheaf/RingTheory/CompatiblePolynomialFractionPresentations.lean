/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.FiniteType

/-!
# Compatible polynomial maps with unit-denominator presentations

Source: Stacks Project, Algebra, Tag 00SF (lemma-lci-local), simultaneous-presentation
refinement using Tags 00QM, 00F3 and the fraction construction preceding Tag 00CO
(blueprint: lem-trf-compatible-polynomial-fraction-presentations).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

namespace Algebra

/-- Two essentially finite type algebras surjecting onto a common algebra admit compatible
maps from a finite polynomial algebra. Each algebra has unit-denominator fraction
presentations using its own block of variables. The blocks may be empty.

Source: Stacks Project, Algebra, Tag 00SF (lemma-lci-local), agent refinement using
Tags 00QM, 00F3 and the fraction construction preceding Tag 00CO
(blueprint: lem-trf-compatible-polynomial-fraction-presentations).

Proof:
1. By `def-weil-pbc-essentially-finite-type-algebra`, write `P` and `Q` as localizations
   of finite type algebras `B` and `C`. By `def-weil-pbc-finite-type-algebra`, choose
   surjections from polynomial rings on `Fin r` and `Fin s` to these algebras.
   Their variable images in the localizations give `p` and `q`.
2. Lift the images of `q` through the surjection `u` to obtain `qLift`, and lift the
   images of `p` through `v` to obtain `pLift`. The universal property in
   `def-weil-pbc-mv-polynomial-ring` gives `f` and `g` on the sum of the two blocks.
   Their composites agree on every variable, hence are equal by that universal property.
   Renaming along `Sum.inl` and `Sum.inr` embeds the two blocks: extending monomial
   exponents by zero preserves distinct monomials.
3. For an element of `P`, write its preimage in the localization as `b / t`.
   Surjectivity of the polynomial presentation of `B` supplies polynomial lifts of
   `b` and `t` in the first block. Evaluation of the latter is a unit with inverse
   the image of `1 / t`, and multiplying the original element by it gives the
   evaluation of the numerator. The equality of evaluation with the localization
   map on this block follows from the polynomial universal property.
4. Apply the same fraction argument in the second block to every element of `Q`.
   The fraction identities follow directly from the localization construction in
   `def-weil-pbc-essentially-finite-type-algebra`. Empty blocks and zero target
   rings cause no exception: the empty-block polynomial algebra is `k`, and in a
   zero ring `0 = 1` is a unit. No locality or regularity is used.
-/
theorem exists_compatible_polynomial_fraction_presentations
    (k : Type u) [Field k]
    (P : Type v) [CommRing P] [Algebra k P] [EssFiniteType k P]
    (Q : Type w) [CommRing Q] [Algebra k Q] [EssFiniteType k Q]
    (A : Type z) [CommRing A] [Algebra k A]
    (u : P →ₐ[k] A) (v : Q →ₐ[k] A)
    (hu : Function.Surjective u) (hv : Function.Surjective v) :
    ∃ (r s : ℕ) (p : Fin r → P) (q : Fin s → Q)
      (qLift : Fin s → P) (pLift : Fin r → Q)
      (f : MvPolynomial (Fin r ⊕ Fin s) k →ₐ[k] P)
      (g : MvPolynomial (Fin r ⊕ Fin s) k →ₐ[k] Q),
      (∀ i : Fin r, f (MvPolynomial.X (Sum.inl i)) = p i) ∧
      (∀ j : Fin s, f (MvPolynomial.X (Sum.inr j)) = qLift j) ∧
      (∀ i : Fin r, g (MvPolynomial.X (Sum.inl i)) = pLift i) ∧
      (∀ j : Fin s, g (MvPolynomial.X (Sum.inr j)) = q j) ∧
      (∀ j : Fin s, u (qLift j) = v (q j)) ∧
      (∀ i : Fin r, v (pLift i) = u (p i)) ∧
      u.comp f = v.comp g ∧
      (∀ x : P, ∃ a t : MvPolynomial (Fin r) k,
        IsUnit (f (MvPolynomial.rename Sum.inl t)) ∧
        x * f (MvPolynomial.rename Sum.inl t) = f (MvPolynomial.rename Sum.inl a)) ∧
      (∀ y : Q, ∃ c z : MvPolynomial (Fin s) k,
        IsUnit (g (MvPolynomial.rename Sum.inr z)) ∧
        y * g (MvPolynomial.rename Sum.inr z) = g (MvPolynomial.rename Sum.inr c)) := by
  sorry

end Algebra
