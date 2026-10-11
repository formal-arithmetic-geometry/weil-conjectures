/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Smooth.Basic
import Sheaf.RingTheory.StrictlyStandardElement

/-!
# Delocalizing a smooth factorization

Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4
(blueprint: lem-weil-pbc-popescu-delocalize-base).
-/

universe u v w x

namespace Algebra

/-- A smooth factorization after localizing the base descends to a finitely presented
factorization in which some denominator becomes elementary standard.
Source: Stacks Project, Smoothing Ring Maps, Lemma Tag 07F4
(blueprint: lem-weil-pbc-popescu-delocalize-base).

Proof (the eleven steps of the DAG node):
1. Use `lem-weil-pbc-smooth-retract-standard-smooth` to replace the smooth intermediate
   algebra by a standard smooth algebra with a retraction, preserving the factorization.
2. Choose finitely many generators and relations for `A` using
   `def-weil-pbc-finitely-presented-algebra`; their images in the target satisfy the relations.
3. By `lem-weil-pbc-standard-smooth-include-generators`, choose a standard smooth presentation
   whose first variables are the images of those generators and whose initial minor is a unit.
4. Rescale the extra variables by denominators so their images come from the target ring;
   `def-weil-pbc-polynomial-partial-derivative` shows the minor changes by a unit.
5. Use `lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-localization-base-change`
   to identify the polynomial scalar extension with localization. Fractions have common
   denominators, equality can be cleared by a denominator, and derivatives commute with it.
6. Clear denominators in the smooth equations, preserving the presentation and unit minor.
7. Clear denominators in a relation expressing the inverse of the minor to obtain
   `s₀ = a₀ Δ + ∑ aⱼ fⱼ` in the polynomial ring over the original base.
8. Each original relation vanishes in the localized presentation, so some denominator
   multiplies it into the ideal of the smooth equations.
9. Each smooth equation vanishes after evaluation in the localized target, so some
   denominator kills its evaluation in the original target (`def-weil-pbc-module-localization`).
10. Quotient the polynomial ring by the denominator-scaled smooth equations and the original
    relations. This is finitely presented and gives both maps; agreement on generators proves
    their composite is the original map (`def-weil-pbc-mv-polynomial-ring`).
11. Multiply all chosen denominators. The product times every remaining relation belongs
    to the initial relation ideal. The identity in step 7, multiplied by the equation
    denominators, makes the product divisible by the initial Jacobian minor in the quotient.
    These are both conditions of `def-weil-pbc-strictly-standard-element` (1). -/
theorem exists_factorization_isElementaryStandardElement_of_localized_smooth
    {R : Type u} {A : Type v} {Λ : Type w}
    [CommRing R] [CommRing A] [CommRing Λ] [Algebra R A] [Algebra R Λ]
    [FinitePresentation R A] (α : A →ₐ[R] Λ) (S : Submonoid R)
    {B' : Type x} [CommRing B'] [Algebra (Localization S) B']
    [Smooth (Localization S) B']
    (β' : Localization (algebraMapSubmonoid A S) →ₐ[Localization S] B')
    (γ' : B' →ₐ[Localization S] Localization (algebraMapSubmonoid Λ S))
    (hfactor : γ'.comp β' =
      IsLocalization.mapₐ S (Localization S)
        (Localization (algebraMapSubmonoid A S)) (Localization (algebraMapSubmonoid Λ S)) α) :
    ∃ (B : Type (max u v w x)) (_ : CommRing B) (_ : Algebra R B)
      (_ : FinitePresentation R B) (β : A →ₐ[R] B) (γ : B →ₐ[R] Λ),
      γ.comp β = α ∧ ∃ s : S, IsElementaryStandardElement (R := R) (algebraMap R B s.val) := by
  sorry

end Algebra
