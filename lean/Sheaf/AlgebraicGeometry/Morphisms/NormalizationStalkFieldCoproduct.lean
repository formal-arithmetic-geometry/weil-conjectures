/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Stalk
import Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange

/-! # Normalization of a finite field coproduct over a stalk
Source: Stacks Project, Tags 0307 and 035I. -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A field-coproduct presentation over a stalk induces the integral-closure
coproduct presentation of relative normalization over that stalk.

Source: Stacks Project, Tags 0307 and 035I; step 2 of
lem-sbc-cartier-stalk-normalization-product.
(blueprint: lem-sbc-normalization-stalk-field-coproduct)

Proof: Relative normalization commutes with localization at the stalk, by
normalization stalk base change. Use the affine description of normalization
on Spec R: its coordinate ring is the integral closure of R in the sections
of the base-changed source. The supplied isomorphism identifies these sections
as the finite product of E_i, respecting the R-algebra maps by its equation.
A tuple is integral precisely when all its coordinates are integral. One
implication follows by projection; for the other, multiply the finitely many
monic annihilating polynomials of its coordinates. This gives an R-algebra
isomorphism from the integral closure in the product to the product of the
integral closures. Apply Spec and the finite-product/coproduct comparison.
The algebra maps commute throughout, which gives the displayed equation.
For n = 0 the product is the zero ring and both schemes are empty. No group
action, finiteness of normalization, domain condition, or DVR is needed. -/
theorem normalization_stalk_field_coproduct
    {N P : Scheme.{u}} (a : P ⟶ N) [QuasiCompact a] [QuasiSeparated a]
    (s : N) (n : ℕ) (E : Fin n → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (N.presheaf.stalk s) (E i)]
    (e : pullback a (N.fromSpecStalk s) ≅
      ∐ fun i : Fin n ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin n ↦ Spec.map
      (CommRingCat.ofHom (algebraMap (N.presheaf.stalk s) (E i)))) =
        pullback.snd a (N.fromSpecStalk s)) :
    ∃ e' : pullback a.fromNormalization (N.fromSpecStalk s) ≅
        ∐ fun i : Fin n ↦
          Spec (CommRingCat.of (integralClosure (N.presheaf.stalk s) (E i))),
      e'.hom ≫ Sigma.desc (fun i : Fin n ↦ Spec.map (CommRingCat.ofHom
        (algebraMap (N.presheaf.stalk s) (integralClosure (N.presheaf.stalk s) (E i))))) =
          pullback.snd a.fromNormalization (N.fromSpecStalk s) := by sorry

end AlgebraicGeometry.Scheme
