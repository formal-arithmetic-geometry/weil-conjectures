/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Smooth.Basic

/-!
# Split conormal sequence of a smooth principal localization

Source: Stacks Project, Smoothing Ring Maps, proofs of Tags 07EZ (part (e)) and 07C6
(blueprint: lem-weil-pbc-smooth-localization-conormal-split).
-/

set_option autoImplicit false

universe u

namespace Algebra

variable (R : Type u) [CommRing R] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R))
variable (a : MvPolynomial (Fin n) R ⧸ I)

local notation "A" => (MvPolynomial (Fin n) R ⧸ I)
local notation "B" => Localization.Away a
local notation "M" => LocalizedModule.Away a I.Cotangent

attribute [local instance] LocalizedModule.moduleOfIsLocalization

/-- The localized conormal differential of a polynomial presentation splits when the localized
quotient is smooth. The two maps are specified by their values on `g mod I²` divided by one
and on the coordinate basis vectors. These values uniquely determine the localized differential
and the map to Kähler differentials. The finite free module is represented by `Fin n → B`,
and the sum of the conormal and differential modules by their product.

Source: Stacks Project, Smoothing Ring Maps, proofs of Tags 07EZ (part (e)) and 07C6
(blueprint: lem-weil-pbc-smooth-localization-conormal-split).

Proof:
1. Lift `a` to `h` in the polynomial ring and present `B` by adjoining `x₀` with relation
   `h x₀ - 1` (lem-weil-pbc-principal-localization-naive-cotangent). The polynomial algebra
   with this extra variable is smooth (lem-weil-pbc-polynomial-ring-smooth).
   The Jacobi--Zariski quotient sequence (lem-weil-pbc-jacobi-zariski-quotient-smooth) and
   smoothness of `B` give injectivity of its conormal differential, surjectivity onto its
   Kähler differentials, and equality of the image and kernel; the latter module is projective.
2. The principal-localization naive-cotangent lemma identifies that complex with the localized
   original complex plus the contractible complex `B → B` given by multiplication by `a`.
   The polynomial differential basis (lem-weil-pbc-polynomial-ring-kahler-basis) identifies
   its middle term with the coordinate free module. The quotient map has the stated basis
   values by the universal derivation (def-weil-pbc-kahler-differentials).
3. Projectivity (def-weil-pbc-projective-module) splits the surjection. Projection onto its
   kernel, identified with the conormal module by the injective differential, gives the left
   inverse. The two summands give the displayed linear equivalence. -/
theorem smooth_localization_conormal_split
    [Smooth R B] :
    ∃ (d : M →ₗ[B] (Fin n → B)) (π : (Fin n → B) →ₗ[B] KaehlerDifferential R B),
      (∀ (g : I) (i : Fin n),
        d (LocalizedModule.mkLinearMap (Submonoid.powers a) I.Cotangent
          (I.toCotangent g)) i =
            algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.pderiv i (g : _)))) ∧
      (∀ i : Fin n, π (Pi.single i 1) =
        KaehlerDifferential.D R B
          (algebraMap A B (Ideal.Quotient.mk I (MvPolynomial.X i)))) ∧
      (∃ l : (Fin n → B) →ₗ[B] M, l.comp d = LinearMap.id) ∧
      Function.Injective d ∧ Function.Surjective π ∧
      LinearMap.ker π = LinearMap.range d ∧
      (∃ s : KaehlerDifferential R B →ₗ[B] (Fin n → B), π.comp s = LinearMap.id) ∧
      Nonempty ((M × KaehlerDifferential R B) ≃ₗ[B] (Fin n → B)) := by
  sorry

end Algebra
