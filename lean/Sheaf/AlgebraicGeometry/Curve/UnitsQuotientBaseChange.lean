/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import WeilConjectures.AlgebraicGeometry.Curve
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Units modulo powers under algebraically closed base change

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance/thm-sc-constant-invariance,
affine-case proof, unit quotient paragraph (blueprint: lem-sc-units-quotient-base-change).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pullback identifies units modulo `n`-th powers after extending algebraically closed fields.
The equation on representatives specifies that the isomorphism is induced by pullback.

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance/thm-sc-constant-invariance,
affine-case proof, unit quotient paragraph (blueprint: lem-sc-units-quotient-base-change).

Proof:
1. Choose a smooth proper connected compactification with finite boundary using
   lem-sc-compactification. By lem-sc-base-change-curve its base change is again a smooth
   proper connected compactification. Boundary points are rational over the algebraically
   closed field, so their base changes identify the free boundary divisor groups.
2. By lem-sc-affine-unit-divisor-base-change this identification carries the subgroup `L`
   of boundary divisors of units onto `L'` and commutes with pullback of units.
   The divisor map onto `L` is surjective by its definition. Its kernel consists of global
   units on the compactification, by lem-sc-divisor-exact-sequence and left exactness of
   global sections. These are precisely the constants by lem-sc-global-functions.
   The same argument applies over the extension field.
3. Constants in both algebraically closed fields are `n`-divisible for `n ≥ 1`.
   The divisor maps therefore identify the two unit quotients with `L/nL` and `L'/nL'`:
   equality modulo `n` of divisors means equality up to an `n`-th power and a constant,
   and the constant has an `n`-th root. The compatible identification of `L` with `L'`
   induces the desired isomorphism, with the stated equation on unit classes. -/
theorem units_quotient_base_change
    (k k' : Type u) [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    (C : Scheme.{u}) (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ e : (Γ(C, ⊤)ˣ ⧸ (powMonoidHom n : Γ(C, ⊤)ˣ →* Γ(C, ⊤)ˣ).range) ≃*
        (Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ ⧸
          (powMonoidHom n :
            Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ →*
            Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k'))), ⊤)ˣ).range),
      ∀ a : Γ(C, ⊤)ˣ,
        e (QuotientGroup.mk a) =
          QuotientGroup.mk (Units.map (pullback.fst f
            (Spec.map (CommRingCat.ofHom (algebraMap k k')))).appTop.hom.toMonoidHom a) := by
  sorry

end AlgebraicGeometry
