/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1, reviewer R-ppd1203
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.DivisorClassCurve
import Sheaf.AlgebraicGeometry.DivisorModule
import Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings
import WeilConjectures.AlgebraicGeometry.Curve.SerreDuality
import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# The Picard group of a proper curve splits as `ℤ × Pic⁰`

Source: blueprint, `sec-curve-estimates/sk-def-pic`, node lem-sc-pic-proper-decomposition,
order 888 (blueprint: lem-sc-pic-proper-decomposition).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- Source: blueprint, `sec-curve-estimates/sk-def-pic`, node lem-sc-pic-proper-decomposition,
order 888 (blueprint: lem-sc-pic-proper-decomposition).

Let `C` be a proper smooth connected curve over the algebraically closed field `k`. The degree
sequence `0 → Pic⁰(C) → Pic(C) → ℤ → 0` splits: `Pic⁰(C)` is a subgroup `P0` of `Pic(C)` with
underlying set `f.picZero`, and there is an isomorphism `Pic(C) ≅ ℤ × Pic⁰(C)` (`ℤ` written
multiplicatively, as the group law of `Pic(C)`) whose first component is the degree and which
restricts to the identity on `Pic⁰(C)`.

Proof, step 1: by lem-sc-smooth-connected-curve-local-rings (2) `C` has a closed point `P`,
which is `k`-rational by lem-weil-pbc-closed-point-residue-field-base. The degree of def-sc-pic0
is the degree of divisors transported along `Cl(C) ≅ Pic(C)` (lem-sc-divisor-class-curve, well
defined by lem-sc-deg-principal-zero), a homomorphism; `λ = [𝒪_C(P)]` has degree `deg [P] = 1`
(def-sc-divisor), so `s : n ↦ λ^n` is a homomorphism with `deg ∘ s = id`, and the degree is
surjective.
Step 2: `Pic⁰(C) = ker deg`, so the sequence is exact at `Pic⁰(C)` and at `Pic(C)`, and step 1
gives exactness at `ℤ`. The map `x ↦ (deg x, x · s(deg x)⁻¹)` lands in `ℤ × Pic⁰(C)`, is a
homomorphism, and has inverse `(n, y) ↦ s(n) · y`; its first component is the degree and it
restricts to the identity on `Pic⁰(C)`, i.e. the sequence splits. -/
theorem Scheme.Hom.exists_mulEquiv_prod_picZero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] :
    ∃ (P0 : Subgroup C.Pic) (_ : (P0 : Set C.Pic) = f.picZero)
      (e : C.Pic ≃* Multiplicative ℤ × P0),
      (∀ L, (e L).1 = Multiplicative.ofAdd (f.picDegree L)) ∧
      ∀ y : P0, e y = (1, y) :=
  sorry

end AlgebraicGeometry
