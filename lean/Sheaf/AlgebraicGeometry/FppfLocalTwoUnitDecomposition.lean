/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q79
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber

/-!
# Fppf local decomposition with three unit conditions

Source: Conrad, Reductive group schemes, printed p.129, after equation (4.3.1), with the
open-polynomial argument giving the version for arbitrary global sections
(blueprint: lem-sfb-fppf-local-two-unit-decomposition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Any two global sections `u, v` admit an fppf covering on which `u = a + b`, with `a`,
`b`, and `1 + b * v` units. No invertibility condition is imposed on `u`, `v`, or `1 + u * v`.
Source: Conrad, Reductive group schemes, printed p.129, after equation (4.3.1); the
open-polynomial argument below removes the condition on `1 + u * v` in that context
(blueprint: lem-sfb-fppf-local-two-unit-decomposition).

Proof plan:
1. On the affine line `p : L → T`, with coordinate `x`, form
   `P = x * (p^*u - x) * (1 + x * p^*v)` and its basic open `j : W = D(P) → L`.
   The affine-space construction supplies `x`, and the basic-open lemma makes `j` an open
   immersion (def-sbc-affine-space, lem-weil-pbc-basic-open-function, def-weil-open-immersion).
2. The affine-line projection is smooth; composition with the open immersion is smooth,
   hence flat and locally of finite presentation (sbc-lem-affine-space-smooth,
   lem-pc-open-immersion-smooth-composition, sbc-lem-smooth-criterion).
3. Over any point `t` choose an affine neighbourhood `Spec R` and put `k = κ(t)`.
   The coefficient map `R[X] → k[X]` has prime kernel, since `k[X]` is a domain. Its
   contraction is the prime of `t`. Each of `X`, `u_bar - X`, and `1 + X * v_bar` is
   nonzero, by its coefficient of degree one or zero, so their product is nonzero.
   The kernel therefore gives a point of `W` over `t`. This proves surjectivity, including
   over finite residue fields (def-weil-affine-spectrum, def-weil-residue-field,
   lem-weil-pbc-polynomial-ring-domain, lem-weil-pbc-basic-open-function).
4. On `W`, the restriction `c` of `P` is a unit. Put `b = x|W`, `a = f^*u - b`, and
   `d = 1 + b * f^*v`, where `f = p ∘ j`. Then `c = b * a * d`, so inverses for `b`, `a`,
   and `d` are respectively `a * d * c⁻¹`, `b * d * c⁻¹`, and `b * a * c⁻¹`.
   Also `f^*u = a + b`. Flatness, local finite presentation and surjectivity make the
   singleton family an fppf covering (lem-weil-pbc-basic-open-function, def-pc-fppf-site).
   The construction still applies to the empty scheme, where surjectivity is vacuous. -/
theorem exists_fppf_two_unit_decomposition (T : Scheme.{u}) (u v : Γ(T, ⊤)) :
    ∃ (I : Type u) (Ti : I → Scheme.{u}) (f : ∀ i, Ti i ⟶ T),
      Presieve.ofArrows Ti f ∈ fppfPrecoverage T ∧
        ∃ (a b : ∀ i, Γ(Ti i, ⊤)), ∀ i,
          (f i).appTop u = a i + b i ∧
            IsUnit (a i) ∧ IsUnit (b i) ∧ IsUnit (1 + b i * (f i).appTop v) := by
  sorry

end AlgebraicGeometry.Scheme
