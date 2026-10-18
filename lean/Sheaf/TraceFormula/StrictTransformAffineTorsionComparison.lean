/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Mathlib.Algebra.Module.Torsion
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Affine torsion comparison for a Cartier-factor blow-up chart

Source: Stacks Project, Divisors, Tag 080H, proof of
`lemma-strict-transform-different-centers`, algebra reduction paragraph
(blueprint: lem-trf-strict-transform-affine-torsion-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open AlgebraicGeometry

namespace AlgebraicGeometry

/--
The proof is the affine calculation in Tag 080H.  First put
`B = A[I/a]`, `L = A_a`, and `N = M ⊗_A B`.  The chart inclusion `B → L` is
injective, every power of `a` acts bijectively on `L`, and every element of `L`
is a power of `a` times the image of an element of `B`; hence it is a
localization at the powers of `a`.  Tensoring the localization map with `M`
and using `M_a ⊗_L L ≅ M_a` gives a localization map `N → M_a`, with
`m ↦ m ⊗ 1` mapping to `m/1`.  Its kernel is killed by a power of `a`, and
every element of `N` has a power-of-`a` multiple in the image.

For an element killed by `(xa)^n`, choose such a multiple `a^r z = u(m)`.
The kernel bound gives `a^s x^n a^n m = 0`; the hypothesis that
`Γ_(x)(M) = 0` then gives `a^(s+n)m = 0`, so `a^(s+n+r)z = 0`.  This proves
the inclusion from `(xa)`-power torsion to `a`-power torsion.  The reverse
inclusion is immediate from `(xa)^q z = x^q a^q z = 0`.  The convention
allowing exponent zero in `Submodule.powTorsion` agrees with the positive
exponent convention in the statement, since an exponent-zero witness forces
the element itself to be zero.

Source: Stacks Project, Divisors, Tag 080H, proof of
`lemma-strict-transform-different-centers`, algebra reduction paragraph
(blueprint: lem-trf-strict-transform-affine-torsion-comparison).
-/
theorem strictTransform_affine_torsion_comparison
    {A : Type u} [CommRing A] (I : Ideal A) (a x : A) (ha : a ∈ I)
    (hx : x ∈ nonZeroDivisors A) (M : Type v) [AddCommGroup M] [Module A M]
    (hM : Submodule.powTorsion A M x = ⊥) :
    Submodule.powTorsion A (TensorProduct A M (AffineBlowup.chartRing I a)) a =
      Submodule.powTorsion A (TensorProduct A M (AffineBlowup.chartRing I a)) (x * a) := by
  sorry

end AlgebraicGeometry
