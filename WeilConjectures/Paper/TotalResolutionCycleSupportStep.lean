/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u

namespace WeilConjectures.DerivedTotalResolution

variable {R : Type u} [Ring R]

/-- Remove one specified outer column of a finitely supported total cycle.
Source: Stacks Project, Homology, Tag 09IZ, proof, the two boundary corrections.
(blueprint: aux-total-resolution-cycle-support-step)

Proof. Set s=r+1 and q=n+s. Project the total cocycle equation to column -s.
Since no column to its left occurs, the component x_s is a vertical cycle.
Projection to column 1-s shows that the horizontal image of x_s is a vertical
boundary, up to the total sign. Its homology class is thus in the kernel of
H^q(K.X(-s)) -> H^q(K.X(1-s)). Apply h_homology at p=-s-1 (< -1) to lift this
class from H^q(K.X(-s-1)), and choose a vertical cycle representative a there.
Its total degree is n-1. Subtract the appropriately signed total boundary of
a. Its vertical boundary vanishes; its horizontal boundary changes only column
-s, making that component a vertical boundary. Choose a primitive t in vertical
degree q-1 in column -s, and subtract its signed total boundary. This kills
column -s and changes only column 1-s in addition. The difference remains a
cycle because the square of the total differential is zero. Call it z' and
write its remaining coordinates as x' from column 0 through -r. Let b be the
sum of these two signed corrections. Then z = z' + d(b), as asserted. No
iteration, column-zero identification, or choice of descent measure is used. -/
theorem total_resolution_cycle_support_step
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (n : ℤ)
    (h_homology : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.homologyMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.homologyMap (K.d (p + 1) (p + 2)) q).hom)
    (r : ℕ) (z : (K.total (ComplexShape.up ℤ)).cycles n)
    (x : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)))
    (hx : (K.total (ComplexShape.up ℤ)).iCycles n z =
      ∑ i ∈ Finset.range (r + 1 + 1),
        K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x i)) :
    ∃ z' : (K.total (ComplexShape.up ℤ)).cycles n,
      ∃ x' : ∀ i : ℕ, (K.X (-(i : ℤ))).X (n + (i : ℤ)),
      ∃ b : (K.total (ComplexShape.up ℤ)).X (n - 1),
        (K.total (ComplexShape.up ℤ)).iCycles n z' =
          (∑ i ∈ Finset.range (r + 1),
            K.ιTotalOrZero (ComplexShape.up ℤ) (-(i : ℤ)) (n + (i : ℤ)) n (x' i)) ∧
        (K.total (ComplexShape.up ℤ)).iCycles n z =
          (K.total (ComplexShape.up ℤ)).iCycles n z' +
            (K.total (ComplexShape.up ℤ)).d (n - 1) n b := by
  sorry

end WeilConjectures.DerivedTotalResolution
