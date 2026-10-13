/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalCechColumns

/-! # Cancellation of two horizontal Čech deletions

Source: Stacks, Tag 08D1, alternating Čech double complex
(blueprint: lem-sc-principal-cech-horizontal-square).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Two successive alternating restriction maps compose to zero.
Source: Stacks, Tag 08D1, proof, alternating Čech double complex
(blueprint: lem-sc-principal-cech-horizontal-square).

Proof: project to a target subset S of cardinality p+3. Expand both finite sums
and use the product projection equations. A surviving term deletes two distinct
members a and b of S. Pair the deletion order (a,b) with (b,a). Both terms are the
restriction from S minus {a,b} to S, by functoriality of the section presheaf.
If a<b, deleting a lowers the position of b by one, whereas deleting b leaves
the position of a unchanged. Thus the two integer exponents differ by one and
have opposite signs. Terms with an empty twice-erased subset are absent in both
orders. Every surviving ordered pair has a distinct partner, so the sum is zero.
This calculation holds in every coefficient degree. Product projections and
degree evaluations jointly detect equality of chain maps, proving the result.
Negative p and the empty cover have empty target or source rows and give zero
maps automatically. -/
theorem principalCechHorizontal_square
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
    (principalCechHorizontal r f p).app F ≫
      (principalCechHorizontal r f (p + 1)).app F = 0 := by
  sorry

end AlgebraicGeometry
