/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerIntegralCriterion

/-! # Unbounded native normalized tower effectivity

Source: current blueprint sk-lem-sp-tower, second paragraph.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)

/-- Unbounded normalized effectivity, retaining the actual native completion and counit.
No constructibility, common bound, or Noetherian hypothesis is imposed.
Source: current blueprint sk-lem-sp-tower.proof.md, second paragraph; Stacks 0940
(blueprint: lem-sp-native-normalized-limit-effectivity).

Proof: represent the strict tower by a complex before replacing it by a simultaneous
flat-term K-flat model. On the tail starting at m, the normalized quotient-error
triangle has right term the constant m-th level and left term its shift with
successor maps multiplied by ell. The product shift on the left is nilpotent of
exponent m+1, so its finite geometric series inverts one minus shift. The left Roos
limit is therefore zero. The right limit is its constant value: diagonal inclusion
and finite partial sums split the product difference map. Perfect reduction commutes
with the exact countable products and the Roos cone. Finite-tail comparison retains
the original m-th projection. The representative normalization of L identifies the
resulting finite comparison with evaluation of L.adjunction.counit. Exact scalar
restriction reflects its invertibility, and derived evaluations jointly detect
isomorphisms of strict towers, giving invertibility of that actual counit.
For completeness, use the original quotient complexes, whose n-th terms are killed
by ell^(n+1), rather than asserting torsion of their K-flat replacements. Write
ell=u*pi^e, e positive. The n-th original row is killed by pi^(e*(n+1)). Apply the
ringed power-torsion theorem with pi. Its signed double-Roos comparison and
augmentation formulas identify its invertible completion unit with the canonical
native one. The section equivalence and equality of the two continuous integer-ring
presentations retain the equality of the native object required by Complete.
Neither part uses a cohomological bound. The zero tower and empty site yield zero;
n=0 is exponent one, and e need not equal one. -/
theorem normalized_limit_effectivity
    (L : Limit l E T D R) (C : spDerivedCoefficientTowers l E T D)
    (hC : IsSpNormalizedTower l E T D C) :
    Complete l E T ((lim l E T D R L).obj C) ∧
      IsIso (L.adjunction.counit.app C) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeTower
