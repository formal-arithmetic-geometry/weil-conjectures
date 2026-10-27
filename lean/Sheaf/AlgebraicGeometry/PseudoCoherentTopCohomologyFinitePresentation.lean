/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q142
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTopCancellation

/-! # Finite presentation of the top cohomology of a pseudo-coherent complex

Source: Stacks Project, Cohomology of Sheaves, Tag 08DN,
`lemma-finite-cohomology`, part (2), with `m = n - 1`.
(blueprint: lem-sfb-pseudocoherent-top-cohomology-fp)
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- If a pseudo-coherent complex has zero cohomology above `n`, its cohomology
sheaf in degree `n` is finitely presented. The scheme need not be coherent or Noetherian.

Source: Stacks Project, Cohomology of Sheaves, Tag 08DN,
`lemma-finite-cohomology`, part (2), with `m = n - 1`.
(blueprint: lem-sfb-pseudocoherent-top-cohomology-fp)

Proof:
1. Fix a point x. By `IsPseudoCoherent` (def-pur-pseudo-coherent-complex), choose
   an open neighbourhood U and a bounded-above finite free complex P representing
   the restriction of K. Exact open restriction
   (`open_restriction_adjunction_exact`, lem-sc-derived-open-restriction-adjunction-exact)
   identifies its cohomology with the restriction of the cohomology of K, so it
   vanishes above n. Its terms are finite locally free
   (def-sc-finite-locally-free-sheaf). If N is an upper bound, put r = max(N, n).
2. Induct on the nonnegative integer r - n. When r > n, apply
   `Modules.exists_local_finiteLocallyFree_top_cancellation`
   (lem-sfb-finite-locally-free-top-cancellation) at x. After shrinking, it gives
   a quasi-isomorphic finite locally free complex zero above r - 1. Exact restriction
   preserves vanishing above n and the quasi-isomorphism preserves cohomology.
   Continue until the representative Q is zero above n; the case r = n needs no step.
3. Shrink again to trivialize Q in degrees n - 1 and n, with finite ranks a and b.
   Since Q in degree n + 1 is zero, its degree-n cohomology is the cokernel of
   the differential from the free module of rank a to the free module of rank b.
   It is the restriction of the degree-n cohomology of K by exact restriction.
   This is a finite presentation at x in the sense of
   `SheafOfModules.IsFinitePresentation` (def-weil-pbc-module-finite-type-presentation).
   Since x was arbitrary, the cohomology sheaf is finitely presented. On the empty
   scheme the local condition is vacuous. -/
theorem isFinitePresentation_homology_of_isPseudoCoherent
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedCategory X) (hK : X.IsPseudoCoherent K) (n : ℤ)
    (hvanish : ∀ i : ℤ, n < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj K)) :
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.Scheme
