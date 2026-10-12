/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffinePseudoCoherentLift
import Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree
import Sheaf.AlgebraicGeometry.PerfectHomGap
import Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor

/-! # Extending perfect complexes after adjoining a shifted locally free sheaf

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, Lemma 36.13.6,
lemma-lift-perfect-complex-plus-locally-free
(blueprint: lem-sc-affine-perfect-plus-locally-free).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect object on a quasi-compact open of an affine scheme extends after adjoining
an integer shift of a finite locally free sheaf, whose rank is allowed to vary locally.
Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, Lemma 36.13.6,
lemma-lift-perfect-complex-plus-locally-free
(blueprint: lem-sc-affine-perfect-plus-locally-free).

Proof:
1. Perfectness implies pseudo-coherence and locally finite Tor-amplitude by
   lem-pc-perfect-pseudo-coherent-locally-finite-tor. A finite open cover of U gives
   a common Tor-amplitude interval [a,b]. By lem-sc-affine-pseudo-coherent-lift,
   represent F by the restriction of a bounded-above finite-free complex P on X.
2. Choose r < a and put K = image of the differential from degree r-1 to degree r.
   On U this is the kernel of the next differential. By
   lem-sc-affine-truncation-kernel-finite-locally-free, K restricted to U is finite
   locally free. The complex beginning with K in degree r-1 represents F on U.
   The bounded finite-free tail beginning in degree r is perfect on X. Stupid
   truncation gives the triangle tail|U → F → K|U[1-r] → (tail|U)[1].
3. Since U is quasi-compact and separated, lem-sc-perfect-ext-bounded-qcoh-vanishing
   gives an interval [a',b'] outside which a quasi-coherent target has no maps from F.
   Choose r additionally with r-1 < a'. The sheaf K|U[1-r] is in degree r-1,
   so the map from F to it vanishes.
4. The split-triangle lemma gives tail|U isomorphic to K|U[-r] direct sum F.
   Take the sheaf K|U and the perfect tail as the two existential witnesses.
-/
theorem exists_perfect_lift_plus_finiteLocallyFree
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F) :
    ∃ (r : ℤ) (M : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)),
      M.IsFiniteLocallyFree ∧ ∃ P : schemeDerivedCategory X, IsPerfect X P ∧
        Nonempty
          (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
              (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
              (Modules.overEquiv U)).mapDerivedCategory.obj P ≅
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj M)⟦-r⟧ ⊞ F) :=
  sorry

end AlgebraicGeometry.Scheme
