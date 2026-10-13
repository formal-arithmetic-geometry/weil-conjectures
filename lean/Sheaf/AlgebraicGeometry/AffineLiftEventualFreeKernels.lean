/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.AffineTruncationKernelFiniteLocallyFree
import Sheaf.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import Sheaf.AlgebraicGeometry.AffineFiniteFreeSheafComplexLift
import Sheaf.AlgebraicGeometry.QuasiCompactFiniteTorDimension

/-! # Eventual finite locally free kernels of an affine lift

Source: Stacks Project, Tag 08EG, the common Tor bound and kernel paragraphs.
(blueprint: lem-sc-affine-lift-eventual-free-kernels).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- The restricted finite-free lift is exact in all sufficiently low degrees, and
its outgoing kernels in those degrees are finite locally free.
Source: Stacks Project, Tag 08EG, first two paragraphs of the proof of Lemma 36.13.6.
(blueprint: lem-sc-affine-lift-eventual-free-kernels).

Proof: Perfectness gives locally finite Tor dimension. Choose finitely many of the
Tor-amplitude neighbourhoods covering the quasi-compact open and take the minimum
lower endpoint a and maximum upper endpoint b. Tensor cohomology is local, hence
the represented object has Tor amplitude [a,b] on the entire open. In particular
its ordinary cohomology vanishes below a, by tensoring with the structure sheaf.
Use the affine identification X = Spec Gamma(X) and termwise tilde/sections to
lift K to a bounded-above finite-free module complex; the finite-free lift theorem
supplies this complex and its comparison. Exact restriction and the given derived
representation transfer the same Tor bound to that model. For every r ≤ a-1 the
affine truncation-kernel theorem identifies the restricted image of d^(r-1) with
the kernel of d^r, and makes this image finite locally free. Transport that property
along the termwise comparison and the affine scheme equivalence. Ordinary
cohomology vanishing gives exactness in every degree i ≤ r. The choice N = a-1
is independent of r. For the empty open take any interval; all restricted objects
are zero, and the kernel is the rank-zero locally free sheaf.
-/
theorem affine_lift_eventual_free_kernels
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (K.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r))))
    (hrep : Nonempty
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅ F)) :
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    ∃ N : ℤ, ∀ r : ℤ, r ≤ N →
      (∀ i : ℤ, i ≤ r → ((R.mapHomologicalComplex (.up ℤ)).obj K).ExactAt i) ∧
      (kernel (R.map (K.d r (r + 1)))).IsFiniteLocallyFree := by
  sorry

end AlgebraicGeometry.Scheme
