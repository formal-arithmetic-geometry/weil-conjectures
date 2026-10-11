/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away

/-! # Flatness of the lower truncation image on principal opens

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, proof paragraph
invoking Cohomology, Lemma cohomology-lemma-last-one-flat
(blueprint: lem-sc-affine-truncation-kernel-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wU

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- For a bounded-above finite-free complex whose associated sheaf complex on `U` has
Tor amplitude in `[a,b]`, the image
of the differential entering degree `r < a` becomes flat and finitely presented after
localization at every principal open contained in the chosen quasi-compact open.
Source: Stacks Project, Tag 08EG, proof paragraph invoking
`cohomology-lemma-last-one-flat`
(blueprint: lem-sc-affine-truncation-kernel-flat).

Proof:
1. Fix f with D(f) contained in U. Open restriction preserves Tor amplitude
   (Stacks Tag 09U8). Apply lem-pc-affine-tor-amplitude-criterion on Spec(A_f):
   widen the upper bound to max(a,b) if necessary. Tensoring the localized complex
   with any A_f-module N has
   zero cohomology below a. Its image in degree r is K_f, since localization is exact.
2. With N = A_f, vanishing in degree r - 1 identifies the relations of K_f with
   the image of P_f^(r-2). Thus P_f^(r-2) → P_f^(r-1) → K_f → 0 is a finite free
   presentation, so K_f is finitely presented.
3. For every N, vanishing in degree r - 1 and
   lem-pc-module-flat-opcycles-tor-criterion applied with lower bound r show that
   C_f = coker(P_f^(r-1) → P_f^r) is flat. In the exact sequence
   0 → K_f → P_f^r → C_f → 0 both P_f^r and C_f are flat; hence K_f is flat
   by Stacks Tag 00HM (kernel of a surjection between flat modules).
4. The choice of f was arbitrary. These principal opens cover U, giving the
   equivalent flatness and finite-presentation assertion for the associated sheaf on U.
-/
theorem affine_truncation_kernel_flat
    (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (U : (Spec (.of A)).Opens) (hU : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (a b : ℤ) (r : ℤ) (hr : r < a)
    (hamp : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes U.toScheme
          ((@Functor.mapDerivedCategory
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _
            ((SheafOfModules.overFunctor.{u}
                (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
              Equivalence.functor
                (C := SheafOfModules.{u}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
                (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
                (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
                (ComplexShape.up ℤ)).obj P))) G i) :
    ∀ f : A, PrimeSpectrum.basicOpen f ≤ U →
      Module.Flat (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) ∧
        Module.FinitePresentation (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) := by
  sorry

end AlgebraicGeometry
