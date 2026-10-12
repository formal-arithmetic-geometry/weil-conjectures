/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
import Sheaf.AlgebraicGeometry.AffinePerfectMapLift
import Sheaf.AlgebraicGeometry.AffinePerfectPlusLocallyFree
import Sheaf.AlgebraicGeometry.PerfectTwoOutOfThree

/-! # Affine perfect extension after adjoining a shift

Source: literature/stacks-project/perfect.tex, Tag 08EI (Lemma 36.13.8)
(blueprint: lem-sc-affine-perfect-plus-shift).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
/-- If `X` is affine and `U` is a quasi-compact open, every perfect complex on `U`
becomes the restriction of a perfect complex on `X` after adjoining its shift by one.
Source: Stacks Project, Tag 08EI (Lemma 36.13.8)
(blueprint: lem-sc-affine-perfect-plus-shift).

Proof: use `lem-sc-affine-perfect-plus-locally-free` to extend
`𝓕[-r] ⊕ F`; lift the projection onto the first summand by
`lem-sc-affine-perfect-map-lift`; the cone of the lifted map is perfect by
`lem-pc-perfect-two-out-of-three`, and its restriction is `F ⊕ F[1]` by the
cone computation in the source proof. -/
theorem exists_perfect_restrict_iso_directSum_shift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme)
    (hF : Scheme.IsPerfect U.toScheme F) :
    ∃ E : schemeDerivedCategory X,
      Scheme.IsPerfect X E ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj E ≅
          F ⊞ F⟦(1 : ℤ)⟧) := by
  sorry
end AlgebraicGeometry
