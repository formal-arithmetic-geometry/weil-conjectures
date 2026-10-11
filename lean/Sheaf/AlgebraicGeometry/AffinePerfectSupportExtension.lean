/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.AlgebraicGeometry.PerfectComplex

/-! # Affine perfect support extension

Source: Stacks Project, Derived Categories of Schemes, Tag 08EK (Lemma 36.13.10)
(blueprint: lem-sc-affine-perfect-support-extension).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect complex on a quasi-compact open of an affine scheme, supported on the
intersection with a closed set with quasi-compact complement, extends after adjoining
its shift to a perfect complex supported on that closed set.
Support is expressed by vanishing of every cohomology stalk off the closed subset.
Restriction uses the canonical equivalence from the localized site to the open subscheme.
Source: Stacks Project, Tag 08EK (blueprint: lem-sc-affine-perfect-support-extension).
Proof: write T as the vanishing set of finitely many functions. By
lem-sc-affine-perfect-plus-shift extend F plus F[1] to X; by
lem-sc-perfect-into-support-on-T replace the functions by powers annihilating F.
Take successive multiplication cones. By lem-sc-affine-support-iterated-cones the
result is perfect, supported on T, and restricts to a sum of shifts of F.
Apply lem-sc-affine-perfect-map-lift to the endomorphism that is zero on the unshifted
F summand and identity on the others. Its lifted source remains supported on T.
The cone of the lifted map is perfect and supported on T by two-of-three, and its
restriction cancels all the unwanted summands, leaving F plus F[1]. -/
theorem exists_perfect_supported_extension (X : Scheme.{u}) [IsAffine X]
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (hFT : ∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf x))) :
    ∃ E : schemeDerivedCategory X, IsPerfect X E ∧
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj E ≅
          F ⊞ F⟦(1 : ℤ)⟧) :=
  sorry

end AlgebraicGeometry.Scheme
