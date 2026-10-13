/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionDetectsIso
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Target locality of the single-complex criterion

Source: Stacks Project, Tag 0DJ9, reduction to affine bases.
(blueprint: lem-pc-single-complex-target-locality).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The single-complex criterion for affine bases suffices for arbitrary bases.
The extra premise supplies only the affine-base case, to be proved separately by
source-open induction; it does not assume the original conclusion.
Source: Stacks Project, Tag 0DJ9, first paragraph of the proof.
(blueprint: lem-pc-single-complex-target-locality).

Proof: For a point of S' choose an affine neighbourhood V of its image in S, and an
affine neighbourhood V' of the point contained in g inverse-image V. Restrict f to
f inverse-image V and f' to f' inverse-image V'. Together with g restricted V' → V
and the restriction of g' these form a cartesian square with affine bases. Quasi-
compactness and quasi-separatedness survive this restriction. Restrict K, K' and
phi, using the canonical derived pullback composition comparison; quasi-coherent
cohomology and the stalk condition survive since local rings on opens agree with
the original local rings. Apply the supplied affine-base criterion. Derived direct
image commutes with restriction to inverse-image opens, as does derived pullback.
Their canonical comparisons identify the restricted composite with the local
base-change composite: this follows from naturality of the derived counits in the
adjoint description of the map. Thus the original arrow is invertible on V'.
Apply schemeDerived_isIso_of_openRestriction, since such V' cover S'. Empty bases
are covered by the vacuous locality criterion. No global compactness of S is used.
-/
theorem singleComplexBaseChange_targetLocal
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (h_affine : ∀ {X₀ X₀' S₀ S₀' : Scheme.{u}}
      (f₀ : X₀ ⟶ S₀) (f₀' : X₀' ⟶ S₀') (g₀ : S₀' ⟶ S₀) (g₀' : X₀' ⟶ X₀)
      (sq₀ : IsPullback g₀' f₀' f₀ g₀)
      [IsAffine S₀] [IsAffine S₀'] [QuasiCompact f₀] [QuasiSeparated f₀]
      (K₀ : schemeDerivedCategory X₀) (hK₀ : schemeDerivedQCohProperty X₀ K₀)
      (K₀' : schemeDerivedCategory X₀') (hK₀' : schemeDerivedQCohProperty X₀' K₀')
      (φ₀ : (derivedPullback g₀').obj K₀ ⟶ K₀')
      (h_stalk₀ : SingleComplexBaseChange.StalkCondition f₀ f₀' g₀ g₀' sq₀ K₀ K₀' φ₀),
      IsIso (schemeDerivedBaseChangeMap f₀ f₀' g₀ g₀' sq₀.w K₀ ≫
        (schemeDerivedDirectImage f₀').map φ₀))
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) [QuasiCompact f] [QuasiSeparated f]
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K)
    (K' : schemeDerivedCategory X') (hK' : schemeDerivedQCohProperty X' K')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ) :
    IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map φ) := by sorry

end AlgebraicGeometry
