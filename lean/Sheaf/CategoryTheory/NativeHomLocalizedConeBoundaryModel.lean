/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.CategoryTheory.NativeHomSignedShiftLaws
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # The K-injective native Hom cone boundary

Source: Stacks Project, Tags 08J9 and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

/-- The signed native-Hom cone calculation on a K-injective model.
Source: Stacks Project, Tag 08JC, the cone calculation in lemma-RHom-triangulated
(blueprint: lem-sf-native-hom-localized-cone-boundary-model).

The Hom complex into a K-injective complex identifies the Hom of an ordinary
mapping cone with the inverse rotation of the Hom cone.  The two summand
coordinates determine the first two arrows, and the degree-one signed mate
identifies the connecting arrow.  Applying localization and the evaluation
comparison gives the displayed derived triangle.  This is the model-level
calculation; transport to an arbitrary coefficient is a separate theorem.
-/
theorem nativeHom_localized_cone_boundary_model
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G)
    (I : CochainComplex C ℤ) [I.IsKInjective] :
    let M := DerivedCategory.Q.obj I
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
      (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁) ∈
        distTriang (DerivedCategory C) := by sorry

end AlgebraicGeometry.ProEtale
