/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P6
-/
module

public import Sheaf.CategoryTheory.NativeHomLocalizedConeBoundaryModel
public import Mathlib.CategoryTheory.Triangulated.Opposite.Functor

/-! # Transport of the native Hom cone boundary

Source: Stacks Project, Tags 08J9 and 08JC.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

/-- Naturality transports the K-injective cone boundary to any coefficient.
Source: Stacks Project, Tag 08JC, the evaluation-characterized transport in
lemma-RHom-triangulated (blueprint: lem-sf-native-hom-localized-cone-boundary-transport).

For an isomorphism from the localization of a K-injective complex to a derived
object, naturality of the evaluation comparison and of the signed source mate
identifies the model triangle with the triangle formed using that object.  The
statement records only this triangle isomorphism; distinguishedness is supplied
by the model theorem and the main cone-boundary theorem.
-/
theorem nativeHom_localized_cone_boundary_transport
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {E G : CochainComplex C ℤ} (f : E ⟶ G)
    (I : CochainComplex C ℤ) [I.IsKInjective]
    (M : DerivedCategory C) (e : DerivedCategory.Q.obj I ≅ M) :
    let M₀ := DerivedCategory.Q.obj I
    let H₀ := MonoidalClosed.internalHom.flip.obj M₀
    let H := MonoidalClosed.internalHom.flip.obj M
    let T := (triangleOpEquivalence (DerivedCategory C)).functor.obj
      (op (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)))
    Nonempty (Triangle.mk (H₀.map T.mor₁) (H₀.map T.mor₂)
      (H₀.map T.mor₃ ≫ siteHomSignedSourceComponent M₀ 1 T.obj₁) ≅
      Triangle.mk (H.map T.mor₁) (H.map T.mor₂)
        (H.map T.mor₃ ≫ siteHomSignedSourceComponent M 1 T.obj₁)) := by sorry

end AlgebraicGeometry.ProEtale
