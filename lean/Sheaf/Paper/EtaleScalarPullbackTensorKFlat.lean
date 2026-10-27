/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.ExceptionalCoefficientMaps

/-! K-flat representative form of scalar/pullback tensor compatibility.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-kflat-representative).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The normalized scalar/pullback tensor equation on flat-term K-flat representatives.
This is the representative calculation underlying the unrestricted derived statement.
Source: Stacks 07A4, 0G7E and 0GL6
(blueprint: lem-pur-etale-scalar-pullback-tensor-kflat-representative).
Proof: on homogeneous local pure tensors, both composites send an iterated tensor to the
same pair of pulled-back factors; balancing and the signed total-complex construction
identify the maps, and sheafification preserves the equality. -/
theorem etaleScalarPullback_tensor_kFlat
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P R : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hR : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat R)
    (_hPflat : ∀ n : ℤ, ObjectProperty.flat (P.X n))
    (_hRflat : ∀ n : ℤ, ObjectProperty.flat (R.X n)) :
    (scalarPullbackIso φ f).hom.app
        (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj R) ≫
      (scalarExtension φ X).map
        (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R)) ≫
      (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
          (DerivedCategory.Q.obj P),
          (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
            (DerivedCategory.Q.obj R)) =
    (upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.map
        ((ExceptionalCoefficients.tensorIso φ Y).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj R)) ≫
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} B) f).app
        ((scalarExtension φ Y).obj (DerivedCategory.Q.obj P))).app
          ((scalarExtension φ Y).obj (DerivedCategory.Q.obj R))) ≫
      ((scalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj P) ⊗ₘ
        (scalarPullbackIso φ f).hom.app (DerivedCategory.Q.obj R)) := by
  sorry

end AlgebraicGeometry.Etale
