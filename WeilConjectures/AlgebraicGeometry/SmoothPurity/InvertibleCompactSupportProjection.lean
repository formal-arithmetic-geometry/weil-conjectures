/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison

/-!
# Compact-support projection for an invertible tensor factor

Source: the current blueprint lem-pur-coprojection, test-object Hom calculation
(blueprint: lem-pur-invertible-compact-support-projection).
-/

@[expose] public section
set_option autoImplicit false
universe u u'
open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem projection_at_dualizable
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    {L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)} (hL : IsDualizable L) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app L) := by
  let := (upperStar A f).leftDerivedFunctorMonoidal
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology Y) A)
  exact Adjunction.isIso_rightAdjointProjectionMap_app_app_of_isDualizable
    (derivedUpperStarLowerStarAdjunction A f) (leftDerivedUpperStarTensorComparison A f)
    (fun B C ↦ by
      rw [leftDerivedUpperStarTensorComparison_eq_leftDerivedTensorComparison,
        Functor.leftDerivedFunctorMonoidal_δ]) K hL

private theorem projection_compactification_isIso
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (h : IsIso (((rightDerivedLowerStarProjectionMap A c.g).app
      ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj K)).app L)) :
    IsIso (((projectionMapOfCompactification A c).app K).app L) := by
  have := h
  change IsIso
    (((rightDerivedLowerStarProjectionMap A c.g).app
      ((openImmersionLowerShriek A c.i).mapDerivedCategory.obj K)).app L ≫
      (lowerStar A c.g).rightDerivedFunctor.map
        (((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app
          ((upperStar A c.g).leftDerivedFunctor.obj L)) ≫
      (lowerStar A c.g).rightDerivedFunctor.map
        ((openImmersionLowerShriek A c.i).mapDerivedCategory.map
          (((derivedTensor A X).obj K).map
            ((leftDerivedUpperStarCompactificationIso A c).hom.app L))))
  infer_instance

private theorem dualizable_of_inverse
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A]
    {Y : Scheme.{u}} (L M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (e : L ⊗ M ≅ 𝟙_ _) : IsDualizable L := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory
    (Sheaf (Scheme.ProEt.topology Y) A)
  exact isDualizable_of_tensorIso e ((β_ M L) ≪≫ e)

/-- The canonical compact-support projection is invertible when its second factor has
an inverse. There is no constructibility restriction on its first factor.
Source: blueprint lem-pur-coprojection.proof.md, projection step; the abstract dualizable
projection theorem in WeilConjectures/CategoryTheory/Adjunction/ProjectionMapDualizable.lean
(blueprint: lem-pur-invertible-compact-support-projection).

Proof: The inverse and the braiding make L dualizable. Equip derived pullback with its
strong monoidal structure, whose comonoidal tensorator is the one defining the canonical
proper direct-image projection. The general right-adjoint projection theorem makes that
factor invertible at L. In the compactification formula, the other two factors are the
open-immersion projection isomorphism and the pullback-composition isomorphism, mapped by
functors. Thus every factor of the canonical compact-support projection is invertible. -/
theorem isIso_projectionMap_of_tensor_inverse
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [CategoryTheory.Abelian.HasFunctorialFlatResolution A] [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (L M : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A))
    (e : L ⊗ M ≅ 𝟙_ _) :
    IsIso (((projectionMap A f).app K).app L) := by
  exact projection_compactification_isIso A (HasCompactification.compactification f) K L
    (projection_at_dualizable A _ _ (dualizable_of_inverse A L M e))

end AlgebraicGeometry.ProEtale
