/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleProjectionMates
public import WeilConjectures.AlgebraicGeometry.FiniteProjectionActionLaws
import all WeilConjectures.AlgebraicGeometry.FiniteProjectionActionLaws

/-! # Expanding the target image in projection tensor-action coherence

Source: prop-sf-pf-coherence, finite all-ideal reduction paragraph.
(blueprint: lem-sf-projection-tensor-coordinate-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor

namespace WeilConjectures

private theorem splitProjectionActionImage
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {P Q : B} {X Y Z : A} (a : P ⟶ Q) (b : Q ⟶ F.obj X)
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : P ⟶ F.obj Z)
    (h : a ≫ b ≫ F.map (f ≫ g) = r) :
    r = a ≫ b ≫ F.map f ≫ F.map g := by
  rw [← F.map_comp]
  exact h.symm

/-- The canonical projection tensor-action equation with the two target images separate.
Source: prop-sf-pf-coherence, finite all-ideal reduction paragraph;
lem-pur-finite-projection-action-laws, canonical compactification action identity.
(blueprint: lem-sf-projection-tensor-coordinate-action).

Proof: apply the canonical compactification tensor-action identity to k,q,N.
Expand projectionTensorCoordinateComponent and reverse that identity. Functoriality
of compact support separates the image of the pullback tensor comparison from the
image of the inverse target associator. The elementary splitProjectionActionImage
lemma performs this last categorical step without unfolding the derived functors. -/
theorem projectionTensorCoordinateComponent_tensorAction
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (k : DerivedCategory (Sheaf (ProEt.topology X) A))
    (q N : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    let T := derivedTensor A X
    let U := (upperStar A f).leftDerivedFunctor
    let F := rightDerivedLowerShriekOfCompactification A c
    ((derivedTensor A Y).flip.obj N).map (projectionTensorCoordinateComponent A c k q) ≫
      projectionTensorCoordinateComponent A c ((T.obj k).obj (U.obj q)) N =
    (projectionActionAssociator A Y (F.obj k) q N).hom ≫
      projectionTensorCoordinateComponent A c k (((derivedTensor A Y).obj q).obj N) ≫
      F.map ((T.obj k).map (leftDerivedUpperStarTensorIso A f q N).hom) ≫
      F.map (projectionActionAssociator A X k (U.obj q) (U.obj N)).inv := by
  dsimp only
  dsimp only [projectionTensorCoordinateComponent]
  exact splitProjectionActionImage (rightDerivedLowerShriekOfCompactification A c)
    (projectionActionAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj k) q N).hom
    (((projectionMapOfCompactification A c).app k).app
      (((derivedTensor A Y).obj q).obj N))
    (((derivedTensor A X).obj k).map (leftDerivedUpperStarTensorIso A f q N).hom)
    (projectionActionAssociator A X k
      ((upperStar A f).leftDerivedFunctor.obj q)
      ((upperStar A f).leftDerivedFunctor.obj N)).inv _
    (genericProjectionAction_compactification A f c k q N)


end WeilConjectures
