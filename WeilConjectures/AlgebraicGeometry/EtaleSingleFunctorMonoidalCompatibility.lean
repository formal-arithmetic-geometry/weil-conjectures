/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleFlatSingleTensorCompatibilityData
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly

/-! # Monoidal compatibility of degree-zero etale sheaves

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u uB
open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] SymmetricCategory.toBraidedCategory
attribute [local instance] sheafMonoidalCategory sheafBraidedCategory sheafMonoidalClosed

variable {B : Type uB} [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
  [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
  {X X' : AlgebraicGeometry.Scheme.{u}}

private theorem singleFunctorFlatPairing_eq
    (L M N : Sheaf X.smallEtaleTopology B) (hL : ObjectProperty.flat L)
    (f : L ⊗ M ⟶ N) :
    singleFunctorFlatPairing L M N hL f =
      (singleFunctorObjTensorIso L M hL).hom ≫ (DerivedCategory.singleFunctor _ 0).map f := by
  unfold singleFunctorFlatPairing
  rfl

/-- Canonical flat degree-zero pairings preserve associativity, symmetry and exact pullback.

Source: Stacks Project, Cohomology, Tags 06YQ and 06YU; the canonical tensor/counit
comparisons in `Derived.Invertible` and `Derived.UpperStarMonoidal.Comparison`. -/
theorem etaleSingleFunctor_monoidalCompatibility
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' : AlgebraicGeometry.Scheme.{u}} (v : X' ⟶ X)
    [(upperStar B v).PreservesFlat] :
    EtaleFlatSingleTensorCompatibility (B := B) v := by
  let S := DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology B) 0
  refine ⟨?_, ?_, ?_⟩
  · intro L M N P Q R T hL hM hP f g h k a w
    simp only [singleFunctorFlatPairing_eq, derivedTensor_map_app,
      derivedTensor_obj_map, Category.assoc]
    simpa only [Category.assoc] using
      (flatPairing_associativity_assembly S ObjectProperty.flat
        (fun A C hA ↦ (singleFunctorObjTensorIso A C hA).hom)
        (fun A C E ↦ (derivedTensorAssociator B X (S.obj A) (S.obj C) (S.obj E)).hom)
        (fun {_ _} hA hC ↦ ObjectProperty.prop_tensor hA hC)
        (fun {_ _ _ _} f g hA hA' ↦
          singleFunctorObjTensorIso_hom_naturality f g hA hA')
        (fun A C E hA hC ↦ singleFunctorObjTensorIso_associativity A C E hA hC)
        hL hM hP f g h k a w)
  · intro L M P Q hL hM f g a w
    simp only [singleFunctorFlatPairing_eq]
    rw [← Category.assoc, ← Category.assoc,
      singleFunctorObjTensorIso_symmetry L M hL hM]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [w]
  · intro L M N L' M' N' hL hL' f g b c d w
    let S' := DerivedCategory.singleFunctor (Sheaf X'.smallEtaleTopology B) 0
    let U := upperStar B v
    let D := U.leftDerivedFunctor
    let γ := (singleFunctorCompLeftDerivedUpperStarIso B v).hom
    simp only [singleFunctorFlatPairing_eq, derivedTensor_map_app,
      derivedTensor_obj_map]
    simpa only [Category.assoc] using
      (flatPairing_pullback_assembly S S' U D γ ObjectProperty.flat ObjectProperty.flat
        (fun A C hA ↦ (singleFunctorObjTensorIso A C hA).hom)
        (fun A C hA ↦ (singleFunctorObjTensorIso A C hA).hom)
        (fun A C ↦ Functor.OplaxMonoidal.δ U A C)
        (fun A C ↦ ((leftDerivedUpperStarTensorComparison B v).app (S.obj A)).app (S.obj C))
        (fun {_} hA ↦ Functor.PreservesFlat.flat_obj (F := U) hA)
        (fun {_ _ _ _} b c hA hA' ↦
          singleFunctorObjTensorIso_hom_naturality b c hA hA')
        (fun A C hA ↦ singleFunctorObjTensorIso_pullback v A C hA)
        hL hL' f g b c d w)

end AlgebraicGeometry.Etale
