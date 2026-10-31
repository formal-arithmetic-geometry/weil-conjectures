/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTensorIso
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Supporting.Tensor.TotalTensorBraiding
import WeilConjectures.SixFunctors.Supporting.Tensor.FixedTensorRepresentativeBraiding

/-! # Braiding on coefficient-sheaf K-flat representatives

Source: Stacks Tags 07A4 and 0FPT.
(blueprint: lem-sf-fixed-coefficient-representative-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.mapHomologicalComplex
attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
namespace WeilConjectures

universe u
open AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local instance 20000] ProEtale.sheafBraidedCategory
attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

/-- The coefficient-sheaf representative has the same inverse-braiding square.
Source: Stacks 07A4 and 0FPT.
Proof: its published component equation identifies it with the generic inverse
localization tensorator. Apply the generic braiding square.
(blueprint: lem-sf-fixed-coefficient-representative-braiding). -/
theorem fixedRepresentativeSwapForCoefficients
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (T : Scheme.{u})
    (S : ObjectProperty (CochainComplex (Sheaf (ProEt.topology T) B) ℤ))
    (hS : ∀ Z, S Z → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Z)
    (b : curriedTensor (DerivedCategory (Sheaf (ProEt.topology T) B)) ≅
      (curriedTensor (DerivedCategory (Sheaf (ProEt.topology T) B))).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding' DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology T) B) (.up ℤ)) K L).hom)
    (P Q : CochainComplex (Sheaf (ProEt.topology T) B) ℤ) (hP : S P) (hQ : S Q) :
    (finiteScalarRepresentativeTensorIso B T S hS).hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
      DerivedCategory.Q.map (totalTensorBraiding Q P).inv ≫
        (finiteScalarRepresentativeTensorIso B T S hS).hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) := by
  rw [finiteScalarRepresentativeTensorIso_hom_app,
    finiteScalarRepresentativeTensorIso_hom_app]
  unfold finiteScalarFixedTensorRepresentativeForCoefficients
  exact fixedRepresentativeSwapGeneric S hS b hb P Q hP hQ

-- Share the already proved coefficient-instance shortcuts used by the canonical map.
attribute [local instance 2000] isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat

attribute [local instance 10000] WeilConjectures.finiteScalarCountableColimits
  WeilConjectures.finiteScalarTensorTotal
  WeilConjectures.finiteScalarIntrinsicCountableColimits
  WeilConjectures.finiteScalarFunctorAdditive WeilConjectures.finiteScalarFunctorEquivalence
  WeilConjectures.finiteScalarFixedTensorPreadditive

-- Use the same inherited data as the native derived tensor and exact-functor APIs.
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms

-- Match the native additive data in the published complex tensor models.
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive

/-- Native scalar representatives have the normalized inverse braiding square.
Source: Stacks 07A4 and 0FPT.
Proof: specialize the proved coefficient-sheaf square to the finite scalar module
category and its chosen flat-term K-flat representatives.
(blueprint: lem-sf-fixed-coefficient-representative-braiding). -/
theorem finiteScalarFixedRepresentativeSwap
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (b : CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) ≅
      (CategoryTheory.MonoidalCategory.curriedTensor
        (DerivedCategory (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))).flip)
    (hb : ∀ K L, HEq ((b.hom.app K).app L)
      (DerivedMonoidal.braiding'
        (DerivedCategory.Qh (C := Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
        (HomotopyCategory.quasiIso (Sheaf (ProEt.topology X)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) (.up ℤ)) K L).hom)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    let r := finiteScalarRepresentativeTensorIso
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
      (finiteScalarFlatRepresentatives X B) (finiteScalarFlatRepresentatives_kFlat X B)
    r.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) ≫
        ((b.inv.app (DerivedCategory.Q.obj Q)).app (DerivedCategory.Q.obj P)) =
      DerivedCategory.Q.map (totalTensorBraiding Q P).inv ≫
        r.hom.app (⟨Q, hQ⟩, ⟨P, hP⟩) := by
  exact fixedRepresentativeSwapForCoefficients
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
    (finiteScalarFlatRepresentatives X B) (finiteScalarFlatRepresentatives_kFlat X B)
    b hb P Q hP hQ

end WeilConjectures
