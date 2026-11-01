/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTensorIso
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorSharedRepresentativeEquation

/-! # Intrinsic presentation coordinates for the shared representative equation

Source: Stacks 07A4 and the constructed representative normalization.
(blueprint: lem-sf-finite-intrinsic-tensor-representative-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
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

attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures.IntegralVerdier

attribute [local implicit_reducible] finiteIntrinsicTensorModel
  finiteScalarRepresentativeTotalTensor
attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

/-- The shared representative equation restricted to an intrinsic K-flat presentation.
Source: Stacks 07A4; the representative normalization already proved in the project.
Proof: specialize the shared equation to the restriction of the supplied presentation.
Its tensor and representative components are exactly the supplied components.
(blueprint: lem-sf-finite-intrinsic-tensor-representative-equation). -/
theorem intrinsic_normalization
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
    let F := (sfIntrinsicDerivedEquivalence X B).functor
    let e := (sfIntrinsicModuleEquivalence X B).functor.mapDerivedCategoryFactors
    let r := finiteScalarRepresentativeTensorIso
      (ModuleCat.{u + 1} (ULift.{u + 1} B)) X
      (finiteScalarFlatRepresentatives X B) (finiteScalarFlatRepresentatives_kFlat X B)
    let t := finiteScalarTensorRealization X B (finiteIntrinsicTensorModel X B a)
    let hUP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B P hP).1
    let hUQ := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B Q hQ).1
    F.map (r.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) ≫
        (t.hom.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        a.tensor.map (Prod.mkHom (e.hom.app P) (e.hom.app Q)) =
      e.hom.app ((finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))).obj (P, Q)) ≫
        DerivedCategory.Q.map ((finiteScalarTotalTensorIso X B).hom.app (P, Q)) ≫
        a.representative.hom.app (⟨U.obj P, hUP⟩, ⟨U.obj Q, hUQ⟩) := by
  exact finiteScalarTensorSharedRepresentative_normalization B
    (finiteIntrinsicTensorModel X B a) P Q hP hQ

end WeilConjectures.IntegralVerdier
