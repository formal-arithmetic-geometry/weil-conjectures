/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalTensor
public import WeilConjectures.SixFunctors.IntegralVerdier.SignedSymmetryNativeRepresentative
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteScalarLocalizedBraiding

/-! # Resolving representative part of finite intrinsic tensor symmetry

This is the flat-term K-flat representative calculation used by the intrinsic
symmetry theorem.
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

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor
attribute [local implicit_reducible] DerivedCategory DerivedMonoidal instCategoryDerivedCategory
  instCategoryDerivedMonoidal toDerivedMonoidal

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.Scheme.sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence
  CategoryTheory.Equivalence.mapDerivedCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

private theorem paste_factor_square
    {D : Type*} [Category D] {A B C E G H : D}
    {f : A ⟶ B} {e : A ⟶ C} {e' : B ⟶ E} {u : C ⟶ E}
    {c : C ⟶ G} {c' : E ⟶ H} {v : G ⟶ H}
    (hf : f ≫ e' = e ≫ u) (hc : u ≫ c' = c ≫ v) :
    f ≫ e' ≫ c' = (e ≫ c) ≫ v := by
  rw [← Category.assoc f e', hf, Category.assoc, hc, Category.assoc]

/-- Realization factorization intertwines the two localized signed tensor squares.
Source: Stacks 06YL and 0FPT.
Proof: compose the factorization naturality equation with the functorial image of
the scalar chain square. The prescribed native map is the intrinsic Koszul swap.
(blueprint: lem-sf-finite-scalar-factorization-braiding). -/
theorem finiteScalarFactorizationBraiding
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ) :
    let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
    let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
    let F := (sfIntrinsicDerivedEquivalence X B).functor
    let e := (sfIntrinsicModuleEquivalence X B).functor.mapDerivedCategoryFactors
    F.map (DerivedCategory.Q.map (totalTensorBraiding Q P).inv) ≫
        e.hom.app ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))).obj (Q, P)) ≫
        DerivedCategory.Q.map ((finiteScalarTotalTensorIso X B).hom.app (Q, P)) =
      (e.hom.app ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))).obj (P, Q)) ≫
        DerivedCategory.Q.map ((finiteScalarTotalTensorIso X B).hom.app (P, Q))) ≫
        intrinsicKoszulSwap X (proEtaleConstantRing X B) (U.obj P) (U.obj Q) := by
  let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
  exact paste_factor_square
    ((sfIntrinsicModuleEquivalence X B).functor.mapDerivedCategoryFactors_hom_naturality
      (totalTensorBraiding Q P).inv)
    (finiteScalarLocalizedBraiding X B P Q)

end WeilConjectures.IntegralVerdier
