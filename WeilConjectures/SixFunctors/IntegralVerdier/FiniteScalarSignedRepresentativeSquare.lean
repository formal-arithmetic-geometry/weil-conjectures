/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorRealization
public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorResolution
public import WeilConjectures.SixFunctors.Supporting.Tensor.TotalTensorBraiding
public import WeilConjectures.SixFunctors.IntegralVerdier.SignedSymmetryNativeRepresentative
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteScalarFactorizationBraiding

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

private theorem finish_representative_square
    {D : Type*} [Category D] {A B C E G H I J : D}
    {f : A ⟶ B} {e : A ⟶ C} {e' : B ⟶ E} {c : C ⟶ G} {c' : E ⟶ H}
    {a : G ⟶ I} {a' : H ⟶ J} {v : G ⟶ H} {s : I ⟶ J}
    (hc : f ≫ e' ≫ c' = (e ≫ c) ≫ v) (hs : a ≫ s = v ≫ a') :
    f ≫ e' ≫ c' ≫ a' = (e ≫ c ≫ a) ≫ s := by
  calc
    f ≫ e' ≫ c' ≫ a' = (f ≫ e' ≫ c') ≫ a' := by simp only [Category.assoc]
    _ = ((e ≫ c) ≫ v) ≫ a' := by rw [hc]
    _ = e ≫ c ≫ (v ≫ a') := by simp only [Category.assoc]
    _ = e ≫ c ≫ (a ≫ s) := by rw [← hs]
    _ = (e ≫ c ≫ a) ≫ s := by simp only [Category.assoc]

/-- The realized signed swap commutes with the localized scalar comparison.
Source: Stacks 06YL and 0FPT.
Proof: paste factorization naturality, the localized total braiding square, and
identification of the supplied signed representative with the native braiding.
(blueprint: lem-sf-finite-scalar-signed-representative-square). -/
theorem finiteScalarSignedRepresentativeSquare
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B))) ℤ)
    (hP : finiteScalarFlatRepresentatives X B P)
    (hQ : finiteScalarFlatRepresentatives X B Q) :
    let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
    let U := (sfIntrinsicModuleEquivalence X B).functor.mapHomologicalComplex (.up ℤ)
    let F := (sfIntrinsicDerivedEquivalence X B).functor
    let e := (sfIntrinsicModuleEquivalence X B).functor.mapDerivedCategoryFactors
    let hUP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B P hP).1
    let hUQ := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).mpr
      (finiteScalarPreservesRepresentatives X B Q hQ).1
    F.map (DerivedCategory.Q.map (totalTensorBraiding Q P).inv) ≫
        e.hom.app ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))).obj (Q, P)) ≫
        DerivedCategory.Q.map ((finiteScalarTotalTensorIso X B).hom.app (Q, P)) ≫
        (intrinsicRepresentative.{u} X (proEtaleConstantRing X B) a
          (U.obj Q) (U.obj P) hUQ hUP).hom =
      (e.hom.app ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} B)))).obj (P, Q)) ≫
        DerivedCategory.Q.map ((finiteScalarTotalTensorIso X B).hom.app (P, Q)) ≫
        (intrinsicRepresentative.{u} X (proEtaleConstantRing X B) a
          (U.obj P) (U.obj Q) hUP hUQ).hom) ≫
        (s.swap (DerivedCategory.Q.obj (U.obj P)) (DerivedCategory.Q.obj (U.obj Q))).hom := by
  let : HasDerivedCategory.{u + 2}
      (proEtaleRingModules X (proEtaleConstantRing X B)) := HasDerivedCategory.standard _
  exact finish_representative_square
    (finiteScalarFactorizationBraiding X B P Q)
    (finiteScalarSignedRepresentativeNative X B a s P Q hP hQ)

end WeilConjectures.IntegralVerdier
