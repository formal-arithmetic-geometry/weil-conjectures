/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison

/-! # Intrinsic inverse-total tensor comparison on coproduct summands

Source: Stacks Tag 07A4 and the native total-complex desc construction.
(blueprint: lem-sf-finite-scalar-intrinsic-tensor-summand).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
open CategoryTheory.Functor
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
attribute [local instance 2000] SymmetricCategory.toBraidedCategory Abelian.toPreadditive
attribute [local instance 4000] Preadditive.preadditiveHasZeroMorphisms
attribute [local instance 30000] SheafOfModules.instPreadditive
  HomologicalComplex.instPreadditive CategoryTheory.functorCategoryPreadditive
  Preadditive.preadditiveHasZeroMorphisms Functor.preservesZeroMorphisms_of_additive
attribute [local irreducible] sfIntrinsicModuleEquivalence
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

universe a v
open CategoryTheory.Limits

private theorem intrinsicTensor_ι {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (P Q : CochainComplex (proEtaleRingModules Y R) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (proEtaleRingModulePullback f R S c).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y R) a b n h) ≫
      (proEtaleTensorPullbackTotalIso f R S c P Q).inv.f n =
    (proEtaleOrdinaryTensorPullback f R S c (P.X a) (Q.X b)).hom ≫
      CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
        (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X S) a b n h := by
  apply (cancel_mono ((proEtaleTensorPullbackTotalIso f R S c P Q).hom.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.inv_hom_id,
    HomologicalComplex.id_f]
  simp only [proEtaleTensorPullbackTotalIso, asIso_hom, proEtaleTensorPullbackTotal,
    tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  simp only [proEtaleOrdinaryTensor]
  erw [Category.comp_id]

/-- The intrinsic inverse-total tensor comparison has the ordinary pullback map on summands.
Source: Stacks, Cohomology on Sites, Tag 07A4; the coproduct-desc definition of
`proEtaleTensorPullbackTotal`.
(blueprint: lem-sf-finite-scalar-intrinsic-tensor-summand).

Proof: postcompose by the hom component of the total tensor pullback isomorphism.
Its inverse cancels on the left. On the right the injection followed by that hom
is the defining coproduct-desc component, namely the inverse ordinary tensor
comparison followed by the pulled-back injection. Cancel the ordinary tensor
isomorphism, then use the identity law. Specialize this calculation to the
constant coefficient rings and the specified intrinsic complex comparison. -/
theorem finiteScalarIntrinsicComplexTensorPullback_ι (R : Type u) [CommRing R] [Finite R]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex (proEtaleRingModules Y (proEtaleConstantRing Y R)) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    (proEtaleRingModulePullback p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
      (proEtaleConstantRingComparison p R)).map
        (CochainComplex.ιMapBifunctor P Q (proEtaleOrdinaryTensor Y
          (proEtaleConstantRing Y R)) a b n h) ≫
      ((finiteScalarIntrinsicComplexTensorPullback R p).app (P, Q)).f n =
    (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
        (P.X a) (Q.X b)).hom ≫
      CochainComplex.ιMapBifunctor
        (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
          (.up ℤ)).obj P)
        (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
          (.up ℤ)).obj Q)
        (proEtaleOrdinaryTensor X (proEtaleConstantRing X R)) a b n h := by
  simpa only [finiteScalarIntrinsicComplexTensorPullback_app] using
    intrinsicTensor_ι p (proEtaleConstantRing Y R) (proEtaleConstantRing X R)
      (proEtaleConstantRingComparison p R) P Q a b n h

end WeilConjectures
