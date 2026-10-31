/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarOrdinaryPullbackComparison
public import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarRepresentativeTotalRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealizationSummand
import WeilConjectures.SixFunctors.Finite.Scalar.FiniteScalarIntrinsicTensorSummand

/-! The right scalar tensor pullback composite on a summand.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-right-summand).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
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

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

universe a v
open CategoryTheory.Limits

section
variable {C E F : Type*} [Category C] [Category E] [Category F]
private theorem paste_right (G : C ⥤ F) (U : C ⥤ E) (B : E ⥤ F)
    (c : G ⟶ U ⋙ B) {x T : C} {d D : E} {w W : F}
    (j : x ⟶ T) (t : U.obj T ⟶ D) (s : B.obj D ⟶ W)
    (dt : U.obj x ⟶ d) (ds : B.obj d ⟶ w) (jU : d ⟶ D) (jB : w ⟶ W)
    (ht : U.map j ≫ t = dt ≫ jU) (hs : B.map jU ≫ s = ds ≫ jB) :
    G.map j ≫ c.app T ≫ B.map t ≫ s = (c.app x ≫ B.map dt ≫ ds) ≫ jB := by
  rw [reassoc_of% (c.naturality j)]
  rw [← B.map_comp_assoc, ht, B.map_comp, Category.assoc, hs]
  simp only [Category.assoc]
end

/-- The right total composite on a coproduct summand is its ordinary composite.
Source: Stacks Tag 07A4; the native total-comparison injection identities.
(blueprint: lem-sf-finite-scalar-tensor-pullback-right-summand).

Proof: apply the defining tensor-comparison formula on each injection. Naturality of the
ordinary scalar comparison moves it before the injection. The realization formula and intrinsic
inverse-total formula identify the remaining two factors. Functoriality and associativity paste
these equalities. -/
theorem finiteScalarTensorPullback_right_summand
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) ⋙
      (sfIntrinsicModuleEquivalence X R).functor).map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h) ≫
    (((finiteScalarComplexPullbackComparison R p).inv.app
        ((finiteScalarRepresentativeTotalTensor
          (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R)))).obj (P, Q)) ≫
      ((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).map ((finiteScalarRepresentativeTotalRealization R Y).app (P, Q)) ≫
      (finiteScalarIntrinsicComplexTensorPullback R p).app
        (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj P,
         ((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ)).obj Q)).f
      n) =
    ((finiteScalarOrdinaryPullbackComparison R p).inv.app ((P.X a) ⊗ (Q.X b)) ≫
      (proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).map
        ((finiteScalarOrdinaryTensorIso Y R).hom.app ((P.X a), (Q.X b))) ≫
      (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
        ((sfIntrinsicModuleEquivalence Y R).functor.obj (P.X a))
        ((sfIntrinsicModuleEquivalence Y R).functor.obj (Q.X b))).hom) ≫
      CochainComplex.ιMapBifunctor
      (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).obj (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj P))
      (((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
        (.up ℤ)).obj (((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex
          (.up ℤ)).obj Q)) (proEtaleOrdinaryTensor X (proEtaleConstantRing X R)) a b n h := by
  let A := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p
  let V := (sfIntrinsicModuleEquivalence X R).functor
  let U := (sfIntrinsicModuleEquivalence Y R).functor
  let B := proEtaleRingModulePullback p (proEtaleConstantRing Y R)
    (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
  let AP := (A.mapHomologicalComplex (.up ℤ)).obj P
  let AQ := (A.mapHomologicalComplex (.up ℤ)).obj Q
  let UP := (U.mapHomologicalComplex (.up ℤ)).obj P
  let UQ := (U.mapHomologicalComplex (.up ℤ)).obj Q
  let VAP := (V.mapHomologicalComplex (.up ℤ)).obj AP
  let VAQ := (V.mapHomologicalComplex (.up ℤ)).obj AQ
  let BUP := (B.mapHomologicalComplex (.up ℤ)).obj UP
  let BUQ := (B.mapHomologicalComplex (.up ℤ)).obj UQ
  let j := CochainComplex.ιMapBifunctor P Q (curriedTensor _) a b n h
  let tU := (finiteScalarRepresentativeTotalRealization R Y).app (P, Q)
  let tB := (finiteScalarIntrinsicComplexTensorPullback R p).app (UP, UQ)
  unfold finiteScalarComplexPullbackComparison
  change (A ⋙ V).map j ≫ (finiteScalarOrdinaryPullbackComparison R p).inv.app
      ((CochainComplex.mapBifunctor P Q (curriedTensor _)).X n) ≫
      B.map (tU.f n) ≫ tB.f n = _
  refine paste_right (A ⋙ V) U B (finiteScalarOrdinaryPullbackComparison R p).inv
    j (tU.f n) (tB.f n)
    ((finiteScalarOrdinaryTensorIso Y R).hom.app (P.X a, Q.X b))
    ((proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
      (U.obj (P.X a)) (U.obj (Q.X b))).hom)
    (CochainComplex.ιMapBifunctor UP UQ (proEtaleOrdinaryTensor Y
      (proEtaleConstantRing Y R)) a b n h)
    (CochainComplex.ιMapBifunctor BUP BUQ (proEtaleOrdinaryTensor X
      (proEtaleConstantRing X R)) a b n h) ?_ ?_
  · exact finiteScalarRepresentativeTotalRealization_ι R Y P Q a b n h
  · exact finiteScalarIntrinsicComplexTensorPullback_ι R p UP UQ a b n h

end WeilConjectures
