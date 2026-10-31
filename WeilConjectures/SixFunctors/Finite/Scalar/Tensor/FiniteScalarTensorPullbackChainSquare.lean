/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorPullbackChainSquareComponent
import WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # The scalar tensor square before localization

Source: Stacks Tags 00YV and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-pullback-chain-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
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
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

/-- Fixed-scalar inverse image preserves flat-term K-flat representatives.
Source: Stacks Tag 0G7E and preservation of flat sheaves by pro-etale inverse image.
(blueprint: lem-sf-finite-scalar-tensor-pullback-chain-square).

Proof: inverse image preserves flat sheaves and colimits. Apply the general
flat-term K-flat preservation theorem and check flatness degree by degree. -/
theorem finiteScalarPullback_preservesRepresentatives
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (hP : finiteScalarFlatRepresentatives Y R P) :
    finiteScalarFlatRepresentatives X R
      (((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
        (.up ℤ)).obj P) := by
  exact ⟨(ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).kFlat_map_of_flat_terms
    P hP.1 hP.2, fun n ↦ Functor.PreservesFlat.flat_obj
      (F := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) (hP.2 n)⟩

/-- The signed ordinary tensor square for the scalar inverse image commutes.
No derived category or tensor model occurs here.

Source: Stacks Tags 07A4 and 07A6, ordinary tensor square and signed totalization.
(blueprint: lem-sf-finite-scalar-tensor-pullback-chain-square).

Proof: use the ordinary inverse mate's adjunction-unit equation and the section
normalization of sfIntrinsicDirectImageComparison. Together with the scalar-unit
normalization of finiteScalarOrdinaryTensorIso, these show that both ordinary
composites send a balanced pure tensor to the tensor of the two inverse-image unit
sections. The tensor universal property followed by sheafification proves equality.
For complexes test each total-degree map on the coproduct injection of bidegree
(a,b). The defining summand equations of the two total tensor comparisons reduce
the equality to that ordinary square. The same Koszul signs occur on both sides,
so these degree maps give the stated equality of chain maps. This proof applies
to unbounded complexes, zero rings, zero complexes, and empty schemes.
-/
theorem finiteScalarTensorPullback_chain_square
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    tensorOrdinaryPullbackLaw
      (finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))))
      (finiteScalarRepresentativeTotalTensor
        (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} R))))
      (uncurry.obj ((proEtaleOrdinaryTensor Y (proEtaleConstantRing Y R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)))
      (uncurry.obj ((proEtaleOrdinaryTensor X (proEtaleConstantRing X R)).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ)))
      ((sfIntrinsicModuleEquivalence Y R).functor.mapHomologicalComplex (.up ℤ))
      ((sfIntrinsicModuleEquivalence X R).functor.mapHomologicalComplex (.up ℤ))
      ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).mapHomologicalComplex
        (.up ℤ))
      ((proEtaleRingModulePullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).mapHomologicalComplex
          (.up ℤ))
      (finiteScalarComplexPullbackComparison R p)
      (finiteScalarFixedComplexTensorPullbackForCoefficients
        (ModuleCat.{u + 1} (ULift.{u + 1} R)) p)
      (finiteScalarRepresentativeTotalRealization R Y)
      (finiteScalarRepresentativeTotalRealization R X)
      (finiteScalarIntrinsicComplexTensorPullback R p) := by
  intro P Q
  apply HomologicalComplex.hom_ext _ _
  intro n
  exact finiteScalarTensorPullback_chain_square_component R p P Q n

end WeilConjectures
