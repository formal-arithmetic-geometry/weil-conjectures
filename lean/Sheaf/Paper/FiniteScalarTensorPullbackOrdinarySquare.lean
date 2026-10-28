/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J2
-/
module

public import Sheaf.Paper.FiniteScalarOrdinaryPullbackComparison

/-! # The ordinary constant-scalar tensor pullback square

Source: Stacks Tags 00YV and 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-ordinary-square).
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
attribute [local irreducible] SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleOrdinaryTensorPullback
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
  CategoryTheory.Functor.mapHomologicalComplex

namespace WeilConjectures

/-- The scalar realization's ordinary tensor comparison commutes with inverse image.
Source: Stacks, Sites and Sheaves, Tag 00YV; Modules on Sites, Tag 03EL.
(blueprint: lem-sf-finite-scalar-tensor-pullback-ordinary-square).

Proof: precompose both maps by the hom component of the scalar comparison at
M tensor N, an isomorphism. Their source is then intrinsic pullback, so transpose
both maps through the intrinsic pullback adjunction. The inverse mate defining the scalar
comparison is characterized by its adjunction-unit equation. Substitute that
unit equation and the scalar-unit normalization of sfIntrinsicDirectImageComparison.
The ordinary realization tensor comparison is built from the sheafification tensor
isomorphism, which sends the scalar-unit sections of m tensor n to the pair of
scalar-unit sections of m and n. The fixed-coefficient inverse-image tensorator
is the adjoint of tensoring the two inverse-image units. Thus both transposed maps
send every pure tensor m tensor n to the tensor of the two intrinsic inverse-image
unit sections. The characterizing pure-unit equation of
proEtaleOrdinaryTensorPullback gives the same image for the right composite.
The sectionwise tensor universal property followed by the sheafification adjunction
proves equality. This uses only adjunctions and tensor universal properties, so also
covers the zero ring and empty schemes. No complexes or totalization occur here. -/
theorem finiteScalarTensorPullback_ordinary_square
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) :
    (sfIntrinsicModuleEquivalence X R).functor.map
        (Functor.OplaxMonoidal.δ
          (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p) M N) ≫
      (finiteScalarOrdinaryTensorIso X R).hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj M,
         (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} R)) p).obj N) ≫
      (uncurry.obj (proEtaleOrdinaryTensor X (proEtaleConstantRing X R))).map
        (Prod.mkHom ((finiteScalarOrdinaryPullbackComparison R p).inv.app M)
          ((finiteScalarOrdinaryPullbackComparison R p).inv.app N)) =
    (finiteScalarOrdinaryPullbackComparison R p).inv.app (M ⊗ N) ≫
      (proEtaleRingModulePullback p (proEtaleConstantRing Y R)
          (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)).map
        ((finiteScalarOrdinaryTensorIso Y R).hom.app (M, N)) ≫
      (proEtaleOrdinaryTensorPullback p (proEtaleConstantRing Y R)
        (proEtaleConstantRing X R) (proEtaleConstantRingComparison p R)
        ((sfIntrinsicModuleEquivalence Y R).functor.obj M)
        ((sfIntrinsicModuleEquivalence Y R).functor.obj N)).hom := by sorry

end WeilConjectures
