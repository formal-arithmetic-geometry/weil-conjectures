/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorSummandDiagram
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramFixed
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramRealization
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramMap
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramOrdinary
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorDiagramRight

/-! Pasting the scalar tensor summand diagram.

Source: Stacks Tags 00YV, 07A4 and 07A6.
(blueprint: lem-sf-finite-scalar-tensor-diagram-commutes).
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

attribute [local implicit_reducible] finiteScalarRepresentativeTotalTensor

universe a v

private theorem diagram_commutes {C : Type a} [Category.{v} C]
    (D : FiniteScalarTensorSummandDiagram C)
    (h1 : D.j0 ≫ D.l1 = D.a1 ≫ D.j1)
    (h2 : D.j1 ≫ D.l2 = D.a2 ≫ D.j2)
    (h3 : D.j2 ≫ D.l3 = D.a3 ≫ D.j3)
    (ho : D.a1 ≫ D.a2 ≫ D.a3 = D.ordinaryRight)
    (hr : D.j0 ≫ D.right = D.ordinaryRight ≫ D.j3) :
    D.j0 ≫ D.l1 ≫ D.l2 ≫ D.l3 = D.j0 ≫ D.right := by
  have hl : D.j0 ≫ D.l1 ≫ D.l2 ≫ D.l3 = (D.a1 ≫ D.a2 ≫ D.a3) ≫ D.j3 := by
    rw [← Category.assoc D.j0 D.l1 (D.l2 ≫ D.l3), h1]
    rw [Category.assoc, reassoc_of% h2, h3]
    simp only [Category.assoc]
  exact hl.trans ((CategoryTheory.eq_whisker ho _).trans hr.symm)

/-- Pasting the native summand diagram gives the two equal summand composites.
Source: Stacks Tag 07A4, constituents of the signed total comparison.
(blueprint: lem-sf-finite-scalar-tensor-diagram-commutes).

Proof: the first three field equations identify the left total path on an injection
with the ordinary left path followed by the target injection. Substitute the ordinary
scalar square. The right field equation identifies that result with the right total
path on the same injection. This pasting uses only associativity of composition. -/
theorem finiteScalarTensorDiagram_commutes
    (R : Type u) [CommRing R] [Finite R] {X Y : Scheme.{u}} (p : X ⟶ Y)
    (P Q : CochainComplex
      (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1} R))) ℤ)
    (a b n : ℤ) (h : a + b = n) :
    let D := finiteScalarTensorSummandDiagram R p P Q a b n h
    D.j0 ≫ D.l1 ≫ D.l2 ≫ D.l3 = D.j0 ≫ D.right := by
  exact diagram_commutes (finiteScalarTensorSummandDiagram R p P Q a b n h)
    (finiteScalarTensorDiagram_fixed R p P Q a b n h)
    (finiteScalarTensorDiagram_realization R p P Q a b n h)
    (finiteScalarTensorDiagram_map R p P Q a b n h)
    (finiteScalarTensorDiagram_ordinary R p P Q a b n h)
    (finiteScalarTensorDiagram_right R p P Q a b n h)

end WeilConjectures
