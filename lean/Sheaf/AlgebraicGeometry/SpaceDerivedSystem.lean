/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # Simplicial systems of derived quasi-coherent objects

Source: Stacks Project, Simplicial Spaces, Tags 0DLA and 0DL9
(blueprint: def-sfb-space-simplicial-derived-system).

Coherent systems retain every simplicial operator, including degeneracies. The equalizer
uses the canonical composition comparisons, rather than a freely chosen pair of arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite Functor

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} [∀ A : AlgebraicSpace S, HasDerivedCategory.{w} A.SmallModules]

/-- Transport along an equality of space maps, using their actual derived pullbacks.
Source: Stacks, Tag 0D6D (blueprint: def-sfb-space-simplicial-derived-system). -/
def spaceDerivedPullbackCongr {X Y : AlgebraicSpace S} {f g : X ⟶ Y} (h : f = g) :
    spaceDerivedPullback f ≅ spaceDerivedPullback g :=
  eqToIso (congrArg spaceDerivedPullback h)

/-- The canonical augmentation comparison for a simplicial operator.
Source: Stacks, Tag 0DLA (blueprint: def-sfb-space-simplicial-derived-system). -/
def spaceAugmentationComparison {X : AlgebraicSpace S} (U : SimplicialObject (Over X))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    spaceDerivedPullback (U.obj (op n)).hom ≅
      spaceDerivedPullback (U.obj (op m)).hom ⋙ spaceDerivedPullback (U.map φ.op).left :=
  (spaceDerivedPullbackCongr (Over.w (U.map φ.op))).symm ≪≫
    spaceDerivedPullbackComp (U.obj (op m)).hom (U.map φ.op).left

/-- Identity comparison for the actual simplicial structure map.
Source: Stacks, Tag 0DLA (blueprint: def-sfb-space-simplicial-derived-system). -/
def spaceSystemIdentityComparison {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) (n : SimplexCategory) :
    spaceDerivedPullback (U.map (𝟙 n).op).left ≅ 𝟭 ((U.obj (op n)).left.DerivedModules) :=
  spaceDerivedPullbackCongr (congrArg Over.Hom.left (U.map_id (op n))) ≪≫
    spaceDerivedPullbackId (U.obj (op n)).left

/-- Composition comparison for the actual simplicial structure maps.
Source: Stacks, Tag 0DLA (blueprint: def-sfb-space-simplicial-derived-system). -/
def spaceSystemCompositionComparison {X : AlgebraicSpace S}
    (U : SimplicialObject (Over X)) {l m n : SimplexCategory} (φ : l ⟶ m) (ψ : m ⟶ n) :
    spaceDerivedPullback (U.map (φ ≫ ψ).op).left ≅
      spaceDerivedPullback (U.map φ.op).left ⋙ spaceDerivedPullback (U.map ψ.op).left :=
  spaceDerivedPullbackCongr
      (congrArg Over.Hom.left (U.map_comp ψ.op φ.op)) ≪≫
    spaceDerivedPullbackComp (U.map φ.op).left (U.map ψ.op).left

/-- A coherent quasi-coherent derived family, with identity and composition laws for
all simplicial operators; no flatness is assumed for degeneracies.
Source: Stacks, Tag 0DLA and definition-cartesian-derived-modules
(blueprint: def-sfb-space-simplicial-derived-system). -/
structure SpaceDerivedSystem {X : AlgebraicSpace S} (U : SimplicialObject (Over X)) where
  /-- The derived object in every degree. -/
  obj (n : SimplexCategory) : (U.obj (op n)).left.DerivedModules
  /-- Every integer cohomology module is quasi-coherent. -/
  qcoh (n : SimplexCategory) : ((U.obj (op n)).left).derivedQCohProperty (obj n)
  /-- Transition isomorphism for every simplicial operator. -/
  transition {m n : SimplexCategory} (φ : m ⟶ n) :
    (spaceDerivedPullback (U.map φ.op).left).obj (obj m) ≅ obj n
  /-- The identity operator has the canonical unit transition. -/
  identity (n : SimplexCategory) :
    (transition (𝟙 n)).hom = (spaceSystemIdentityComparison U n).hom.app (obj n)
  /-- Transition isomorphisms respect the canonical pullback comparison. -/
  composition {l m n : SimplexCategory} (φ : l ⟶ m) (ψ : m ⟶ n) :
    (transition (φ ≫ ψ)).hom =
      (spaceSystemCompositionComparison U φ ψ).hom.app (obj l) ≫
        (spaceDerivedPullback (U.map ψ.op).left).map (transition φ).hom ≫
        (transition ψ).hom

/-- Transport the pullback of a degree-zero morphism to the degree-one augmentation.
Source: Stacks, Tag 0DL9 (blueprint: def-sfb-space-simplicial-derived-system). -/
def spaceDegreeOneRestriction {X : AlgebraicSpace S} (U : SimplicialObject (Over X))
    {M N : X.DerivedModules}
    (a : (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).obj M ⟶
      (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 0))).hom).obj N)
    (i : Fin 2) :
    (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 1))).hom).obj M ⟶
      (spaceDerivedPullback (U.obj (op (SimplexCategory.mk 1))).hom).obj N :=
  (spaceAugmentationComparison U (SimplexCategory.δ i)).hom.app M ≫
    (spaceDerivedPullback (U.map (SimplexCategory.δ i).op).left).map a ≫
    (spaceAugmentationComparison U (SimplexCategory.δ i)).inv.app N

end AlgebraicGeometry.AlgebraicSpace
