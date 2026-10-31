/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.InternalSectionTensorLocalization
public import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.CategoryTheory.LocalizedModuleExactIndependent
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.SixFunctors.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.SectionDerivedPushpullNormalization
import WeilConjectures.AlgebraicGeometry.SectionDerivedTensorNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived

/-!
# Internal and ringed module projection comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0B56 and 0GL1;
latest blueprint, lem-sf-tensor-hom, proof opening and Steps 1--2
(blueprint: lem-sfb-module-object-ringed-projection-comparison).

All operations below are the fixed section-action operations. The tensor on the
section side is their normalized K-flat realization, not an unspecified bifunctor.
The equations compare the specified adjunctions and the actual universal derived
pullback tensor map, including the counit and open-unit projection transposes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

/-- The ringed projection mate for the fixed canonical tensor comparison and derived
adjunction. Source: Stacks 0B56, equation-projection-formula-map
(blueprint: lem-sfb-module-object-ringed-projection-comparison). -/
def sectionProjectionMate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (modules Λ X)) (L : DerivedCategory (modules Λ Y)) :
    (tensor Λ Y).obj ((derivedPushforward Λ f).obj K, L) ⟶
      (derivedPushforward Λ f).obj
        ((tensor Λ X).obj (K, (derivedPullback Λ f).obj L)) :=
  derivedProjectionFormulaMate (derivedPullback Λ f) (derivedPushforward Λ f)
    (derivedAdjunction Λ f) (tensor Λ Y) (tensor Λ X) (tensorPullComparison Λ f) K L

/-- The module-object inverse open projection, using the actual pullback tensor map.
Source: Stacks 0GL1, and the open-unit normalization in lem-sf-open-tensor-normalization
(blueprint: lem-sfb-module-object-ringed-projection-comparison). -/
def internalInverseOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (internalModules Λ U)) (N : DerivedCategory (internalModules Λ X)) :
    (internalDerivedExtension Λ j).obj (M ⊗ (internalDerivedPullback Λ j).obj N) ⟶
      (internalDerivedExtension Λ j).obj M ⊗ N :=
  (((internalOpenAdjunction Λ j).projectionMap (internalDerivedPullback Λ j)
    (CondensedRing.derivedTensor Λ U) (CondensedRing.derivedTensor Λ X)
    (CondensedRing.leftDerivedUpperStarTensorIso Λ j).inv).app M).app N

/-- The ringed inverse open projection is the adjunct of the open unit tensored with
identity followed by the inverse restriction/tensor comparison. Source: Stacks 0GL1
and lem-sf-open-tensor-normalization, gamma_inverse
(blueprint: lem-sfb-module-object-ringed-projection-comparison). -/
def sectionInverseOpenProjection {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : DerivedCategory (modules Λ U)) (N : DerivedCategory (modules Λ X)) :
    (derivedExtension Λ j).obj ((tensor Λ U).obj (M, (derivedPullback Λ j).obj N)) ⟶
      (tensor Λ X).obj ((derivedExtension Λ j).obj M, N) :=
  ((derivedOpenAdjunction Λ j).homEquiv _ _).symm
    ((tensor Λ U).map (Prod.mkHom ((derivedOpenAdjunction Λ j).unit.app M) (𝟙 _)) ≫
      (tensorPullComparison Λ j).inv.app ((derivedExtension Λ j).obj M, N))

/-- The complete comparison assertion, expressed using the fixed comparison maps.
Universes retain the small pro-etale site and the ordinary unbounded derived categories.
Every field is an equation of components of specified natural transformations.
Source: Stacks 07A4, 07A6, 0B56 and 0GL1; lem-sf-tensor-hom, proof opening and Steps 1--2
(blueprint: lem-sfb-module-object-ringed-projection-comparison). -/
structure ModuleObjectRingedProjectionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- The tensor realization retains its fixed signed-total representative normalization. -/
  tensorNormalization : ∀ T : Scheme.{u},
    TensorRepresentativeCondition Λ T (qTensor Λ T)
  /-- Both ordinary open operations on each side are exact. -/
  openExact : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteColimits (CondensedRing.openImmersionLowerShriek Λ j) ∧
    PreservesFiniteLimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteColimits (CondensedRing.upperStar Λ j) ∧
    PreservesFiniteLimits (extension Λ j) ∧ PreservesFiniteColimits (extension Λ j) ∧
    PreservesFiniteLimits (pullback Λ j) ∧ PreservesFiniteColimits (pullback Λ j)
  /-- The specified Hom bijections agree under the operation comparisons. -/
  adjunction : ∀ (M : DerivedCategory (internalModules Λ Y))
      (N : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedPullback Λ f).obj M ⟶ N),
    (derivedAdjunction Λ f).homEquiv _ _
        ((derivedPullComparison Λ f).inv.app M ≫ (derivedFunctor Λ X).map q) =
      (derivedFunctor Λ Y).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).homEquiv _ _ q) ≫
        (derivedPushComparison Λ f).hom.app N
  /-- The unit comparison, with the specified internal unit. -/
  unit : ∀ M : DerivedCategory (internalModules Λ Y),
    (derivedAdjunction Λ f).unit.app ((derivedFunctor Λ Y).obj M) =
      (derivedFunctor Λ Y).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).unit.app M) ≫
        (derivedPushComparison Λ f).hom.app ((internalDerivedPullback Λ f).obj M) ≫
        (derivedPushforward Λ f).map ((derivedPullComparison Λ f).hom.app M)
  /-- The counit comparison, with the specified internal counit. -/
  counit : ∀ N : DerivedCategory (internalModules Λ X),
    (derivedAdjunction Λ f).counit.app ((derivedFunctor Λ X).obj N) =
      (derivedPullback Λ f).map ((derivedPushComparison Λ f).inv.app N) ≫
        (derivedPullComparison Λ f).inv.app ((internalDerivedPushforward Λ f).obj N) ≫
        (derivedFunctor Λ X).map
          ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ f).counit.app N)
  /-- Geometric pullback compositors agree, for every second scheme morphism. -/
  compositor : ∀ {Z : Scheme.{u}} (g : Y ⟶ Z)
      (M : DerivedCategory (internalModules Λ Z)),
    (derivedPullComparison Λ (f ≫ g)).hom.app M ≫
        (derivedPullbackComposition Λ f g).hom.app ((derivedFunctor Λ Z).obj M) =
      (derivedFunctor Λ X).map ((CondensedRing.leftDerivedUpperStarComp Λ f g).hom.app M) ≫
        (derivedPullComparison Λ f).hom.app ((internalDerivedPullback Λ g).obj M) ≫
        (derivedPullback Λ f).map ((derivedPullComparison Λ g).hom.app M)
  /-- Equality of the actual pullback tensor transformations, on all unbounded pairs. -/
  tensor : ∀ M N : DerivedCategory (internalModules Λ Y),
    (derivedFunctor Λ X).map (((CondensedRing.leftDerivedUpperStarTensor Λ f).app M).app N) ≫
        (tensorComparison Λ X).hom.app
          ((internalDerivedPullback Λ f).obj M, (internalDerivedPullback Λ f).obj N) ≫
        (ModuleRingedComparison.tensor Λ X).map (Prod.mkHom
          ((derivedPullComparison Λ f).hom.app M) ((derivedPullComparison Λ f).hom.app N)) =
      (derivedPullComparison Λ f).hom.app (M ⊗ N) ≫
        (derivedPullback Λ f).map ((tensorComparison Λ Y).hom.app (M, N)) ≫
        (tensorPullComparison Λ f).hom.app
          ((derivedFunctor Λ Y).obj M, (derivedFunctor Λ Y).obj N)
  /-- Equality of the specified direct-image projection mates. -/
  projection : ∀ (K : DerivedCategory (internalModules Λ X))
      (L : DerivedCategory (internalModules Λ Y)),
    (derivedFunctor Λ Y).map (CondensedRing.moduleObjectProjectionMap Λ f K L) ≫
        (derivedPushComparison Λ f).hom.app (K ⊗ (internalDerivedPullback Λ f).obj L) ≫
        (derivedPushforward Λ f).map
          ((tensorComparison Λ X).hom.app (K, (internalDerivedPullback Λ f).obj L) ≫
            (ModuleRingedComparison.tensor Λ X).map
              (Prod.mkHom (𝟙 _) ((derivedPullComparison Λ f).hom.app L))) =
      (tensorComparison Λ Y).hom.app ((internalDerivedPushforward Λ f).obj K, L) ≫
        (ModuleRingedComparison.tensor Λ Y).map
          (Prod.mkHom ((derivedPushComparison Λ f).hom.app K) (𝟙 _)) ≫
        sectionProjectionMate Λ f ((derivedFunctor Λ X).obj K) ((derivedFunctor Λ Y).obj L)
  /-- Ordinary open adjunction units agree under the same section equivalences. -/
  ordinaryOpenUnit : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : internalModules Λ U),
    (equivalence Λ U).functor.map
        ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).unit.app M) ≫
        (pullComparison Λ j).hom.app ((CondensedRing.openImmersionLowerShriek Λ j).obj M) ≫
        (pullback Λ j).map ((extensionComparison Λ j).hom.app M) =
      (openAdjunction Λ j).unit.app ((equivalence Λ U).functor.obj M)
  /-- Ordinary open adjunction counits agree. -/
  ordinaryOpenCounit : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (N : internalModules Λ X),
    (extension Λ j).map ((pullComparison Λ j).inv.app N) ≫
        (extensionComparison Λ j).inv.app ((CondensedRing.upperStar Λ j).obj N) ≫
        (equivalence Λ X).functor.map
          ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ j).counit.app N) =
      (openAdjunction Λ j).counit.app ((equivalence Λ X).functor.obj N)
  /-- The localized open adjunctions agree as Hom bijections. -/
  openAdjunction : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : DerivedCategory (internalModules Λ U))
      (N : DerivedCategory (internalModules Λ X))
      (q : (internalDerivedExtension Λ j).obj M ⟶ N),
    (derivedOpenAdjunction Λ j).homEquiv _ _
        ((derivedExtensionComparison Λ j).inv.app M ≫ (derivedFunctor Λ X).map q) =
      (derivedFunctor Λ U).map ((internalOpenAdjunction Λ j).homEquiv _ _ q) ≫
        (derivedPullComparison Λ j).hom.app N
  /-- The localized open unit comparison. -/
  openUnit : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : DerivedCategory (internalModules Λ U)),
    (derivedOpenAdjunction Λ j).unit.app ((derivedFunctor Λ U).obj M) =
      (derivedFunctor Λ U).map ((internalOpenAdjunction Λ j).unit.app M) ≫
        (derivedPullComparison Λ j).hom.app ((internalDerivedExtension Λ j).obj M) ≫
        (derivedPullback Λ j).map ((derivedExtensionComparison Λ j).hom.app M)
  /-- The localized open counit comparison. -/
  openCounit : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (N : DerivedCategory (internalModules Λ X)),
    (derivedOpenAdjunction Λ j).counit.app ((derivedFunctor Λ X).obj N) =
      (derivedExtension Λ j).map ((derivedPullComparison Λ j).inv.app N) ≫
        (derivedExtensionComparison Λ j).inv.app ((internalDerivedPullback Λ j).obj N) ≫
        (derivedFunctor Λ X).map ((internalOpenAdjunction Λ j).counit.app N)
  /-- Equality of the inverse open projection maps fixed by the open-unit adjunct. -/
  inverseOpenProjection : ∀ {U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : DerivedCategory (internalModules Λ U))
      (N : DerivedCategory (internalModules Λ X)),
    (derivedFunctor Λ X).map (internalInverseOpenProjection Λ j M N) ≫
        (tensorComparison Λ X).hom.app ((internalDerivedExtension Λ j).obj M, N) ≫
        (ModuleRingedComparison.tensor Λ X).map
          (Prod.mkHom ((derivedExtensionComparison Λ j).hom.app M) (𝟙 _)) =
      (derivedExtensionComparison Λ j).hom.app (M ⊗ (internalDerivedPullback Λ j).obj N) ≫
        (derivedExtension Λ j).map
          ((tensorComparison Λ U).hom.app (M, (internalDerivedPullback Λ j).obj N) ≫
            (ModuleRingedComparison.tensor Λ U).map
              (Prod.mkHom (𝟙 _) ((derivedPullComparison Λ j).hom.app N))) ≫
        sectionInverseOpenProjection Λ j ((derivedFunctor Λ U).obj M)
          ((derivedFunctor Λ X).obj N)

/-- The termwise section equivalences identify the specified internal and ringed
adjunctions, pullback compositors, tensor maps, and both projection mates.

Source: Stacks 07A4, 07A6, 0B56 and 0GL1; latest blueprint lem-sf-tensor-hom,
proof opening and Steps 1--2
(blueprint: lem-sfb-module-object-ringed-projection-comparison).

Proof:
1. Apply sectionDerivedPushpullNormalization to the identical ordinary operations.
It compares the two independently specified derived operations and adjunctions,
including units, counits and the geometric pullback compositors.
2. The normalized tensor comparisons localize the same signed total map, summand
by summand. K-flat localization extensionality identifies these comparisons.
3. The universal derived bifunctor characterization identifies the actual
leftDerivedUpperStarTensor with internalDelta. Apply
section_derived_tensor_normalization to obtain the tensor square for every pair.
4. Under the adjunction comparison, the transpose of moduleObjectProjectionMap
is the counit tensored with identity after this tensor square. This is precisely
the defining transpose of sectionProjectionMate. Injectivity of homEquiv gives
the projection equation, without asserting invertibility of this projection.
5. The ordinary open operations and their units and counits agree by
internal_module_operations_transport and the slice-site interpretation of an open.
Both open operations are exact. Localize their ordinary adjunctions termwise;
the exact-derived units and counits are localizations of the ordinary ones.
The resulting restriction comparison equals the specified derivedPullComparison
by the canonical exact/left-derived factorization.
6. Tensor the open-unit comparison with identity and use the inverse of the tensor
square from step 3. These are exactly the two transposes defining the inverse
open projections. Injectivity of the identified open Hom bijections gives their
equality, with the same normalization as gamma_inverse in OpenTensorNormalization.
-/
theorem moduleObjectRingedProjectionComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ModuleObjectRingedProjectionComparison Λ f := by
  sorry

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
