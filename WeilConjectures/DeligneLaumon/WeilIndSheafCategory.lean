/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.DeligneLaumon.ConstructiblePullbackTExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Indization
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Opposites
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFullyFaithful
import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.DeligneLaumon.CommonStageOpenHeartAdjunction
import WeilConjectures.DeligneLaumon.IsomorphismFieldTransport
import WeilConjectures.DeligneLaumon.CommonStagePullbackCompNaturality

/-! # Ambient equivariant ind-sheaves for the recorded common-stage Weil heart

This file provides the pullback functoriality on geometric fibres used for the common-stage
Weil heart: common-stage pullback along base-changed morphisms, its normalized composition
isomorphism, and the Frobenius-equivariance square of pullback.

## Main definitions

- `zlPull`: pullback on geometric fibres along a morphism defined over `k₀`.
- `zlPullComp`: the normalized composition isomorphism for common-stage pullback.
- `zlFrobeniusSquare`: the commutation of pullback with geometric Frobenius pullback.

## Implementation details

All inverse-image comparisons are normalized by the existing integral pullback composition.
The object comparison for common-stage pullback is an equality, never a chosen automorphism.

## References

* SGA 4, XVII
* Stacks Project, Tag 099N(5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The base change of a morphism `f₀` over `k₀` to the fixed algebraic closure `k` of the
finite field. -/
def zlFiberMap {X₀ Y₀ : Over (Spec (.of D.k₀))} (f₀ : X₀ ⟶ Y₀) :=
  ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).left

/-- Pullback on geometric fibres along a morphism `f₀` over `k₀`, given by the common-stage
derived pullback along its base change. -/
def zlPull {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :=
  @commonStageDerivedPullback l _ Ω _ _ _ _ _ (zlFiberMap D f₀)
    (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x)
    (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y)

/-- The integral pullback composition isomorphism, normalized by finite reductions. -/
def zlIntegralPullComp (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (integralPullbackComposition l E).choose f g

/-- Common-stage pullback of the rationalization of an integral constructible complex `K` is
equal to the rationalization of the integral pullback of `K`. -/
theorem zlStagePull_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :
    (commonStageDerivedPullback l Ω f).obj
        ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
          ((sfRationalConstructibleLocalization l _ Y).obj K)) =
      (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
        ((sfRationalConstructibleLocalization l _ X).obj
          ((constructibleIntegralPullback l _ f).obj K)) := by
  refine ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 _).trans ?_
  change (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
    ((rationalDerivedPullback l _ f).obj _) = _
  exact congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
    ((rationalDerivedPullback_existsUnique l _ f).exists.choose_spec.2.1 _)

/-- The isomorphism induced by the equality `zlStagePull_eq`. -/
def zlStagePullIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (K : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y) :=
  eqToIso (zlStagePull_eq l Ω f L K)

section CompositionProof
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback commonStagePullbackCompComponent
  completedIntegralCoefficientSheafUnrestricted

/-- There is a unique composition isomorphism for common-stage pullback whose components on
rationalized integral objects are induced by the integral pullback composition. -/
theorem zlPullComp_existsUnique {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : commonStageDerivedPullback l Ω (f ≫ g) ≅
        commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (K : sfIntegralConstructibleCategory l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z),
        e.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
            ((sfRationalConstructibleLocalization l _ Z).obj K)) ≫
          (commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
          (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom =
        (zlStagePullIso l Ω (f ≫ g) L K).hom ≫
          (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
            ((sfRationalConstructibleLocalization l _ X).map
              ((zlIntegralPullComp l _ f g).hom.app K)) := by
  let e : commonStageDerivedPullback l Ω (f ≫ g) ≅
      commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f :=
    NatIso.ofComponents (F := commonStageDerivedPullback l Ω (f ≫ g))
      (G := commonStageDerivedPullback l Ω g ⋙ commonStageDerivedPullback l Ω f)
      (commonStagePullbackCompComponent l Ω f g)
    (fun {_ _} a ↦ commonStagePullbackCompComponent_naturality l Ω f g a)
  have he (L : AlgebraicallyClosedCoefficients.Index l Ω)
      (K : sfIntegralConstructibleCategory l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z) :
      e.hom.app ((GeneralAlgebraicallyClosedCoefficients.inclusion L).obj
          ((sfRationalConstructibleLocalization l _ Z).obj K)) ≫
        (commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
        (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom =
      (zlStagePullIso l Ω (f ≫ g) L K).hom ≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion L).map
          ((sfRationalConstructibleLocalization l _ X).map
            ((zlIntegralPullComp l _ f g).hom.app K)) := by
    apply eq_of_heq
    simp only [zlStagePullIso, eqToIso.hom, eqToHom_map, ← Category.assoc,
      comp_eqToHom_heq_iff, heq_eqToHom_comp_iff]
    dsimp only [zlIntegralPullComp]
    change HEq (commonStagePullbackCompComponent l Ω f g ⟨L, ⟨K⟩⟩).hom _
    exact commonStagePullbackCompComponent_heq.{u, v} l Ω f g ⟨L, ⟨K⟩⟩
  refine ⟨e, he, ?_⟩
  intro a ha
  apply Iso.ext
  apply NatTrans.ext
  funext P
  rcases P with ⟨L, ⟨K⟩⟩
  apply (cancel_mono
    ((commonStageDerivedPullback l Ω f).map (zlStagePullIso l Ω g L K).hom ≫
      (zlStagePullIso l Ω f L ((constructibleIntegralPullback l _ g).obj K)).hom)).1
  simpa only [Category.assoc, GeneralAlgebraicallyClosedCoefficients.inclusion,
    StageSystem.ι, sfRationalConstructibleLocalization, ScalarLocalization.localization]
    using (ha L K).trans (he L K).symm

end CompositionProof
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The uniquely normalized common-stage composition isomorphism. -/
def zlPullComp {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (zlPullComp_existsUnique l Ω f g).exists.choose

/-- Geometric Frobenius is natural for a morphism defined over `k₀`. -/
theorem zlFrobenius_naturality {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (D.geometricFrobenius X₀).asIso.hom ≫ zlFiberMap D f₀ =
      zlFiberMap D f₀ ≫ (D.geometricFrobenius Y₀).asIso.hom := by
  apply pullback.hom_ext
  · simp [zlFiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]
  · simp [zlFiberMap, FiniteFieldDatum.geometricFrobenius,
      FiniteFieldDatum.galoisMap, Over.pullback_map_left, baseChangeMap, Category.assoc]

/-- Pullback on geometric fibres commutes with Frobenius pullback, via the normalized
composition isomorphisms. -/
def zlFrobeniusSquare {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    zlPull D l hl Ω f₀ ⋙ sfCommonStageWeilFrobeniusPullback D l hl X₀ Ω ≅
      sfCommonStageWeilFrobeniusPullback D l hl Y₀ Ω ⋙ zlPull D l hl Ω f₀ :=
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  (zlPullComp l Ω (D.geometricFrobenius X₀).asIso.hom (zlFiberMap D f₀)).symm ≪≫
    eqToIso (congrArg
      (fun f : (D.geometricFiber X₀).left ⟶ (D.geometricFiber Y₀).left ↦
        commonStageDerivedPullback l Ω f) (zlFrobenius_naturality D f₀)) ≪≫
      zlPullComp l Ω (zlFiberMap D f₀) (D.geometricFrobenius Y₀).asIso.hom

section IndExtension
attribute [-instance] Functor.hasLeftKanExtension_of_preserves
attribute [-instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [-instance] Functor.PreservesLeftKanExtension.preserves

universe w
variable {C B : Type w} [SmallCategory C] [SmallCategory B]
  [Abelian C] [Abelian B]

end IndExtension

attribute [instance] Functor.hasLeftKanExtension_of_preserves
attribute [instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [instance] Functor.PreservesLeftKanExtension.preserves

section FrobeniusEquivalence
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback

end FrobeniusEquivalence

end WeilConjectures
