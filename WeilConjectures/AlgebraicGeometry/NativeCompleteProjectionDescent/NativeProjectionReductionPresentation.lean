/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingTensorComparison
public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.PoincareDuality.ProjectionFormula

/-! # Native normalized reduction presentations

Source: current blueprint, sec-smooth-purity,
`sk-prop-sp-integral-adjunction-direct-image.proof.md`, (2)--(3)
(blueprint: def-sp-projection-reduction-presentation).

The integral category is the ordinary unbounded derived category of modules over
`p_T^* underline O_E`. Only its section presentation is used for quotient generators.
The index `n : ℕ` denotes exponent `n + 1` throughout.

## Main definitions

* `TensorPresentation`: the whole-tower tensor comparison and its representative normalization.
* `Limit`: the normalized ordinary and derived restricted-tower limit.
* `reductionAdjunction`: the transported native reduction/limit adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance] AlgebraicGeometry.ProEtale.SpReductionTower.additive
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Actual quotient rings. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1}
    (Padic.coefficientExtensionIntegers l E ⧸ spEllIdeal l E ^ (n + 1)))

/-- Actual quotient transitions. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev transitions (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
    ((Ideal.Quotient.factorPowSucc (spEllIdeal l E) (n + 1)).comp
      ULift.ringEquiv.toRingHom))

/-- Native integral modules. Source: blueprint (2)--(3)
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev Modules (T : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T)

/-- Ordinary unbounded integral derived modules. Source: blueprint (2)--(3)
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev Integral (T : Scheme.{u}) := DerivedCategory (Modules l E T)

/-- Whole derived coefficient systems. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev System (T : Scheme.{u}) := VaryingRing.Derived (rings l E) (transitions l E) T

/-- The existing section-preserving sequence realization. Source: Zheng 4.1
(blueprint: def-sp-projection-reduction-presentation). -/
def towerEquivalence (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ≌ VaryingRing.Modules (rings l E) (transitions l E) T :=
  D.equivalence.trans (SheafOfModules.strictSystemSequenceEquivalence
    (spCoefficientCommRings l E T))

/-- Additivity of exact realization. Source: Zheng 4.1
(blueprint: def-sp-projection-reduction-presentation). -/
instance towerFunctorAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    (towerEquivalence l E T D).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of inverse realization. Source: Zheng 4.1
(blueprint: def-sp-projection-reduction-presentation). -/
instance towerInverseAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    (towerEquivalence l E T D).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Localization of the fixed realization. Source: Zheng 4.1
(blueprint: def-sp-projection-reduction-presentation). -/
def derivedTowerEquivalence (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T) :
    spDerivedCoefficientTowers l E T D ≌ System l E T :=
  letI := D.hasDerived
  (towerEquivalence l E T D).mapDerivedCategory

/-- The exact section equivalence after localization, at its existing universes.
Source: Stacks 00YV (blueprint: def-sp-projection-reduction-presentation). -/
def sectionEquivalence (T : Scheme.{u}) :
    Integral l E T ≌ DerivedCategory (spIntegralSectionModules l E T) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).inverse
  (spIntegralModuleEquivalence l E T).mapDerivedCategory

/-- Native reduction through exactly the recorded section and tower equivalences.
Source: blueprint (3) (blueprint: def-sp-projection-reduction-presentation). -/
def reduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) : Integral l E T ⥤ System l E T :=
  (sectionEquivalence l E T).functor ⋙ R.red ⋙
    (derivedTowerEquivalence l E T D).functor

/-- Ordinary simultaneous quotient extension. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
def ordinaryReduction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    Modules l E T ⥤ VaryingRing.Modules (rings l E) (transitions l E) T :=
  (spIntegralModuleEquivalence l E T).functor ⋙ R.ordinary ⋙
    (towerEquivalence l E T D).functor

/-- Additivity of simultaneous reduction. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
instance ordinaryReductionAdditive (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) : (ordinaryReduction l E T D R).Additive :=
  letI := R.additive
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  inferInstanceAs ((spIntegralModuleEquivalence l E T).functor ⋙ R.ordinary ⋙
    (towerEquivalence l E T D).functor).Additive

/-- The universal localization comparison, retaining the native source.
Source: blueprint (3) (blueprint: def-sp-projection-reduction-presentation). -/
def reductionEpsilon (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (P : CochainComplex (Modules l E T) ℤ) :
    (reduction l E T D R).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := D.hasDerived
  letI := R.additive
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  (R.red ⋙ (derivedTowerEquivalence l E T D).functor).map
      ((spIntegralModuleEquivalence l E T).functor.mapDerivedCategoryFactors.hom.app P) ≫
    (derivedTowerEquivalence l E T D).functor.map
      (R.counit.app
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    (towerEquivalence l E T D).functor.mapDerivedCategoryFactors.hom.app
      ((R.ordinary.mapHomologicalComplex (.up ℤ)).obj
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P))

/-- The actual quotient augmentation `x tensor 1`. Source: blueprint (3)
(blueprint: def-sp-projection-reduction-presentation). -/
def reductionGenerator (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (M : Modules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj M).val.obj U) :
    ((ordinaryReduction l E T D R).obj M).val.obj (op (n, U.unop)) :=
  spReductionGenerator l E T D R.coefficient R.ordinary R.level
    ((spIntegralModuleEquivalence l E T).functor.obj M) n U 1 x

/-- Native signed total tensor. Source: Stacks 06YN
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev totalTensor (T : Scheme.{u}) :=
  Functor.uncurry.obj (curriedTensor (CochainComplex (Modules l E T) ℤ))

/-- The specified flat-term K-flat representative class, tested on unchanged sections.
Source: blueprint (3) (blueprint: def-sp-projection-reduction-presentation). -/
def FlatRepresentative (T : Scheme.{u}) (P : CochainComplex (Modules l E T) ℤ) : Prop :=
  let S := ((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P
  CochainComplex.IsKFlatIndependentCoefficients S ∧
    flatTerms.{u + 1, u, u + 1} (Scheme.ProEt.topology T) (spIntegralSectionRing l E T) S

/-- Existing whole-system tensor calculus. Source: Zheng 4.1
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev Calculus (T : Scheme.{u}) :=
  SemilinearSections.Data.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (VaryingRing.coefficients (rings l E) T)
    (VaryingRing.coefficientTransition (rings l E) (transitions l E) T)

/-- A total-summand pure tensor in the section presentation of the native tensor.
Source: Stacks 03EL, 06YN (blueprint: def-sp-projection-reduction-presentation). -/
def tensorGenerator (T : Scheme.{u}) (P Q : CochainComplex (Modules l E T) ℤ)
    (a b k : ℤ) (h : a + b = k) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj (P.X a)).val.obj U)
    (y : ((spIntegralModuleEquivalence l E T).functor.obj (Q.X b)).val.obj U) :
    ((spIntegralModuleEquivalence l E T).functor.obj ((P ⊗ Q).X k)).val.obj U :=
  ((spIntegralModuleEquivalence l E T).functor.map
    (HomologicalComplex.ιTensorObj P Q a b k h)).val.app U
      ((ModuleRingedComparison.ordinaryTensorComparison (spIntegralCondensed l E) T
        (P.X a) (Q.X b)).inv.val.app U
        (tensorSection.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (spIntegralSectionRing l E T) _ _ U x y))

/-- The normalized whole-tower tensor comparison, with the ordinary signed-total
map and its exact localization square. This is presentation data, not an existence claim.
Source: blueprint (3) (blueprint: def-sp-projection-reduction-presentation). -/
structure TensorPresentation (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (S : Calculus l E T) where
  mu : Functor.uncurry.obj (CondensedRing.derivedTensor (spIntegralCondensed l E) T) ⋙
      reduction l E T D R ≅
    ((reduction l E T D R).prod (reduction l E T D R)) ⋙ S.closed.tensor
  chain : totalTensor l E T ⋙ (ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ) ≅
    ((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).prod
      ((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)) ⋙
        SemilinearSections.totalTensor.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology T))
          (systemRing (Scheme.ProEt.topology T)
            (VaryingRing.coefficients (rings l E) T)
            (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
  generators : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (a b k : ℤ) (h : a + b = k) (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((spIntegralModuleEquivalence l E T).functor.obj (P.X a)).val.obj U)
    (y : ((spIntegralModuleEquivalence l E T).functor.obj (Q.X b)).val.obj U),
    ((chain.hom.app (P, Q)).f k).val.app (op (n, U.unop))
      (reductionGenerator l E T D R _ n U (tensorGenerator l E T P Q a b k h U x y)) =
    coefficientTensorGenerator.{u + 1, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing (Scheme.ProEt.topology T)
        (VaryingRing.coefficients (rings l E) T)
        (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P)
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj Q)
      a b k h (op (n, U.unop))
      (reductionGenerator l E T D R (P.X a) n U x)
      (reductionGenerator l E T D R (Q.X b) n U y)
  kflat : ∀ (P : CochainComplex (Modules l E T) ℤ), FlatRepresentative l E T P →
    CochainComplex.IsKFlatIndependentCoefficients
      (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P)
  localization : ∀ (P Q : CochainComplex (Modules l E T) ℤ)
    (hP : FlatRepresentative l E T P) (hQ : FlatRepresentative l E T Q),
    mu.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      S.closed.tensor.map (Prod.mkHom (reductionEpsilon l E T D R P)
        (reductionEpsilon l E T D R Q)) =
    (reduction l E T D R).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
      reductionEpsilon l E T D R (P ⊗ Q) ≫
      DerivedCategory.Q.map (chain.hom.app (P, Q)) ≫
      (tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology T))
        (systemRing (Scheme.ProEt.topology T)
          (VaryingRing.coefficients (rings l E) T)
          (VaryingRing.coefficientTransition (rings l E) (transitions l E) T))
        S.closed S.tensorModels
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj P)
        (((ordinaryReduction l E T D R).mapHomologicalComplex (.up ℤ)).obj Q)
        (kflat P hP) (kflat Q hQ)).hom

/-- Restriction from completed section coefficients to the actual pulled-back
integral section ring, along the recorded normalized ring isomorphism.
Source: blueprint, restriction before limit
(blueprint: def-sp-projection-reduction-presentation). -/
abbrev completedRestriction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map R.coefficient.hom)

/-- The strict tower after restricting every finite scalar action to R_T. Its
transitions are the actual quotient-semilinear transitions, retained before derivation.
Source: blueprint, clause (2) (blueprint: def-sp-projection-reduction-presentation). -/
def restrictedTower (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T D n ⋙
      completedRestriction l E T D R)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T D n)
      (completedRestriction l E T D R))).flip

/-- The actual ordinary inverse limit of that restricted strict tower.
Source: blueprint, clause (2) (blueprint: def-sp-projection-reduction-presentation). -/
def ordinaryLimit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :=
  restrictedTower l E T D R ⋙ Limits.lim

/-- The n-th ordinary inverse-limit projection, with its original finite-level sections.
Source: blueprint, clause (2) (blueprint: def-sp-projection-reduction-presentation). -/
def ordinaryProjection (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    (C : spCoefficientTowers l E T) (n : ℕ) :=
  limit.π ((restrictedTower l E T D R).obj C) (op n)

/-- Normalization of the ordinary tensor/limit adjunction on local tensor generators.
Source: blueprint, clause (2) (blueprint: def-sp-projection-reduction-presentation). -/
def IsOrdinaryAdjunctionNormalized (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    (adj : R.ordinary ⊣ ordinaryLimit l E T D R) : Prop :=
  ∀ (P : spIntegralSectionModules l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : P.val.obj U),
    (ordinaryProjection l E T D R (R.ordinary.obj P) n).val.app U
        ((adj.unit.app P).val.app U x) =
      ((R.level n).inv.app P).val.app U
        (SheafOfModules.systemModelTmul (D.scalar
          (spIntegralReductionScalar l E T R.coefficient n)).model P U 1 x)

/-- Representative normalization of the derived tensor/limit adjunction.
Source: blueprint, clause (2) (blueprint: def-sp-projection-reduction-presentation). -/
def IsDerivedAdjunctionNormalized (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D)
    [(ordinaryLimit l E T D R).Additive]
    (ordinaryAdjunction : R.ordinary ⊣ ordinaryLimit l E T D R)
    (derived : spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (spIntegralSectionModules l E T))
    (unit : (ordinaryLimit l E T D R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      spTowerLocalization l E T D ⋙ derived)
    (adjunction : R.red ⊣ derived) : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (I : CochainComplex (spCoefficientTowers l E T) ℤ)
    (v : (R.ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P)
        ((spTowerLocalization l E T D).obj I)
        (R.counit.app P ≫
          (spTowerLocalization l E T D).map v) =
      DerivedCategory.Q.map
        ((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I v) ≫ unit.app I

/-- Universal presentation of total derived inverse limit. Ordinary reduction tensors
with each quotient; its right adjoint is precisely the inverse limit of the restricted
finite modules. Both the ordinary and derived universal properties are retained.
The representative equation fixes the derived adjunction to the ordinary one.
Source: blueprint, clause (2), strict tower inverse limit; Stacks 0940 and 09T5
(blueprint: def-sp-projection-reduction-presentation). -/
structure Limit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  [additive : (ordinaryLimit l E T D R).Additive]
  ordinaryAdjunction : R.ordinary ⊣ ordinaryLimit l E T D R
  ordinary_normalization : IsOrdinaryAdjunctionNormalized l E T D R ordinaryAdjunction
  derived : spDerivedCoefficientTowers l E T D ⥤
    DerivedCategory (spIntegralSectionModules l E T)
  unit : (ordinaryLimit l E T D R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    spTowerLocalization l E T D ⋙ derived
  universal : derived.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (spCoefficientTowers l E T) (.up ℤ))
  computes : ∀ I : CochainComplex (spCoefficientTowers l E T) ℤ,
    I.IsKInjective → IsIso (unit.app I)
  adjunction : R.red ⊣ derived
  normalization : IsDerivedAdjunctionNormalized l E T D R ordinaryAdjunction derived unit
    adjunction


/-- Total derived limit in native coordinates. Source: blueprint (2)
(blueprint: def-sp-projection-reduction-presentation). -/
def totalLimit (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (A : Limit l E T D R) :
    System l E T ⥤ Integral l E T :=
  (derivedTowerEquivalence l E T D).inverse ⋙ A.derived ⋙ (sectionEquivalence l E T).inverse

/-- Transport of the normalized adjunction, retaining its unit and counit.
Source: blueprint (2) (blueprint: def-sp-projection-reduction-presentation). -/
def reductionAdjunction (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) (A : Limit l E T D R) :
    reduction l E T D R ⊣ totalLimit l E T D R A :=
  ((sectionEquivalence l E T).toAdjunction.comp A.adjunction).comp
    (derivedTowerEquivalence l E T D).toAdjunction


end AlgebraicGeometry.ProEtale.NativeCompleteProjectionDescent
