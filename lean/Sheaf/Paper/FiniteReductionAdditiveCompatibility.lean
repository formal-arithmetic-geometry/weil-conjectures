/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.Paper.IntegralCompletedTowerPullbackUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Additive compatibility of the actual finite pullback tower

Source: Stacks, Tags 014E, 0FNH, 06XN.
(blueprint: lem-a1-finite-reduction-additive-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local implicit_reducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientSheafSystem
  CategoryTheory.sheafCompose WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.integralCoefficientCommRingSheaf SheafOfModules.restrictScalars
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FiniteReductionTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{t}} (g : X ⟶ Y)

/-- The finite-reduction pullback is a normalized additive construction on strict towers.
Source: Stacks, derived.tex, Situation following Tag 06XN; Tags 014E and 0FNH.
(blueprint: lem-a1-finite-reduction-additive-compatibility).

Proof: let A_n be the additive module functor Res_n g_n^*(- tensor S_n).
Construct its module transition from the canonical quotient map by the finite
pullback adjunction mate. Both this termwise transition and the selected complex
transition send the finite pullback unit of x to the lower-level unit of the
quotient image of x. Their unique unit-generator characterization identifies them.
Thus the transposed construction is the termwise complex functor of the additive
module-to-towers functor A. Applying A to dh+hd gives the homotopy formula. Its shift isomorphism
is the identity on reindexed terms and transports the signed differential by
additivity. The biproduct comparison identifies the cone differential matrix,
commutes with the second summand inclusion, and commutes with its projection to
the shifted first summand. The specified quotient transitions are natural module
maps, so these levelwise maps and their inverses commute with every transition.
Thus they define the asserted strict tower maps; coherence of shifts follows
termwise from the canonical shift comparison. These arguments apply to arbitrary
unbounded complexes and arbitrary scheme morphisms, including empty schemes. -/
theorem finite_reduction_additive_compatibility :
    (∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f f' : P ⟶ P'),
      Homotopy f f' → Nonempty (Homotopy
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)
        ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f'))) ∧
    ∃ c : (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).CommShift ℤ,
      (∀ (P : CochainComplex (Modules l E Y) ℤ) (r i : ℤ) (n : ℕ),
    letI := integralOperationsLevelPullback_additive l E g n
    letI := unrestrictedIntegralReductionFunctor_additive l E Y n
    letI : (unrestrictedIntegralReductionFunctor l E Y n ⋙
        integralOperationsLevelPullback l E g n ⋙
        SheafOfModules.restrictScalars
          (limit.π (integralCoefficientSheafSystem l E X) (op n))).Additive := by
      with_unfolding_all infer_instance
    (((Functor.commShiftIso (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X)
        (self := c) r).hom.app P).f i).app (op n) =
      (((unrestrictedIntegralReductionFunctor l E Y n ⋙
          integralOperationsLevelPullback l E g n ⋙
          SheafOfModules.restrictScalars
            (limit.π (integralCoefficientSheafSystem l E X) (op n))).mapCochainComplexShiftIso
          r).hom.app P).f i) ∧
      ∃ e : ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
        (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).obj
          (CochainComplex.mappingCone f) ≅ CochainComplex.mappingCone
            ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f),
        ∀ {P P' : CochainComplex (Modules l E Y) ℤ} (f : P ⟶ P'),
          (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map
      (CochainComplex.mappingCone.inr f) ≫ (e f).hom =
    CochainComplex.mappingCone.inr
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f) ∧
  (e f).hom ≫ (CochainComplex.mappingCone.triangle
      ((integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map f)).mor₃ =
    (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X).map
        (CochainComplex.mappingCone.triangle f).mor₃ ≫
      (Functor.commShiftIso (integralOperationsPullbackTowerFunctor l E g ⋙ transpose l E X)
        (self := c) (1 : ℤ)).hom.app P := by sorry

end WeilConjectures.FiniteReductionTower
