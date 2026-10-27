/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModels
public import Sheaf.Paper.KoszulReconstruction
public import Sheaf.RingTheory.RlimPerfectComplete
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral

/-! # Data of the algebraic tower underlying local finite perfect models

Source: Stacks Project, Tag 09C6, the construction of the algebraic normalized tower;
Tags 09B1 and 09BV for its compatible local comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The small localization furnished by the Grothendieck universal construction.
Source: Stacks Tag 05RU. -/
abbrev finitePerfectAdicAlgebraDerived (R : Type t) [CommRing R] :
    HasDerivedCategory.{t} (ModuleCat.{t} R) :=
  HasDerivedCategory.ofIsGrothendieckAbelian _

attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Exact constant realization, including the recorded coefficient-universe lift.
Source: Stacks Tags 093J and 03CY. -/
def finitePerfectAdicConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    ModuleCat.{t} A ⥤ SheafOfModules.{t + 1} (adicModuleRing X A) :=
  ModuleCat.uliftFunctor.{t + 1, t} A ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom ⋙
    koszulConstantFunctor X A

theorem finitePerfectAdicConstant_exact (X : Scheme.{t}) (A : Type t) [CommRing A] :
    (finitePerfectAdicConstant X A).Additive ∧
      PreservesFiniteLimits (finitePerfectAdicConstant X A) ∧
      PreservesFiniteColimits (finitePerfectAdicConstant X A) := by
  have h := commutativeSiteConstantModuleFunctor_exact
    (ProEt.topology X) (ULift.{t + 1} A)
  have h' : (koszulConstantFunctor X A).Additive ∧
      PreservesFiniteLimits (koszulConstantFunctor X A) ∧
      PreservesFiniteColimits (koszulConstantFunctor X A) := h
  have := h'.1
  have := h'.2.1
  have := h'.2.2
  have he : (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom).IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A)).isEquivalence_functor
  have : PreservesLimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) :=
    Adjunction.isEquivalencePreservesLimits _
  have : PreservesColimits (ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} A ≃+* A).toRingHom) :=
    Adjunction.isEquivalence_preservesColimits _
  unfold finitePerfectAdicConstant
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The exact derived constant functor on the chosen small algebraic localization.
Source: Stacks Tag 05RU. -/
def finitePerfectAdicDerivedConstant (X : Scheme.{t}) (A : Type t) [CommRing A] :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} (adicModuleRing X A)) :=
  have := (finitePerfectAdicConstant_exact X A).1
  have := (finitePerfectAdicConstant_exact X A).2.1
  have := (finitePerfectAdicConstant_exact X A).2.2
  (finitePerfectAdicConstant X A).mapDerivedCategory

/-- A normalized algebraic quotient system, including its actual adjunctions.
Source: Stacks Tags 09AW and 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
structure FinitePerfectAdicAlgebraTower {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) where
  level : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  transition : ∀ n : ℕ, level (n + 1) ⟶
    (DerivedCategory.adicStepRestriction d.ideal n).obj (level n)
  extension : ∀ n : ℕ, DerivedCategory (ModuleCat.{t} A) ⥤
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  adjunction : ∀ n : ℕ, extension n ⊣ DerivedCategory.adicLevelRestriction d.ideal n
  stepExtension : ∀ n : ℕ,
    DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1)))
  stepAdjunction : ∀ n : ℕ, stepExtension n ⊣ DerivedCategory.adicStepRestriction d.ideal n
  normalized : ∀ n : ℕ, IsIso
    (((stepAdjunction n).homEquiv (level (n + 1)) (level n)).symm (transition n))
  residuePerfect : DerivedCategory.IsPerfect (level 0)

/-- Completed constant realization, followed by exact slice restriction.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicLocalRealization (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt) :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  finitePerfectAdicDerivedConstant X A ⋙
    completedAdicDerivedChange X (completedAdicScalar X d) ⋙
      ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- The levelwise derived diagram of the specified strict tower, restricted to a slice.
Source: Stacks Tags 0940 and 0941.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicRestrictedTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) :
    ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  (DerivedCategory.Q.objPreimage Z).asFunctor ⋙ DerivedCategory.Q ⋙
    ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- A compatible trivialization of the entire diagram, rather than unrelated level isomorphisms.
Source: Stacks Tag 09C6.
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
structure FinitePerfectAdicLocalTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) extends FinitePerfectAdicAlgebraTower d where
  comparison : Nonempty (finitePerfectAdicRestrictedTower X d U Z ≅
    Functor.ofOpSequence (X := fun n ↦
      (DerivedCategory.adicLevelRestriction d.ideal n).obj (level n))
      (DerivedCategory.adicTowerTransition d.ideal level transition) ⋙
      finitePerfectAdicLocalRealization X d U)

/-- The diagram realized by a specified algebraic quotient tower.
Source: Stacks Tag 09C6 (blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicModelDiagram (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt) (T : FinitePerfectAdicAlgebraTower d) :=
  Functor.ofOpSequence (X := fun n ↦
    (DerivedCategory.adicLevelRestriction d.ideal n).obj (T.level n))
    (DerivedCategory.adicTowerTransition d.ideal T.level T.transition) ⋙
    finitePerfectAdicLocalRealization X d U

/-- Regard a pro-etale object of an etale chart as an object over the original base.
Source: Stacks Tags 094T and 0951
(blueprint: def-weil-pbc-finite-perfect-adic-tower-data). -/
def finitePerfectAdicChartObject {X : Scheme.{t}} (V : X.Etale) (U : V.left.ProEt) :
    X.ProEt := ProEt.mk (U.hom ≫ V.hom)

end AlgebraicGeometry.Scheme
