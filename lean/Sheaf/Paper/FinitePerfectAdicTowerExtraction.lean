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

/-! # The algebraic tower underlying local finite perfect models

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
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-extraction). -/
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
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-extraction). -/
def finitePerfectAdicLocalRealization (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt) :
    DerivedCategory (ModuleCat.{t} A) ⥤
      DerivedCategory (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  finitePerfectAdicDerivedConstant X A ⋙
    completedAdicDerivedChange X (completedAdicScalar X d) ⋙
      ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- The levelwise derived diagram of the specified strict tower, restricted to a slice.
Source: Stacks Tags 0940 and 0941.
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-extraction). -/
def finitePerfectAdicRestrictedTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) :
    ℕᵒᵖ ⥤ DerivedCategory
      (SheafOfModules.{t + 1} ((completedAdicRing X d).over U)) :=
  (DerivedCategory.Q.objPreimage Z).asFunctor ⋙ DerivedCategory.Q ⋙
    ringedDerivedRestrictionGeneral.{t + 1, t, t + 1, t + 1} (completedAdicRing X d) U

/-- A compatible trivialization of the entire diagram, rather than unrelated level isomorphisms.
Source: Stacks Tag 09C6.
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-extraction). -/
structure FinitePerfectAdicLocalTower (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (U : X.ProEt)
    (Z : DerivedCategory (CompletedAdicTowers X d)) extends FinitePerfectAdicAlgebraTower d where
  comparison : Nonempty (finitePerfectAdicRestrictedTower X d U Z ≅
    Functor.ofOpSequence (X := fun n ↦
      (DerivedCategory.adicLevelRestriction d.ideal n).obj (level n))
      (DerivedCategory.adicTowerTransition d.ideal level transition) ⋙
      finitePerfectAdicLocalRealization X d U)

/-- Uniform finite perfect local models admit compatible algebraic stalk trivializations.

Source: Stacks Project, Tag 09C6, the choice of the algebraic stalk system and of
compatible local markings, using Tags 09B1 and 09BV.
(blueprint: lem-weil-pbc-finite-perfect-adic-tower-extraction).

Proof: refine the given etale covering by connected Noetherian affine neighborhoods.
At each finite level descend the given complex by finite-ring derived comparison.
Its cohomology is finite locally constant and lies in the fixed interval. Full
faithfulness descends the actual consecutive quotient maps, and their adjoint
transposes are isomorphisms by associativity of derived tensor. Take the exact
geometric stalk of this normalized diagram at a point of each nonempty neighborhood;
its residue term is perfect by the prescribed perfect local model. Derived extension
and exact restriction are adjoint, both for the base ring and consecutive quotients.
The finite-ring local-constancy theorem identifies each descended complex locally
with this stalk model. The finite locally constant Isom sheaves have nonempty stalks;
the compatible finite-derived-trivialization theorem gives one pro-etale covering
and commuting markings on it. Forgetting the quotient scalars and applying the
normalized finite-coefficient comparisons yields an isomorphism of the entire
restricted strict diagram with the completed constant realization of the algebraic
system. Transitivity assembles the refinements; empty neighborhoods contribute the
empty covering. This construction does not take a limit or choose a perfect
representative over the base ring. -/
theorem finitePerfectAdicTower_extraction
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (hmodels : HasUniformFinitePerfectModels X d φ M) :
    ∃ S : Sieve (⊤_ X.ProEt), S ∈ ProEt.topology X (⊤_ X.ProEt) ∧
      ∀ (U : X.ProEt) (f : U ⟶ ⊤_ X.ProEt), S f →
        Nonempty (FinitePerfectAdicLocalTower X d U ((completedAdicReduction X d).obj M)) := by
  sorry

end AlgebraicGeometry.Scheme
