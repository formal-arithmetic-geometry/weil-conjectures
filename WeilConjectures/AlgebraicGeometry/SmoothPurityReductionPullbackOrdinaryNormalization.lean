/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionMonoidalData

/-! # Ordinary normalization equations for a smooth-purity reduction pullback

Source: Stacks 03EL, 0D6D; blueprint integral direct-image proof (3).
(blueprint: lem-sp-reduction-pullback-ordinary-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The derived normalization and its comparison isomorphism are deliberately
omitted from this intermediate object. -/
structure SpReductionPullbackCore
    (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D') where
  integral : SheafOfModules.AlgebraicInverseImage
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    (spIntegralSectionRing l E T) (spIntegralSectionRing l E T')
  level : ∀ n : ℕ, SheafOfModules.AlgebraicInverseImage
    (Scheme.proEtaleSheafInverseImage g (Type (u + 1)))
    ((spCoefficientCommRings.{u, u} l E T).obj (op n))
    ((spCoefficientCommRings.{u, u} l E T').obj (op n))
  system : SheafOfModules.AlgebraicInverseImage
    (spMonoidalSequenceInverseImage T g)
    (spMonoidalSystemRing l E T) (spMonoidalSystemRing l E T')
  [integralAdditive : integral.modules.Additive]
  [integralLimits : PreservesFiniteLimits integral.modules]
  [integralColimits : PreservesFiniteColimits integral.modules]
  [systemAdditive : system.modules.Additive]
  [systemLimits : PreservesFiniteLimits system.modules]
  [systemColimits : PreservesFiniteColimits system.modules]
  evaluation : ∀ n : ℕ,
    system.modules ⋙ spMonoidalEvaluation l E T' n ≅
      spMonoidalEvaluation l E T n ⋙ (level n).modules
  ordinary : integral.modules ⋙ spMonoidalOrdinary l E T' D' r' ≅
    spMonoidalOrdinary l E T D r ⋙ system.modules

attribute [instance] SpReductionPullbackCore.integralAdditive
  SpReductionPullbackCore.integralLimits SpReductionPullbackCore.integralColimits
  SpReductionPullbackCore.systemAdditive SpReductionPullbackCore.systemLimits
  SpReductionPullbackCore.systemColimits

/-- Insert a candidate derived comparison into the ordinary pullback core.
The core fields are copied definitionally; only the `ν` field is supplied here.
Source: Stacks 03EL and 0G7E; blueprint integral direct-image proof (3). -/
def SpReductionPullbackCore.toData
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    (p : SpReductionPullbackCore l E T D r g D' r')
    (ν : p.integral.modules.mapDerivedCategory ⋙
      spMonoidalReduction l E T' D' r' ≅
      spMonoidalReduction l E T D r ⋙ p.system.modules.mapDerivedCategory) :
    SpReductionPullbackData l E T D r g D' r' where
  integral := p.integral
  level := p.level
  system := p.system
  evaluation := p.evaluation
  ordinary := p.ordinary
  ν := ν

/-- The ordinary equations are independent of the eventual choice of ν. -/
structure SpReductionPullbackOrdinaryData
    (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTower l E T D) {T' : Scheme.{u}} (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D')
    where
  core : SpReductionPullbackCore l E T D r g D' r'
  constant : ∀ ν, SpPullbackConstant l E T D r g D' r'
    (SpReductionPullbackCore.toData l E T D r g D' r' core ν)
  projection : ∀ ν, SpPullbackProjection l E T D r g D' r'
    (SpReductionPullbackCore.toData l E T D r g D' r' core ν)
  system_ring : ∀ ν, SpPullbackSystemRing l E T D r g D' r'
    (SpReductionPullbackCore.toData l E T D r g D' r' core ν)
  evaluation_section : ∀ ν,
    SpPullbackEvaluationSection l E T D r g D' r'
      (SpReductionPullbackCore.toData l E T D r g D' r' core ν)
  ordinary_section : ∀ ν,
    SpPullbackOrdinarySection l E T D r g D' r'
      (SpReductionPullbackCore.toData l E T D r g D' r' core ν)

/-- The ordinary coefficient, projection, system-ring, evaluation, and tensor-section
normalizations for canonical algebraic pullback data, stored independently of the later
derived comparison isomorphism.

Source: Stacks Project, Tags 03EL and 0D6D; blueprint integral direct-image proof (3).
Proof: evaluate the ringed inverse-image maps on Kan-extension generators. Constant
sections are fixed by the adjunction unit; naturality gives the projection equation and
identifies the sequence-site ring map with the level coefficient map. The module
adjunction and tensor universal property then give the evaluation and ordinary-section
equations. All equations are before localization, so no K-flat or flatness hypothesis is
used; identity and empty schemes are included. The equations are recorded uniformly for
every possible derived comparison, since they only inspect the ordinary core fields.
(blueprint: lem-sp-reduction-pullback-ordinary-normalization). -/
theorem sp_reduction_pullback_ordinary_normalization
    (hl : ∀ x : T, IsUnit (l : T.residueField x))
    (D : SpCoefficientTowersAbelian l E T) (r : SpReductionTower l E T D)
    {T' : Scheme.{u}} (hl' : ∀ x : T', IsUnit (l : T'.residueField x)) (g : T' ⟶ T)
    (D' : SpCoefficientTowersAbelian l E T') (r' : SpReductionTower l E T' D') :
    Nonempty (SpReductionPullbackOrdinaryData l E T D r g D' r') := by
  sorry

end AlgebraicGeometry.ProEtale
