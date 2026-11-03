/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalCoefficientRefinementExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import all WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.AlgebraicGeometry.CondensedPullIsoBalancedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate

/-! # Scalar transport of the original coefficient exchange

Source: Stacks Project, Tags 07A7 and 0E47, the scalar/geometric mate rectangle.
(blueprint: lem-sp-original-coefficient-scalar-exchange)
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option cleanup.letToHave false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open QuotientChange

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
attribute [local instance] finiteProperCache2 finiteProperCache3 finiteProperCache4
  finiteProperCache5 finiteProperCache6 finiteProperCache7 finiteProperCache8
  finiteProperCache9 finiteProperCache10 finiteProperCache12

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

noncomputable local instance :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory _ _

attribute [local semireducible] D L F adj
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  upperStar lowerStar upperStarFromPoint Functor.mapDerivedCategory
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarComp
  condensedAmbientExchange CategoryTheory.mateEquiv
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem normalized_rho_eq
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a]
    [∀ T : Scheme.{u}, PreservesFiniteLimits (extension a T)]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (b : D a Y ⋙ L S f ≅ L R f ⋙ D a X) (hb : PullNormalized a f b) :
    rho a f b = derivedPushHom a f := by
  rw [condensed_pull_iso_balanced_comparison a f b hb]
  unfold rho inverseConjugatePullComparison
  exact (derivedPushHom_eq_mateEquiv a f).symm

private theorem refinement_eq_condensed
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare a b f g) :
    refinementAmbientExchange R sq = condensedAmbientExchange R sq := by
  unfold refinementAmbientExchange condensedAmbientExchange
  rw [coefficientDerivedAdjunction_eq, coefficientDerivedAdjunction_eq,
    coefficientAmbientSquare_eq, coefficientIsoTransThree_eq]
  rfl

set_option maxHeartbeats 1600000 in
-- Normalize the two scalar/geometric mate rectangles over internal module categories.
private theorem scalar_exchange_forward
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (φ : R ⟶ T) [IsMonHom φ]
    [∀ W : Scheme.{u}, PreservesFiniteLimits (extension φ W)]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare a b f g)
    (K : DerivedCategory (Modules R X))
    (hK : IsIso ((condensedAmbientExchange R sq).app K))
    (hf : IsIso ((derivedPushHom φ f).app K))
    (hb : IsIso ((derivedPushHom φ b).app ((L R a).obj K))) :
    IsIso ((condensedAmbientExchange T sq).app ((D φ X).obj K)) := by
  let : ∀ W : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules R W) := sectionDerived R
  let : ∀ W : Scheme.{u}, HasDerivedCategory.{u + 1}
      (ModuleRingedComparison.modules T W) := sectionDerived T
  let β := @chosenScalarPull.{u} R T _ _ _ _ φ _
  have hβ {U V : Scheme.{u}} (q : U ⟶ V) : PullNormalized φ q (β q) :=
    chosenScalarPull_normalized φ q
  have hw := NatTrans.congr_app (IntegralQuotient.internal_rectangle φ β hβ sq) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hw
  rw [quotient_ambient_eq R sq, quotient_ambient_eq T sq,
    normalized_rho_eq φ f (β f) (hβ f), normalized_rho_eq φ b (β b) (hβ b)] at hw
  let := hK
  let := hf
  let := hb
  have hc : IsIso (((L T g).map ((derivedPushHom φ f).app K) ≫
      (condensedAmbientExchange T sq).app ((D φ X).obj K)) ≫
      (F T b).map ((β a).hom.app K)) := by
    rw [Category.assoc, hw]
    infer_instance
  have : IsIso ((L T g).map ((derivedPushHom φ f).app K) ≫
      (condensedAmbientExchange T sq).app ((D φ X).obj K)) :=
    IsIso.of_isIso_comp_right _ ((F T b).map ((β a).hom.app K))
  exact IsIso.of_isIso_comp_left ((L T g).map ((derivedPushHom φ f).app K)) _


set_option maxHeartbeats 800000 in
-- Compare the canonical derived-category instances by structural proof congruence.
/-- Scalar transport of the literal ordinary exchange, provided the two specified
scalar/direct-image mates are invertible at the indicated inputs.

Source: Stacks Project, Tags 07A7 and 0E47.
(blueprint: lem-sp-original-coefficient-scalar-exchange)

Proof: normalize the coefficient adjunctions and inverse-image compositors to the
ordinary module-object interfaces. The scalar/geometric mate rectangle identifies
pullback of the first direct-image comparison, followed by the new-coefficient
exchange and the invertible top balancing map, with scalar extension of the old
exchange followed by the second direct-image comparison. Every factor on this
second route is invertible. Cancel the first and last invertible factors of the
first route. This uses no properness, constructibility, or Noetherian assumption. -/
theorem originalCoefficientScalarExchange
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (φ : R ⟶ T) [IsMonHom φ]
    [∀ W : Scheme.{u}, PreservesFiniteLimits (extension φ W)]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare a b f g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X)))
    (hK : IsIso ((refinementAmbientExchange R sq).app K))
    (hf : IsIso ((derivedPushHom φ f).app K))
    (hb : IsIso ((derivedPushHom φ b).app
      ((upperStar R a).leftDerivedFunctor.obj K))) :
    IsIso ((refinementAmbientExchange T sq).app
      ((extension φ X).leftDerivedFunctor.obj K)) := by
  rw [refinement_eq_condensed] at hK ⊢
  have hb' : IsIso ((derivedPushHom φ b).app ((L R a).obj K)) := by
    refine Eq.mp ?_ hb
    run_tac coefficientCongrGoal
  have h := scalar_exchange_forward φ sq K hK hf hb'
  refine Eq.mp ?_ h
  run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.CondensedRing
