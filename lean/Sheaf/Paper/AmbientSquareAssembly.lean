/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.DerivedExchangeExactNormalization
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.RationalTatePullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- Ambient square assembly: expand the pullback comparison and cancel the
published compositor. The two leg equations and commutativity of the square
reduce the result to associativity.
(blueprint: lem-sfb-ambient-square-assembly) -/
theorem ambient_square_assembly
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (Modules Λ Y)} {B : DerivedCategory (Modules Λ X)}
    {B' : DerivedCategory (Modules Λ Y')} {Q : DerivedCategory (Modules Λ X')}
    (e : (moduleObjectDerivedPullback Λ f).obj A ⟶ B)
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ B')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ Q)
    (e₂ : (moduleObjectDerivedPullback Λ f').obj B' ⟶ Q)
    (s₁ : (CondensedRing.upperStar Λ (g' ≫ f)).leftDerivedFunctor.obj A ⟶ Q)
    (s₂ : (CondensedRing.upperStar Λ (f' ≫ g)).leftDerivedFunctor.obj A ⟶ Q)
    (h₁ : (CondensedRing.leftDerivedUpperStarComp Λ g' f).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e ≫ d = s₁)
    (h₂ : (CondensedRing.leftDerivedUpperStarComp Λ f' g).hom.app A ≫
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂ = s₂)
    (he : (eqToIso (congrArg (fun a : X' ⟶ Y ↦ (CondensedRing.upperStar Λ a).leftDerivedFunctor)
      sq.toCommSq.w.symm)).hom.app A ≫ s₁ = s₂) :
    (condensedAmbientPullbackComparison Λ sq).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂ := by sorry
end AlgebraicGeometry.ProEtale.RationalP1
