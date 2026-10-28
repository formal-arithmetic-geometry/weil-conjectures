/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.Paper.DerivedExchangeExactNormalization
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.RationalTatePullback
public import Sheaf.Paper.RationalP1ScalarChernMaps
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing
/-- Ambient twisted-unit mate assembly. Apply `unit_mateEquiv`, then use
naturality of the exchange and the two adjunction units.
(blueprint: lem-sfb-ambient-twisted-unit-mate) -/
theorem ambient_twisted_unit_mate
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)
    {A : DerivedCategory (Modules Λ Y)} {B : DerivedCategory (Modules Λ X)}
    {B' : DerivedCategory (Modules Λ Y')} {Q : DerivedCategory (Modules Λ X')}
    (e : (moduleObjectDerivedPullback Λ f).obj A ≅ B)
    (j : (moduleObjectDerivedPullback Λ g).obj A ⟶ B')
    (d : (moduleObjectDerivedPullback Λ g').obj B ⟶ Q)
    (e₂ : (moduleObjectDerivedPullback Λ f').obj B' ≅ Q)
    (h : (condensedAmbientPullbackComparison Λ sq).hom.app A ≫
      (moduleObjectDerivedPullback Λ g').map e.hom ≫ d =
      (moduleObjectDerivedPullback Λ f').map j ≫ e₂.hom) :
    (moduleObjectDerivedPullback Λ g).map (scalarTwistedUnit Λ f A B e) ≫
      (condensedAmbientExchange Λ sq).app B ≫
      (moduleObjectDerivedPushforward Λ f').map d =
      j ≫ scalarTwistedUnit Λ f' B' Q e₂ := by sorry
end AlgebraicGeometry.ProEtale.RationalP1
