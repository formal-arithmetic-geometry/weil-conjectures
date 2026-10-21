/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.ProperBaseChangeFourArrows
import Sheaf.Paper.FiniteReductionPullbackCoherence
import Sheaf.CategoryTheory.Adjunction.CoefficientExchange
import Sheaf.CategoryTheory.AdjunctionSquareExchange

/-!
# Finite-level exchange rectangle

Source: blueprint, node `lem-weil-pbc-finite-level-rectangle`, order 1344;
Stacks Project, Tags 0E48, 0B56 and 07A7
(blueprint: lem-weil-pbc-finite-level-rectangle).

The arrows are the specified finite projection and exchange maps, with their
quotient-coefficient actions retained. Index n denotes the positive exponent n+1.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local instance 40000] adicDatumModulesAbelian
attribute [local instance 30000] proEtaleRingModules_hasDerivedCategory

attribute [local irreducible] fourCornerCoefficientIso fourCornerFiniteIso
  proEtaleAmbientRingedPullbackComparison proEtaleAmbientRingedExchange
  proEtaleRingDerivedAdjunction fourCornerReductionPullback adicDatumExtension
  proEtaleRingModulePullback proEtaleRingModuleDirectImage

variable {A : Type (t + 1)} [CommRing A]
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y}

private theorem projection_counit {U V : Scheme.{t}} (h : U ⟶ V)
    (d : ProEtaleAdicCoefficientDatum A) (n : ℕ)
    (L : fourCornerDerived U (adicDatumRing U d)) :
    (fourCornerFinitePullback h d n).map
    (fourArrowProjection h d L n) ≫
      (fourCornerFiniteDerivedAdjunction h d n).counit.app ((adicDatumReduction U d n).obj L) =
    (fourCornerReductionPullback h d n).inv.app ((fourCornerPushforward h d).obj L) ≫
      (adicDatumReduction U d n).map
        ((fourCornerDerivedAdjunction h d).counit.app L) := by
  exact Adjunction.squareExchange_map_counit
    (fourCornerDerivedAdjunction h d)
    (fourCornerFiniteDerivedAdjunction h d n)
    _ _ (fourArrowReductionPullback h d n) L

private theorem integralExchange_eq_mate
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A) :
    fourArrowIntegralExchangeNat sq d =
      (mateEquiv (fourCornerDerivedAdjunction f d) (fourCornerDerivedAdjunction f' d)
        (TwoSquare.mk _ _ _ _ (fourArrowIntegralPullbackComparison sq d).hom)).natTrans := by
  unfold fourArrowIntegralExchangeNat fourArrowIntegralPullbackComparison
    fourCornerDerivedAdjunction fourCornerPullback fourCornerPushforward
    proEtaleAmbientRingedExchange
  rfl

private theorem integralExchange_counit
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A)
    (L : fourCornerDerived X (adicDatumRing X d)) :
    (fourCornerPullback f' d).map ((fourArrowIntegralExchangeNat sq d).app L) ≫
      (fourCornerDerivedAdjunction f' d).counit.app ((fourCornerPullback g' d).obj L) =
    (fourArrowIntegralPullbackComparison sq d).hom.app ((fourCornerPushforward f d).obj L) ≫
      (fourCornerPullback g' d).map ((fourCornerDerivedAdjunction f d).counit.app L) := by
  rw [integralExchange_eq_mate]
  exact mateEquiv_counit (fourCornerDerivedAdjunction f d) (fourCornerDerivedAdjunction f' d)
    (TwoSquare.mk _ _ _ _ (fourArrowIntegralPullbackComparison sq d).hom) L

private theorem finiteExchange_eq_mate
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A) (n : ℕ) :
    fourArrowFiniteExchangeNat sq d n =
      (mateEquiv (fourCornerFiniteDerivedAdjunction f d n) (fourCornerFiniteDerivedAdjunction f' d
        n)
        (TwoSquare.mk _ _ _ _ (fourArrowFinitePullbackComparison sq d n).hom)).natTrans := by
  unfold fourArrowFiniteExchangeNat fourArrowFinitePullbackComparison
    fourCornerFiniteDerivedAdjunction fourCornerFinitePullback fourCornerFinitePushforward
    proEtaleAmbientRingedExchange
  rfl

private theorem finiteExchange_counit
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A) (n : ℕ)
    (L : DerivedCategory (proEtaleRingModules X
      ((adicLisseRingSystem X d.ideal).obj (Opposite.op n)))) :
    (fourCornerFinitePullback f' d n).map ((fourArrowFiniteExchangeNat sq d n).app L) ≫
      (fourCornerFiniteDerivedAdjunction f' d n).counit.app ((fourCornerFinitePullback g' d n).obj
        L) =
    (fourArrowFinitePullbackComparison sq d n).hom.app ((fourCornerFinitePushforward f d n).obj L) ≫
      (fourCornerFinitePullback g' d n).map ((fourCornerFiniteDerivedAdjunction f d n).counit.app L)
        := by
  rw [finiteExchange_eq_mate]
  exact mateEquiv_counit (fourCornerFiniteDerivedAdjunction f d n)
    (fourCornerFiniteDerivedAdjunction f' d n)
    (TwoSquare.mk _ _ _ _ (fourArrowFinitePullbackComparison sq d n).hom) L

private theorem finiteExchange_eq
    (sq : ChosenCartesianSquare g' f' f g) (d : ProEtaleAdicCoefficientDatum A)
    (K : fourCornerDerived X (adicDatumRing X d)) (n : ℕ) :
    fourArrowFiniteExchange sq d K n =
      (fourArrowFiniteExchangeNat sq d n).app ((adicDatumReduction X d n).obj K) := by
  unfold fourArrowFiniteExchange
  rfl

attribute [local irreducible] fourArrowFiniteExchange

/-- The canonical four-arrow exchange rectangle commutes at every positive level.
Source: blueprint order 1344; Stacks Remark 21.50.2, Tag 0E48, with the maps of
Tags 0B56 and 07A7 (blueprint: lem-weil-pbc-finite-level-rectangle).
Proof: the integral and finite exchange maps are the mates of the specified
geometric pullback comparisons. The finite projection maps are the counit
adjuncts of the inverse coefficient pullback comparisons. Compatibility of the
pullback comparisons with reduction gives a cube. Apply the coefficient-exchange
mate theorem to this cube, using the two exchange counit equations and the two
projection counit equations. Cancel the invertible coefficient comparison at g.
The components of the four-arrow tuple are exactly the maps in this equation;
associativity gives the displayed rectangle. The witness of finite exchange
invertibility only turns that same map into an isomorphism. -/
theorem properBaseChangeFiniteLevelRectangle
    (sq : ChosenCartesianSquare g' f' f g) [IsProper f]
    (d : ProEtaleAdicCoefficientDatum A) (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = d.ideal)
    (K : fourCornerDerived X (adicDatumRing X d))
    (C : CochainComplex (proEtaleRingModules X (adicDatumRing X d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ K)
    (hK : IsCompletedIntrinsicallyDerivedComplete X d r a ha C eC)
    (W : ∀ n : ℕ, ProEtale.FiniteCoefficientDerivedCategoryPlus X (fourArrowQuotient d n))
    (w : ∀ n : ℕ, ProEtale.EtaleOriginWitness X (fourArrowQuotient d n) (W n))
    (e : ∀ n : ℕ, (fourArrowOriginTransport X d n).obj (W n).obj ≅
      (adicDatumReduction X d n).obj K) (n : ℕ) :
    (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).1.hom ≫
        (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.2.2.hom =
      (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.2.1 ≫
        (properBaseChangeFourArrows sq d r a ha K C eC hK W w e n).2.1.hom := by
  change
    ((fourCornerFinitePullback g d n).map
    (fourArrowProjection f d K n)) ≫ (fourArrowFiniteExchange sq d K n) =
    ((fourCornerReductionPullback g d n).inv.app ((fourCornerPushforward f d).obj K) ≫
        (adicDatumReduction Y' d n).map
          ((fourArrowIntegralExchangeNat sq d).app K)) ≫ (fourArrowProjection f' d
    ((fourCornerPullback g' d).obj K) n ≫
        (fourCornerFinitePushforward f' d n).map
          ((fourCornerReductionPullback g' d n).hom.app K))
  have h := (@Adjunction.coefficient_exchange_of_counit_at
    (DerivedCategory (proEtaleRingModules Y (adicDatumRing Y d)))
    (DerivedCategory (proEtaleRingModules X (adicDatumRing X d)))
    (DerivedCategory (proEtaleRingModules Y' (adicDatumRing Y' d)))
    (DerivedCategory (proEtaleRingModules X' (adicDatumRing X' d)))
    (DerivedCategory (proEtaleRingModules Y ((adicLisseRingSystem Y d.ideal).obj (Opposite.op n))))
    (DerivedCategory (proEtaleRingModules X ((adicLisseRingSystem X d.ideal).obj (Opposite.op n))))
    (DerivedCategory (proEtaleRingModules Y' ((adicLisseRingSystem Y' d.ideal).obj (Opposite.op
      n))))
    (DerivedCategory (proEtaleRingModules X' ((adicLisseRingSystem X' d.ideal).obj (Opposite.op
      n))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules Y
      (adicDatumRing Y d))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules X
      (adicDatumRing X d))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules Y'
      (adicDatumRing Y' d))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules X'
      (adicDatumRing X' d))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules Y
      ((adicLisseRingSystem Y d.ideal).obj (Opposite.op n)))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules X
      ((adicLisseRingSystem X d.ideal).obj (Opposite.op n)))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules Y'
      ((adicLisseRingSystem Y' d.ideal).obj (Opposite.op n)))))
    (instCategoryDerivedCategory _ : Category (DerivedCategory (proEtaleRingModules X'
      ((adicLisseRingSystem X' d.ideal).obj (Opposite.op n))))))
    (U := fourCornerPullback f d) (R := fourCornerPushforward f d)
    (V := fourCornerPullback f' d) (S := fourCornerPushforward f' d)
    (Ue := fourCornerFinitePullback f d n) (Re :=
    fourCornerFinitePushforward f d n)
    (Ve := fourCornerFinitePullback f' d n) (Se :=
    fourCornerFinitePushforward f' d n)
    (G := fourCornerPullback g d) (H := fourCornerPullback g' d)
    (Ge := fourCornerFinitePullback g d n) (He :=
    fourCornerFinitePullback g' d n)
    (T₁ := adicDatumReduction Y d n) (T₂ := adicDatumReduction X d n)
    (T₃ := adicDatumReduction Y' d n) (T₄ := adicDatumReduction X' d n)
    (fourCornerDerivedAdjunction f d)
    (fourCornerDerivedAdjunction f' d)
    (fourCornerFiniteDerivedAdjunction f d n)
    (fourCornerFiniteDerivedAdjunction f' d n)
    (fourArrowIntegralPullbackComparison sq d).hom (fourArrowFinitePullbackComparison sq d n).hom
    K ((fourArrowIntegralExchangeNat sq d).app K)
    ((fourArrowFiniteExchangeNat sq d n).app ((adicDatumReduction X d n).obj K))
    (integralExchange_counit sq d K)
    (finiteExchange_counit sq d n ((adicDatumReduction X d n).obj K))
    (fourCornerReductionPullback f d n) (fourCornerReductionPullback f' d n)
    (fourCornerReductionPullback g d n).hom (fourCornerReductionPullback g' d n).hom
    (fourArrowProjection f d K n)
    (fourArrowProjection f' d ((fourCornerPullback g' d).obj K) n)
    (projection_counit f d n K)
    (projection_counit f' d n ((fourCornerPullback g' d).obj K))
    (fourCornerReductionPullback_square sq d n
      ((fourCornerPushforward f d).obj K))
  simpa only [Category.assoc, finiteExchange_eq, Iso.app_inv,
    Functor.comp_obj] using
    (Iso.eq_inv_comp ((fourCornerReductionPullback g d n).app
      ((fourCornerPushforward f d).obj K))).2 h


end AlgebraicGeometry.Scheme
