/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.ZetaWeil.OrdinaryCompactCohomology
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-! # Proper comparison of entire integral direct-image towers

Source: Weil blueprint, sec-zeta-weil/sk-input-weights,
prop-weil-proper-compact-coincidence.proof.md, first paragraph; Zheng,
Construction 4.1 and Lemma 4.10; Stacks Tags 0941 and 07A6
(blueprint: lem-weil-proper-integral-tower-comparison).

The comparison is constructed on actual strict systems, before evaluation or total
inverse limit. The native integral functors use the fixed total-derived-limit model.
The recorded compact-support functor is identified by its projection-normalized
realization. Natural index n denotes positive exponent n+1 throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open CategoryTheory.Functor

namespace WeilConjectures.ProperIntegralTower
open FrobeniusExchange

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Identity open extension, fixed by its ordinary section-normalized adjunction.
Source: Stacks 03DI, 03CY; Zheng 4.1
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def identityOpen (X : Scheme.{u}) : systemDerivedOpen l E (𝟙 X) ≅ 𝟭 _ :=
  ((systemDerivedOpenAdjunction l E (𝟙 X)).ofNatIsoRight
    (integralComparisonSystemUnit l E X)).leftAdjointUniq Adjunction.id

/-- Apply system direct image to the identity-open isomorphism, retaining all transitions.
Source: Zheng 4.10; blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def systemComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemDerivedOpen l E (𝟙 X) ⋙ systemDirect l E f ≅ systemDirect l E f :=
  isoWhiskerRight (identityOpen l E X) _ ≪≫ Functor.leftUnitor _

/-- The specified strict compact-support tower at the identity compactification.
Source: Zheng 4.1; blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def shriekTower {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  reduction l E X ⋙ (systemDerivedOpen l E (𝟙 X) ⋙ systemDirect l E f) ⋙
    coefficientSequenceDerivedRestriction l E Y

/-- The specified strict ordinary direct-image tower, with completed integral scalars.
Source: Zheng 4.10; blueprint def-weil-derived-direct-image
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def starTower {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  reduction l E X ⋙ systemDirect l E f ⋙ coefficientSequenceDerivedRestriction l E Y

/-- The actual natural isomorphism of full strict towers, formed before localization
at finite evaluations. Source: Zheng 4.1, 4.10
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def towerComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    shriekTower l E f ≅ starTower l E f :=
  isoWhiskerLeft (reduction l E X)
    (isoWhiskerRight (systemComparison l E f) (coefficientSequenceDerivedRestriction l E Y))

/-- The identity-compactification finite comparison Rf_*(a_n), on all ambient complexes.
Source: Stacks 03DI; blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def finiteComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (n : ℕ) :
    sfIntrinsicCompactSupport (Compactification.ofIsProper f)
        (Padic.coefficientExtensionRing l E (n + 1)) ≅
      proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  isoWhiskerRight
    (sfIntrinsicDerivedOpenId (Padic.coefficientExtensionRing l E (n + 1)) X) _ ≪≫
      Functor.leftUnitor _

/-- The natural integral comparison is the total-derived-limit image of the strict
comparison, with this one fixed total-limit model. Source: Stacks 0941
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def nativeIntegralComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    shriekTower l E f ⋙ coefficientConstantTowerLimit l E Y ≅
      starTower l E f ⋙ coefficientConstantTowerLimit l E Y :=
  isoWhiskerRight (towerComparison l E f) (coefficientConstantTowerLimit l E Y)

/-- The comparison on the recorded integral compact-support functor, using its unique
projection-normalized strict-system realization. Source: Bhatt--Scholze 6.7.6;
blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def integralComparison (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f] :
    sfCompactSupportFiniteIntegralFunctor l D.k (finiteFieldDatumPrimeUnit D l hl)
        (Compactification.ofIsProper f) E ⋙ (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ integralDirectImage l E f :=
  letI : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (Eq.mp (congrArg IsUnit (map_natCast
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop ≫
        X.Γevaluation x).hom) l))
      ((finiteFieldDatumPrimeUnit D l hl).map
        (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop ≫
          X.Γevaluation x).hom))).invertible
  letI : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
    (Eq.mp (congrArg IsUnit (map_natCast
      (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop ≫
        Y.Γevaluation y).hom) l))
      ((finiteFieldDatumPrimeUnit D l hl).map
        (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop ≫
          Y.Γevaluation y).hom))).invertible
  compactRealization l E D.k (finiteFieldDatumPrimeUnit D l hl) f
      (Compactification.ofIsProper f) ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E X).ι (nativeIntegralComparison l E f)

end WeilConjectures.ProperIntegralTower
