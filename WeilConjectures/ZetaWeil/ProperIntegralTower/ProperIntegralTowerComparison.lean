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
import WeilConjectures.ZetaWeil.FrobeniusExchange.IdentityOpenSystemEvaluation
import WeilConjectures.ZetaWeil.FrobeniusExchange.ProperSystemEvaluationTransitions

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

/-- The specified term map theta_n is the completed-coefficient restriction of Rf_*(a_n).
Source: blueprint proper-coincidence proof, first paragraph
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def termComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    sfCompactSupportTerm l E (Compactification.ofIsProper f) K n ≅
      sfDirectImageTerm l E f K n :=
  (scalarReductionDerivedRestriction l E Y n).mapIso
    ((finiteComparison l E f n).app ((scalarReductionDerivedExtension l E X n).obj K))

/-- The normalized evaluation of the compact-support strict tower.
Source: Zheng 4.10, canonical finite evaluation and completed-coefficient restriction
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def shriekEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientConstantTowerEvaluation l E Y n).obj ((shriekTower l E f).obj K) ≅
      sfCompactSupportTerm l E (Compactification.ofIsProper f) K n :=
  (coefficientRestrictedEvaluationIso l E Y n).app
      (((reduction l E X) ⋙
        (systemDerivedOpen l E (𝟙 X) ⋙ systemDirect l E f)).obj K) ≪≫
    (scalarReductionDerivedRestriction l E Y n).mapIso
      ((compactFiniteEvaluation l E (Compactification.ofIsProper f) n).app K)

/-- The normalized evaluation of the ordinary strict tower uses the canonical
system-direct-image mate and actual reduction evaluation. Source: Zheng 4.10
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def starEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientConstantTowerEvaluation l E Y n).obj ((starTower l E f).obj K) ≅
      sfDirectImageTerm l E f K n :=
  letI := systemDirectEvaluation_isIso l E f n
  (coefficientRestrictedEvaluationIso l E Y n).app
      (((reduction l E X) ⋙ systemDirect l E f).obj K) ≪≫
    (scalarReductionDerivedRestriction l E Y n).mapIso
      ((asIso (systemDirectEvaluation l E f n)).app ((reduction l E X).obj K) ≪≫
        (proEtaleConstantDerivedDirectImage f
          (Padic.coefficientExtensionRing l E (n + 1))).mapIso
            ((((models l E).system X).reductionEvaluation n).app K))

/-- The natural integral comparison is the total-derived-limit image of the strict
comparison, with this one fixed total-limit model. Source: Stacks 0941
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def nativeIntegralComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    shriekTower l E f ⋙ coefficientConstantTowerLimit l E Y ≅
      starTower l E f ⋙ coefficientConstantTowerLimit l E Y :=
  isoWhiskerRight (towerComparison l E f) (coefficientConstantTowerLimit l E Y)

/-- The actual compact-support total-limit projection followed by normalized evaluation.
Source: Stacks 0941; blueprint specified derived-limit projections
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def shriekProjection {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (coefficientConstantTowerProjection l E Y n).app ((shriekTower l E f).obj K) ≫
    (shriekEvaluation l E f K n).hom

/-- The actual ordinary total-limit projection followed by normalized evaluation.
Source: Stacks 0941; blueprint specified derived-limit projections
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def starProjection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  (coefficientConstantTowerProjection l E Y n).app ((starTower l E f).obj K) ≫
    (starEvaluation l E f K n).hom

/-- The compact-support reduction is exactly the scalar-adjunction adjunct of its
chosen projection. Source: Stacks 07A6, 0941
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def shriekReduction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (shriekProjection l E f K n)

/-- The ordinary reduction is exactly the scalar-adjunction adjunct of its chosen
projection. Source: Stacks 07A6, 0941
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def starReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (starProjection l E f K n)

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

/-- The compact projection in the recorded functor is transported through precisely
its published projection-normalized realization. Source: Bhatt--Scholze 6.7.6; Stacks 0941
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def recordedProjection (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f]
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :=
  (integralComparison l E D hl f).hom.app K ≫
    (nativeIntegralComparison l E f).inv.app K.obj ≫ shriekProjection l E f K.obj n

/-- The recorded compact-support reduction is the adjunct of that same projection.
Source: Stacks 07A6; blueprint final displayed equation
(blueprint: lem-weil-proper-integral-tower-comparison). -/
def recordedReduction (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f]
    (K : sfIntegralConstructibleCategory l E X) (n : ℕ) :=
  ((derivedScalarExtensionRestrictionAdjunction l E Y n).choose.homEquiv _ _).symm
    (recordedProjection l E D hl f K n)

/-- The identity-open term maps compare the entire prescribed towers, naturally in K;
all transitions, actual total-limit projections and their scalar adjuncts agree.
Source: blueprint prop-weil-proper-compact-coincidence.proof.md, first paragraph;
Zheng, Construction 4.1 and Lemma 4.10; Stacks 0941, 07A6
(blueprint: lem-weil-proper-integral-tower-comparison).

Proof:
1. The DVR and completeness results lem-weil-l-adic-extension-integers-dvr and
lem-weil-l-adic-extension-complete imply R = lim R/t^n: compatible lifts are Cauchy,
converge in E, and the valuation bounds give the required residues and uniqueness.
2. Use lem-coef-derived-system-evaluation-calculus to reduce one K-flat representative,
with its actual quotient maps. The unconditional part of
lem-pur-coefficient-system-derived-comparison identifies system image and finite image,
including quotient transitions, without boundedness or etale-origin hypotheses.
3. Identity-open extension has exactly the original sections. Sheafification gives its
canonical identity comparison, natural in every semilinear map. Apply system direct
image and exact completed restriction to obtain towerComparison. Finite evaluation is
Rf_*(a_n). Naturality at the quotient map and the restriction square of
lem-weil-proper-finite-normalization give the displayed transition equation, also for
unbounded reductions; inverse components satisfy the inverse equation.
4. Apply the fixed total right-derived limit of
lem-weil-pbc-ringed-strict-tower-homotopy-limit. It preserves both inverse equations,
giving nativeIntegralComparison and hence integralComparison through the published
projection-normalized compact realization. All coefficients stay completed on Y.
5. Naturality of the actual projections of lem-coef-derived-tower-counit-projections
gives the projection square. Under
lem-weil-derived-scalar-extension-restriction-adjunction, naturality in source and target
transposes that square into the last equation. Neither reduction is claimed invertible.
-/
theorem proper_integral_tower_comparison
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (_inclusion : E →ₐ[ℚ_[l]] Ω)
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsProper f] :
    ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
      ((normalizedDVRTowerTransition l E Y D hl (Nat.le_succ n)).app
          ((shriekTower l E f).obj K.obj) ≫
          (shriekEvaluation l E f K.obj n).hom =
        (shriekEvaluation l E f K.obj (n + 1)).hom ≫
          sfCompactSupportTransition l E (Compactification.ofIsProper f) K.obj n) ∧
      ((normalizedDVRTowerTransition l E Y D hl (Nat.le_succ n)).app ((starTower l E f).obj K.obj) ≫
          (starEvaluation l E f K.obj n).hom =
        (starEvaluation l E f K.obj (n + 1)).hom ≫ sfDirectImageTransition l E f K.obj n) ∧
      ((coefficientConstantTowerEvaluation l E Y n).map
          ((towerComparison l E f).hom.app K.obj) ≫ (starEvaluation l E f K.obj n).hom =
        (shriekEvaluation l E f K.obj n).hom ≫ (termComparison l E f K.obj n).hom) ∧
      (sfCompactSupportTransition l E (Compactification.ofIsProper f) K.obj n ≫
          (termComparison l E f K.obj n).hom =
        (termComparison l E f K.obj (n + 1)).hom ≫ sfDirectImageTransition l E f K.obj n) ∧
      ((nativeIntegralComparison l E f).hom.app K.obj ≫ starProjection l E f K.obj n =
        shriekProjection l E f K.obj n ≫ (termComparison l E f K.obj n).hom) ∧
      ((scalarReductionDerivedExtension l E Y n).map
          ((nativeIntegralComparison l E f).hom.app K.obj) ≫ starReduction l E f K.obj n =
        shriekReduction l E f K.obj n ≫
          (finiteComparison l E f n).hom.app
            ((scalarReductionDerivedExtension l E X n).obj K.obj)) ∧
      ((integralComparison l E D hl f).hom.app K ≫ starProjection l E f K.obj n =
        recordedProjection l E D hl f K n ≫ (termComparison l E f K.obj n).hom) ∧
      (recordedReduction l E D hl f K n =
        (sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl)
          (Compactification.ofIsProper f) E K n).hom) ∧
      ((scalarReductionDerivedExtension l E Y n).map
          ((integralComparison l E D hl f).hom.app K) ≫ starReduction l E f K.obj n =
        recordedReduction l E D hl f K n ≫
          (finiteComparison l E f n).hom.app
            ((scalarReductionDerivedExtension l E X n).obj K.obj)) := by
  intro K n
  have hshriek :
      (normalizedDVRTowerTransition l E Y D hl (Nat.le_succ n)).app
          ((shriekTower l E f).obj K.obj) ≫ (shriekEvaluation l E f K.obj n).hom =
        (shriekEvaluation l E f K.obj (n + 1)).hom ≫
          sfCompactSupportTransition l E (Compactification.ofIsProper f) K.obj n := by
    exact (proper_system_evaluation_transitions l E D hl f K.obj n).1
  have hstar :
      (normalizedDVRTowerTransition l E Y D hl (Nat.le_succ n)).app
          ((starTower l E f).obj K.obj) ≫ (starEvaluation l E f K.obj n).hom =
        (starEvaluation l E f K.obj (n + 1)).hom ≫
          sfDirectImageTransition l E f K.obj n := by
    exact (proper_system_evaluation_transitions l E D hl f K.obj n).2
  have heval (i : ℕ) :
      (coefficientConstantTowerEvaluation l E Y i).map
          ((towerComparison l E f).hom.app K.obj) ≫ (starEvaluation l E f K.obj i).hom =
        (shriekEvaluation l E f K.obj i).hom ≫ (termComparison l E f K.obj i).hom := by
    let := systemDirectEvaluation_isIso l E f i
    let := systemOpenEvaluationInv_isIso l E (𝟙 X) i
    let R := scalarReductionDerivedRestriction l E Y i
    let F := proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (i + 1))
    let M := (reduction l E X).obj K.obj
    have hn := (coefficientRestrictedEvaluationIso l E Y i).hom.naturality
      ((systemComparison l E f).hom.app M)
    have hd := (systemDirectEvaluation l E f i).naturality ((identityOpen l E X).hom.app M)
    have hi := identity_open_system_evaluation l E X i M
    dsimp only [towerComparison, starEvaluation, shriekEvaluation, termComparison,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, shriekTower, starTower, Functor.comp_obj]
    dsimp only [Functor.comp_map, Functor.comp_obj, M] at hn
    rw [← Category.assoc, hn]
    simp only [coefficientFiniteDerivedRestriction, Category.assoc, ← Functor.map_comp]
    apply congrArg (fun z ↦ (coefficientRestrictedEvaluationIso l E Y i).hom.app _ ≫
      R.map z)
    change (coefficientSequenceDerivedEvaluation l E Y i).map
        ((systemComparison l E f).hom.app M) ≫
          (systemDirectEvaluation l E f i).app M ≫ F.map
            ((((models l E).system X).reductionEvaluation i).hom.app K.obj) =
      (compactFiniteEvaluation l E (Compactification.ofIsProper f) i).hom.app K.obj ≫
        (finiteComparison l E f i).hom.app
          ((scalarReductionDerivedExtension l E X i).obj K.obj)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hd
    simp only [systemComparison, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
    erw [Category.comp_id]
    erw [← Category.assoc, hd]
    erw [hi]
    dsimp only [compactFiniteEvaluation, Compactification.ofIsProper, finiteComparison,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
    have ha := (sfIntrinsicDerivedOpenId
      (Padic.coefficientExtensionRing l E (i + 1)) X).hom.naturality
        ((((models l E).system X).reductionEvaluation i).hom.app K.obj)
    dsimp only [Functor.id_map] at ha
    erw [Category.comp_id]
    rw [← F.map_comp]
    erw [← ha]
    simp only [sfIntrinsicCompactSupport, Functor.comp_map, Functor.map_comp]
    rfl
  have htransition :
      sfCompactSupportTransition l E (Compactification.ofIsProper f) K.obj n ≫
          (termComparison l E f K.obj n).hom =
        (termComparison l E f K.obj (n + 1)).hom ≫
          sfDirectImageTransition l E f K.obj n := by
    apply (cancel_epi (shriekEvaluation l E f K.obj (n + 1)).hom).mp
    rw [← Category.assoc, ← hshriek]
    simp only [Category.assoc]
    rw [← heval n]
    rw [← Category.assoc, ← Category.assoc]
    have ht := (normalizedDVRTowerTransition l E Y D hl n.le_succ).naturality
      ((towerComparison l E f).hom.app K.obj)
    have ht' :
        (coefficientConstantTowerEvaluation l E Y (n + 1)).map
            ((towerComparison l E f).hom.app K.obj) ≫
          (normalizedDVRTowerTransition l E Y D hl n.le_succ).app
            ((starTower l E f).obj K.obj) =
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app
            ((shriekTower l E f).obj K.obj) ≫
          (coefficientConstantTowerEvaluation l E Y n).map
            ((towerComparison l E f).hom.app K.obj) := ht
    rw [← ht']
    simp only [Category.assoc]
    rw [hstar, ← Category.assoc, heval (n + 1)]
    simp only [Category.assoc]
  have hprojection :
      (nativeIntegralComparison l E f).hom.app K.obj ≫ starProjection l E f K.obj n =
        shriekProjection l E f K.obj n ≫ (termComparison l E f K.obj n).hom := by
    change (coefficientConstantTowerLimit l E Y).map
        ((towerComparison l E f).hom.app K.obj) ≫
          ((coefficientConstantTowerProjection l E Y n).app _ ≫ _) = _
    rw [← Category.assoc, (coefficientConstantTowerProjection l E Y n).naturality]
    simp only [Category.assoc]
    rw [heval n]
    simp only [shriekProjection, Category.assoc]
  have hreduction :
      (scalarReductionDerivedExtension l E Y n).map
          ((nativeIntegralComparison l E f).hom.app K.obj) ≫ starReduction l E f K.obj n =
        shriekReduction l E f K.obj n ≫
          (finiteComparison l E f n).hom.app
            ((scalarReductionDerivedExtension l E X n).obj K.obj) := by
    unfold starReduction shriekReduction
    exact (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
      |>.homEquiv_naturality_right_square _ _ _ _ hprojection
  have hrecorded :
      (integralComparison l E D hl f).hom.app K ≫ starProjection l E f K.obj n =
        recordedProjection l E D hl f K n ≫ (termComparison l E f K.obj n).hom := by
    unfold recordedProjection
    simp only [Category.assoc]
    rw [← hprojection]
    simp only [Iso.inv_hom_id_app_assoc]
  have hrecordedReduction :
      recordedReduction l E D hl f K n =
        (sfCompactSupportFiniteReductionIso l D.k (finiteFieldDatumPrimeUnit D l hl)
          (Compactification.ofIsProper f) E K n).hom := by
    let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
      (Eq.mp (congrArg IsUnit (map_natCast
        (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop ≫
          X.Γevaluation x).hom) l))
        ((finiteFieldDatumPrimeUnit D l hl).map
          (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop ≫
            X.Γevaluation x).hom))).invertible
    let : ∀ y : Y, Invertible (l : Y.residueField y) := fun y ↦
      (Eq.mp (congrArg IsUnit (map_natCast
        (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop ≫
          Y.Γevaluation y).hom) l))
        ((finiteFieldDatumPrimeUnit D l hl).map
          (((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop ≫
            Y.Γevaluation y).hom))).invertible
    let N := ((reduction l E X) ⋙
      (systemDerivedOpen l E (𝟙 X) ⋙ systemDirect l E f)).obj K.obj
    let a := (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    let q := (((models l E).system Y).reductionEvaluation n).inv.app
        ((coefficientSequenceLimit l E Y).obj N) ≫
      (coefficientSequenceDerivedEvaluation l E Y n).map
        (((models l E).system Y).adjunction.counit.app N)
    have hq : a.homEquiv _ _ q = (coefficientSequenceProjection l E Y n).app N :=
      ((models l E).system Y).counit_projection N n
    have hfinite := a.homEquiv_naturality_right q
      ((compactFiniteEvaluation l E (Compactification.ofIsProper f) n).hom.app K.obj)
    rw [hq] at hfinite
    have hp : a.homEquiv _ _
        (q ≫ (compactFiniteEvaluation l E (Compactification.ofIsProper f) n).hom.app
          K.obj) = shriekProjection l E f K.obj n := by
      simpa only [shriekProjection, shriekEvaluation, coefficientSequenceProjection,
        Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app,
        Functor.whiskerLeft_app, Category.assoc, shriekTower, N, Functor.comp_obj] using hfinite
    have hr : recordedProjection l E D hl f K n =
        (compactRealization l E D.k (finiteFieldDatumPrimeUnit D l hl) f
          (Compactification.ofIsProper f)).hom.app K ≫ shriekProjection l E f K.obj n := by
      simp only [recordedProjection, integralComparison, Iso.trans_hom, NatTrans.comp_app,
        isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.comp_obj,
        ObjectProperty.ι_obj, Category.assoc, Iso.hom_inv_id_app_assoc]
    have hs := (compactRealization_existsUnique l E D.k
      (finiteFieldDatumPrimeUnit D l hl) f (Compactification.ofIsProper f)).exists.choose_spec
    have hspec := hs K n
    have hp' : (a.homEquiv _ _).symm (shriekProjection l E f K.obj n) =
        q ≫ (compactFiniteEvaluation l E (Compactification.ofIsProper f) n).hom.app
          K.obj := by
      apply (a.homEquiv _ _).injective
      exact (Equiv.apply_symm_apply _ _).trans hp.symm
    change (a.homEquiv _ _).symm (recordedProjection l E D hl f K n) = _
    rw [hr]
    rw [a.homEquiv_naturality_left_symm]
    have h := congrArg (fun z ↦ (scalarReductionDerivedExtension l E Y n).map
      ((compactRealization l E D.k (finiteFieldDatumPrimeUnit D l hl) f
        (Compactification.ofIsProper f)).hom.app K) ≫ z) hp'
    refine h.trans ?_
    simpa only [CompactRealizationSpec, Functor.map_comp, Category.assoc, q, N,
      compactImage, realize, operationReduction, Functor.whiskerLeft_app, Functor.comp_obj,
      compactRealization, Compactification.ofIsProper, sfIntrinsicCompactSupport,
      sfAmbientCompactSupportCandidate] using hspec
  refine ⟨hshriek, hstar, heval n, htransition, hprojection, hreduction,
    hrecorded, hrecordedReduction, ?_⟩
  unfold starReduction recordedReduction
  exact (derivedScalarExtensionRestrictionAdjunction l E Y n).choose
    |>.homEquiv_naturality_right_square _ _ _ _ hrecorded

end WeilConjectures.ProperIntegralTower
