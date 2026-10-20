/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.Paper.IntegralTowerInverseImageUnit
public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.SfIntegralCompactSupportConstructible
public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.Paper.SystemOperationExchangeRealization
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.Paper.IntegralPointTransportTowerPowers
public import Sheaf.Paper.FrobeniusGeometricExchange
public import Sheaf.SixFunctors.SchemeFrobenius
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization
import Sheaf.TraceFormula.CompactSupportSystemEvaluationCoherence
import Sheaf.Paper.IntegralInverseImageComparisonComposition
import Sheaf.Paper.IsomorphismReductionTower
import Sheaf.Paper.ExactProductFunctorStrictLimit
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.BasicOperationsCoefficientReduction
import Sheaf.Paper.IsomorphismDerivedPullback
import Sheaf.Paper.IntegralFinitePullbackComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.IntegralPullbackComparisonRealization
import Sheaf.Paper.QcqsCompactSupportRealization

/-! # Whole-system compact-support and Frobenius normalization

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
`prop-trf-rational-frobenius-integral-model.proof.md`, clauses (2)--(3)
(blueprint: lem-trf-compact-support-system-realization-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived
  WeilConjectures.SemilinearSections.abelianSheafify
  WeilConjectures.SemilinearSections.locallyBijective
  WeilConjectures.SemilinearSections.sequenceSmall
  WeilConjectures.SemilinearSections.sliceSmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.CompactSupportNormalization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalize restriction/inverse image on the actual tensor-unit generators.
Source: blueprint proof steps 3 and 6
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def RestrictionSpec {W : Scheme.{u}} (g : W ⟶ W) [IsIso g]
    (j : coefficientSequenceRestriction l E W ⋙ integralTowerInverseImage l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E W) :
    Prop :=
  ∀ (M : coefficientSequenceModules l E W) (n : ℕ) (U : W.ProEt)
    (x : M.val.obj (op (n, (proEtaleIsoPostcompose g).obj U))),
    (((j.hom.app M).app (op n)).val.app (op U))
        (integralComparisonRestrictedSection l E W M n
          (op ((proEtaleIsoPostcompose g).obj U)) x) =
      integralComparisonRestrictedSection l E W
        ((integralComparisonSequencePullback l E g).obj M) n (op U)
        (((integralComparisonSequencePullback l E g).obj M).val.map
          (CategoryTheory.Prod.mkHom (𝟙 n) (proEtaleIsoCommaArrow g U)).op
          (integralComparisonSequenceGenerator l E g M n
            ((proEtaleIsoPostcompose g).obj U) x))

/-- Localize the tensor-unit comparison as an isomorphism of entire strict towers.
Source: blueprint proof step 6
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def derivedRestrictionComparison {W : Scheme.{u}} (g : W ⟶ W) [IsIso g]
    (j : coefficientSequenceRestriction l E W ⋙ integralTowerInverseImage l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E W) :
    coefficientSequenceDerivedRestriction l E W ⋙ integralDerivedTowerInverseImage l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙
        coefficientSequenceDerivedRestriction l E W :=
  letI := integralComparisonSequencePullbackAdditive l E g
  letI := integralTowerInverseImageLimits l E g
  letI := integralTowerInverseImageColimits l E g
  letI := coefficientSequenceRestriction_additive l E W
  letI := coefficientSequenceRestriction_limits l E W
  letI := coefficientSequenceRestriction_colimits l E W
  letI := integralComparisonSequencePullbackLimits l E g
  letI := integralComparisonSequencePullbackColimits l E g
  (Functor.mapDerivedCategoryCompIso (coefficientSequenceRestriction l E W)
    (integralTowerInverseImage l E g)).symm ≪≫
    Functor.mapDerivedCategoryNatIso j ≪≫
    Functor.mapDerivedCategoryCompIso (integralComparisonSequencePullback l E g)
      (coefficientSequenceRestriction l E W)

/-- The full cone condition fixes omega by adjunction, including its shifted coordinate.
Source: blueprint proof step 6
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def ConeSpec {W : Scheme.{u}} (g : W ⟶ W) [IsIso g]
    (j : coefficientSequenceRestriction l E W ⋙ integralTowerInverseImage l E g ≅
      integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E W)
    (ω : coefficientSequenceLimit l E W ⋙ inverseImageIntegralDerived.{u, u} l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E W) :
    Prop :=
  ∀ C : coefficientSequenceDerived l E W,
    (integralComparisonConstantTower l E W).map (ω.hom.app C) ≫
        (integralComparisonTowerCounit l E W).app
          ((coefficientSequenceDerivedRestriction l E W).obj
            ((integralComparisonDerivedSequencePullback l E g).obj C)) =
      (integralTowerInverseImageDiagonal l E g).hom.app ((coefficientSequenceLimit l E W).obj C) ≫
        (integralDerivedTowerInverseImage l E g).map ((integralComparisonTowerCounit l E W).app
          ((coefficientSequenceDerivedRestriction l E W).obj C)) ≫
        (derivedRestrictionComparison l E g j).hom.app C

/-- The system tensor comparison is the adjoint transpose of inverse image of the
completion unit followed by the entire-cone comparison. This fixes a system map,
without choosing maps from their evaluations. Source: blueprint proof steps 3 and 7(ii)
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def sigma {W : Scheme.{u}} (g : W ⟶ W) [IsIso g]
    (ω : coefficientSequenceLimit l E W ⋙ inverseImageIntegralDerived.{u, u} l E g ≅
      integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E W)
    (N : DerivedCategory (scalarReductionSource l E W)) :
    (FrobeniusExchange.reduction l E W).obj ((inverseImageIntegralDerived.{u, u} l E g).obj N) ⟶
      (integralComparisonDerivedSequencePullback l E g).obj
        ((FrobeniusExchange.reduction l E W).obj N) :=
  (((FrobeniusExchange.models l E).system W).adjunction.homEquiv _ _).symm
    ((inverseImageIntegralDerived.{u, u} l E g).map
      (((FrobeniusExchange.models l E).system W).adjunction.unit.app N) ≫
        ω.hom.app ((FrobeniusExchange.reduction l E W).obj N))



/-- The specified compact-support system operation. Source: blueprint clause (3)
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
abbrev operation {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  FrobeniusExchange.systemDerivedOpen l E c.i ⋙ FrobeniusExchange.systemDirect l E c.g

/-- The named lift is simultaneous reduction, exact open extension, total derived
system direct image, then exact coefficient restriction. Source: blueprint proof step 1
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def compactSupportSystemTower {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  FrobeniusExchange.reduction l E X ⋙ operation l E c ⋙
    coefficientSequenceDerivedRestriction l E Y

/-- The canonical finite comparison first commutes restriction with evaluation,
then applies the specified compact-support evaluation and restricts scalars.
Source: blueprint clause (3), proof step 1
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def canonicalEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    compactSupportSystemTower l E c ⋙
        pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n :=
  Functor.isoWhiskerLeft (FrobeniusExchange.reduction l E X ⋙ operation l E c)
      (coefficientRestrictedEvaluationIso l E Y n) ≪≫
    Functor.isoWhiskerRight (FrobeniusExchange.compactFiniteEvaluation l E c n)
      (scalarReductionDerivedRestriction l E Y n)

/-- The named simultaneous compact-support tower, including its quotient arrows.
Source: blueprint proof step 1
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
abbrev tower {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  compactSupportSystemTower l E c

/-- Delta is the identity of the specified common composite, before any evaluation.
Source: blueprint proof step 1
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def delta {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    FrobeniusExchange.reduction l E X ⋙ operation l E c ⋙
        coefficientSequenceDerivedRestriction l E Y ≅ tower l E c := Iso.refl _

/-- The canonical b is the specified pullback/reduction counit isomorphism.
Source: blueprint proof steps 3--5
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
abbrev b {W : Scheme.{u}} [∀ x : W, Invertible (l : W.residueField x)]
    (g : W ⟶ W) (N : sfIntegralConstructibleCategory l E W) :=
  (FrobeniusExchange.reductionPullbackIso l E g).app N

/-- The specified integral comparison, with no change of representative normalization.
Source: blueprint proof step 3, part (b)
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
abbrev kappa {W : Scheme.{u}} [∀ x : W, Invertible (l : W.residueField x)]
    (g : W ⟶ W) [IsIso g] (N : DerivedCategory (scalarReductionSource l E W)) :=
  inverseImagePullbackComparisonDerived l E g
    (fun x ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk x)) _
      ((map_natCast (IsLocalRing.residue (W.presheaf.stalk x)) l).symm ▸
        isUnit_of_invertible (l : W.residueField x)))
    (fun x ↦ isUnit_of_map_unit (IsLocalRing.residue (W.presheaf.stalk x)) _
      ((map_natCast (IsLocalRing.residue (W.presheaf.stalk x)) l).symm ▸
        isUnit_of_invertible (l : W.residueField x))) N

/-- Alpha is the actual unit--tensor--counit word on the entire system.
Source: blueprint displayed alpha-can and proof step 7
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def alphaCan {W : Scheme.{u}} [∀ x : W, Invertible (l : W.residueField x)]
    (g : W ⟶ W) (C : coefficientSequenceDerived l E W)
    (hC : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C)) :=
  (((FrobeniusExchange.models l E).system W).adjunction.unit.app
      ((integralDerivedPullback l E g).obj ((coefficientSequenceLimit l E W).obj C))) ≫
    (coefficientSequenceLimit l E W).map
      ((b l E g ⟨(coefficientSequenceLimit l E W).obj C, hC⟩).hom) ≫
    (coefficientSequenceLimit l E W).map
      ((integralComparisonDerivedSequencePullback l E g).map
        (((FrobeniusExchange.models l E).system W).adjunction.counit.app C))

/-- Beta is total limit of the actual inverse tensor comparison, after proper/open F.
Source: blueprint displayed beta-can and proof step 8
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def betaCan {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [∀ x : X, Invertible (l : X.residueField x)]
    (g : X ⟶ X) (K : sfIntegralConstructibleCategory l E X) :=
  (coefficientSequenceLimit l E Y).map ((operation l E c).map (b l E g K).inv)

/-- The data below are constrained by section generators and the entire counit;
no isomorphism is selected from its finite evaluations. Source: blueprint steps 3, 6--7
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
structure Comparison {W : Scheme.{u}} [∀ x : W, Invertible (l : W.residueField x)]
    (g : W ⟶ W) [IsIso g] where
  /-- The tensor-unit comparison before deriving or taking a limit. -/
  restriction : coefficientSequenceRestriction l E W ⋙ integralTowerInverseImage l E g ≅
    integralComparisonSequencePullback l E g ⋙ coefficientSequenceRestriction l E W
  /-- Its value on every section is the canonical tensor-unit insertion. -/
  restriction_spec : RestrictionSpec l E g restriction
  /-- Exact inverse image commutes with the entire total limit cone. -/
  cone : coefficientSequenceLimit l E W ⋙ inverseImageIntegralDerived.{u, u} l E g ≅
    integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E W
  /-- The adjoint-transpose equation fixes both cone coordinates. -/
  cone_spec : ConeSpec l E g restriction cone
  /-- The specified kappa is invertible on the full domain, with no Tor condition. -/
  kappa_iso : ∀ N : sfIntegralConstructibleCategory l E W, IsIso (kappa l E g N.obj)
  /-- b = sigma R(kappa inverse), as an equality of whole system maps. -/
  reduction_normalization : ∀ N : sfIntegralConstructibleCategory l E W,
    (FrobeniusExchange.reduction l E W).map (kappa l E g N.obj) ≫ (b l E g N).hom =
      sigma l E g cone N.obj
  /-- The named realization is the unit followed by the specified tensor map. -/
  realization_normalization : ∀ N : sfIntegralConstructibleCategory l E W,
    ((FrobeniusExchange.models l E).pullback g).realization.hom.app N.obj =
      ((FrobeniusExchange.models l E).system W).adjunction.unit.app
          ((integralDerivedPullback l E g).obj N.obj) ≫
        (coefficientSequenceLimit l E W).map (b l E g N).hom

/-- Nu is the inverse of the specified kappa followed by the entire-cone comparison.
Source: blueprint displayed nu, proof step 6
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def nu {W : Scheme.{u}} [∀ x : W, Invertible (l : W.residueField x)]
    {g : W ⟶ W} [IsIso g] (A : Comparison l E g)
    (C : coefficientSequenceDerived l E W)
    (hC : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C)) :=
  letI := A.kappa_iso ⟨(coefficientSequenceLimit l E W).obj C, hC⟩
  (asIso (kappa l E g ((coefficientSequenceLimit l E W).obj C))).symm ≪≫ A.cone.app C

/-- The normalized global realization system used by the already named operation maps.
Source: blueprint composition normalization, proof step 5
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
abbrev models :=
  (integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose

/-- The inverse-direction system compositor, with the actual equality of power maps.
Source: blueprint system identity, proof steps 4--5
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def systemCompositor {W : Scheme.{u}} (a : Aut W) (m : ℕ) :
    integralComparisonDerivedSequencePullback l E (a ^ m).hom ⋙
        integralComparisonDerivedSequencePullback l E a.hom ≅
      integralComparisonDerivedSequencePullback l E (a ^ (m + 1)).hom :=
  (integralComparisonSystemComposition l E a.hom (a ^ m).hom).symm ≪≫
    eqToIso (congrArg (integralComparisonDerivedSequencePullback l E)
      (congrArg Iso.hom (pow_succ a m)).symm)

/-- The inverse-direction integral compositor, in the published realization coordinates.
Source: blueprint system identity, proof step 5
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def integralCompositor {W : Scheme.{u}}
    [∀ x : W, Invertible (l : W.residueField x)] (a : Aut W) (m : ℕ)
    (N : sfIntegralConstructibleCategory l E W) :
    (integralDerivedPullback l E a.hom).obj
        ((integralDerivedPullback l E (a ^ m).hom).obj N.obj) ≅
      (integralDerivedPullback l E (a ^ (m + 1)).hom).obj N.obj :=
  (integralComparisonComposition l E (models.{u} l) a.hom (a ^ m).hom N).symm ≪≫
    eqToIso (congrArg (fun g ↦ (integralDerivedPullback l E g).obj N.obj)
      (congrArg Iso.hom (pow_succ a m)).symm)

/-- All normalizations and power laws on one of the three schemes in the square.
Source: blueprint proof steps 3--7, including naturality and compositor compatibility
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
structure PowerNormalization {W : Scheme.{u}}
    [∀ x : W, Invertible (l : W.residueField x)] (a : Aut W) where
  /-- All powers use the specified comparisons, including the identity power. -/
  comparison : ∀ r : ℕ, Comparison l E (a ^ r).hom
  /-- The bounded derived-complete constructible domain is preserved. -/
  pullback_closed : ∀ (r : ℕ) (N : sfIntegralConstructibleCategory l E W),
    sfIntegralConstructible l E W ((integralDerivedPullback l E (a ^ r).hom).obj N.obj)
  /-- The system compositor identity, before any total limit or evaluation. -/
  reduction_composition : ∀ (m : ℕ) (N : sfIntegralConstructibleCategory l E W),
    (integralComparisonDerivedSequencePullback l E a.hom).map (b l E (a ^ m).hom N).inv ≫
        (b l E a.hom ⟨(integralDerivedPullback l E (a ^ m).hom).obj N.obj,
          pullback_closed m N⟩).inv ≫
        (FrobeniusExchange.reduction l E W).map (integralCompositor l E a m N).hom =
      (systemCompositor l E a m).hom.app ((FrobeniusExchange.reduction l E W).obj N.obj) ≫
        (b l E (a ^ (m + 1)).hom N).inv
  /-- The complete realization domain is preserved by system pullback. -/
  limit_closed : ∀ (r : ℕ) (C : coefficientSequenceDerived l E W),
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C) →
      sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
        ((integralComparisonDerivedSequencePullback l E (a ^ r).hom).obj C))
  /-- Alpha-can equals nu as a whole-cone map. -/
  alpha_normalization : ∀ (r : ℕ) (C : coefficientSequenceDerived l E W)
    (hC : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C)),
    alphaCan l E (a ^ r).hom C hC = (nu l E (comparison r) C hC).hom
  /-- Nu is natural in every derived system morphism on its stated domain. -/
  nu_naturality : ∀ (r : ℕ) (C C' : coefficientSequenceDerived l E W) (v : C ⟶ C')
    (hC : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C))
    (hC' : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C')),
    (integralDerivedPullback l E (a ^ r).hom).map ((coefficientSequenceLimit l E W).map v) ≫
        (nu l E (comparison r) C' hC').hom =
      (nu l E (comparison r) C hC).hom ≫
        (coefficientSequenceLimit l E W).map
          ((integralComparisonDerivedSequencePullback l E (a ^ r).hom).map v)
  /-- The inverse-direction integral compositor agrees with the system compositor. -/
  nu_composition : ∀ (m : ℕ) (C : coefficientSequenceDerived l E W)
    (hC : sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj C)),
    (integralCompositor l E a m ⟨(coefficientSequenceLimit l E W).obj C, hC⟩).hom ≫
        (nu l E (comparison (m + 1)) C hC).hom =
      (integralDerivedPullback l E a.hom).map (nu l E (comparison m) C hC).hom ≫
        (nu l E (comparison 1)
          ((integralComparisonDerivedSequencePullback l E (a ^ m).hom).obj C)
          (limit_closed m C hC)).hom ≫
        (coefficientSequenceLimit l E W).map ((systemCompositor l E a m).hom.app C)



/-- The entire assertion for one compactification and its three Frobenius automorphisms.
Source: blueprint clauses (2)--(3), all displayed identifications
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
structure Normalization (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
    {X Y : Scheme.{u}} [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
    [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))]
    [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
    [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))]
    [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ z : c.Z, Invertible (l : c.Z.residueField z)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (aX : Aut X) (aZ : Aut c.Z) (aY : Aut Y) where
  /-- Pullback/reduction, limit and compositor normalization on X. -/
  source : PowerNormalization l E aX
  /-- The same normalization on the retained middle scheme. -/
  middle : PowerNormalization l E aZ
  /-- The same normalization on Y, including arbitrary output systems. -/
  target : PowerNormalization l E aY
  /-- Natural evaluation of the specified common tower. -/
  evaluation : ∀ n : ℕ,
    tower l E c ⋙ pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
      compactSupportRestrictedLevel l E c n
  /-- Evaluation is the specified restriction/evaluation and compact-support composite. -/
  evaluation_normalization : ∀ n : ℕ, evaluation n = canonicalEvaluation l E c n
  /-- Every comparable-pair transition is the actual quotient/scalar comparison. -/
  transition : ∀ (m n : ℕ) (h : n ≤ m)
    (K : DerivedCategory (scalarReductionSource l E X)),
    (pbcTowerTransition Y (completedIntegralCommRingSheafUnrestricted l E Y) m n h).app
        ((tower l E c).obj K) ≫ (evaluation n).hom.app K =
      (evaluation m).hom.app K ≫ compactSupportRestrictedTransition l E c m n h K
  /-- The limit of the finite-output system has the full constructible domain. -/
  output : ∀ K : sfIntegralConstructibleCategory l E X,
    sfIntegralConstructible l E Y ((FrobeniusExchange.compactImage l E f c).obj K.obj)
  /-- The defining identification with Rf_! has its actual finite projections. -/
  realization : FrobeniusExchange.CompactRealizationSpec l E K₀ hl f c
    (FrobeniusExchange.compactRealization l E K₀ hl f c)
  /-- The actual source operation comparison is the unit--tensor--counit word. -/
  alpha_word : ∀ (r : ℕ) (K : sfIntegralConstructibleCategory l E X),
    (integralDerivedPullback l E (aY ^ r).hom).map
        ((FrobeniusExchange.compactRealization l E K₀ hl f c).inv.app K) ≫
      (FrobeniusExchange.compactAlpha l E K₀ hl f c (aY ^ r).hom).app K =
        alphaCan l E (aY ^ r).hom
          ((FrobeniusExchange.reduction l E X ⋙ operation l E c).obj K.obj) (output K)
  /-- Alpha equals nu as an actual entire-cone map in realization coordinates. -/
  alpha_nu : ∀ (r : ℕ) (K : sfIntegralConstructibleCategory l E X),
    (integralDerivedPullback l E (aY ^ r).hom).map
        ((FrobeniusExchange.compactRealization l E K₀ hl f c).inv.app K) ≫
      (FrobeniusExchange.compactAlpha l E K₀ hl f c (aY ^ r).hom).app K =
        (nu l E (target.comparison r)
          ((FrobeniusExchange.reduction l E X ⋙ operation l E c).obj K.obj) (output K)).hom
  /-- Beta is total limit of F applied to b inverse, with the same defining identification. -/
  beta_word : ∀ (r : ℕ) (K : sfIntegralConstructibleCategory l E X),
    (FrobeniusExchange.compactBeta l E K₀ hl f c (aX ^ r).hom).app K ≫
      (FrobeniusExchange.compactRealization l E K₀ hl f c).hom.app
        ((constructibleIntegralPullback l E (aX ^ r).hom).obj K) =
      betaCan l E c (aX ^ r).hom K

/-- At the geometric point the full-cone normalization is the already specified nu.
Source: blueprint point specialization, following proof step 6
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def PointSpec (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) : Prop :=
  letI := fun x ↦ frobeniusPointPrimeInvertible D l hl x
  ∀ (r : ℕ) (A : Comparison l E ((pointFrobeniusAut D) ^ r).hom)
    (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
    nu l E A C hC = IntegralPointTransportTower.nu D l E hl r C hC

/-- The stated finite-field setting, with the compactification base changed once.
Only inherited proof instances are installed. Source: blueprint hypotheses and (3)
(blueprint: lem-trf-compact-support-system-realization-normalization). -/
def Laws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) : Prop :=
  letI : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).1
  letI : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D X₀).2
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (FrobeniusExchange.fiber_finiteType D Y₀).2
  letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  letI := fun z ↦ sfWeilPrimeInvertible D l hl (zlCompactificationMiddle D f₀ c₀) z
  letI := (FrobeniusExchange.fiberMap_properties D f₀).1
  letI := (FrobeniusExchange.fiberMap_properties D f₀).2.1
  letI := (FrobeniusExchange.fiberMap_properties D f₀).2.2
  Nonempty (Normalization l E D.k (zlClosurePrimeUnit D l hl)
    (xft := (FrobeniusExchange.fiber_finiteType D X₀).1)
    (xqc := (FrobeniusExchange.fiber_finiteType D X₀).2)
    (yft := (FrobeniusExchange.fiber_finiteType D Y₀).1)
    (yqc := (FrobeniusExchange.fiber_finiteType D Y₀).2)
    (FrobeniusExchange.fiberMap D f₀) (FrobeniusExchange.geometricCompactification D f₀ c₀)
    (D.geometricFrobenius X₀) (D.geometricFrobenius (zlCompactificationMiddle D f₀ c₀))
    (D.geometricFrobenius Y₀)) ∧ PointSpec l E D hl

/-- The finite-output system, its entire-limit realization and the specified Frobenius
operation comparisons have the simultaneous normalization in the node.
Source: blueprint main-20261015, sec-trace-formula/sk-d-weil,
prop-trf-rational-frobenius-integral-model.proof.md, (2)--(3)
(blueprint: lem-trf-compact-support-system-realization-normalization).

Proof:
1. Use the same reduction, exact open extension, entire-system derived proper image
and coefficient restriction as lem-weil-compact-support-reduction-tower-functor.
Their common composite gives delta before evaluation. The section-model comparison
lem-trf-compact-support-system-evaluation-coherence supplies evaluation and transitions.
2. Apply total derived limit; the normalized Roos projections identify the result
with def-weil-integral-rational-qbar-compact-support, on objects and morphisms.
Use lem-sf-integral-compact-support-constructible for its output domain.
3. The completion-unit identity of
lem-weil-isomorphism-derived-pullback-comparison-normalization makes the specified
kappa invertible on every derived-complete constructible input. The normalized tensor
map of lem-weil-isomorphism-derived-pullback-reduction-tower gives sigma on one flat
K-flat representative and its strict quotient diagram; descent gives every derived map.
4. Tensor generators and the coefficient projection square give the sigma compositor
identity before localization. Combine it with the actual kappa composition equation
of lem-trf-integral-inverse-image-comparison-composition to obtain the b identity.
5. Resolve an arbitrary output system in the entire tower category. Exact inverse
image preserves the resolution and its limit cone. Transposing the entire counit,
with the tensor-unit restriction comparison, gives the unique cone isomorphism omega.
Compose omega with kappa inverse to get nu, also at the point. No output reconstruction
or finite-Tor hypothesis enters.
6. In the source word substitute b = sigma R(kappa inverse). Naturality of the unit
moves kappa inverse outside. The mate identity for sigma and omega, naturality of
omega at the counit, and the triangle identity cancel the reduction/limit pair.
The resulting map is nu. The target word is literally total limit of F(b inverse).
7. The same constructions are natural on derived morphisms. Their compositor identities
on strict tensor generators descend unchanged, yielding all power and naturality laws.
- third-party finite evaluations are never used to detect equality of system maps. -/
theorem compactSupportSystemRealizationNormalization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left]
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
    (c₀ : Compactification f₀.left) : Laws l E D hl f₀ c₀ := by
  sorry

end WeilConjectures.CompactSupportNormalization
