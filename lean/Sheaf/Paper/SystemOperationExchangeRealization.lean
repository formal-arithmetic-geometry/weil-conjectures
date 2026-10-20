/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.Algebra.Field.ULift
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Sheaf.Paper.SfIntegralReductionTower
public import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.SfIntegralDirectImageConstructible
public import Sheaf.Paper.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.SixFunctors.OpenTensorNormalization

/-! # Simultaneous-system realization of operation exchanges

Source: slopmaster2 blueprint, `def:weil-direct-image-object` and
`def:weil-compact-support-object`; Deligne, Weil II, (1.1.10)--(1.1.14)
(blueprint: def-weil-system-operation-exchange-realization).

## Main definitions and statements

- `finiteExchange`, `finiteTensorExchange`: finite mates for a general commuting square.
- `systemExchange`, `systemCompactExchange`: actual mates before evaluation.
- `realize`, `integralExchange`, `coefficientExchange`: normalized whole-system realization.
- `directIntegral`, `compactIntegral`: natural transformations on constructible domains.
- `directIntegral_reduction`, `compactIntegral_reduction`: the specified counit equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Functor

namespace WeilConjectures.FrobeniusExchange
variable (A : Type u) [CommRing A] [Finite A]

/-- The finite exchange for any commuting square is the specified adjunction mate.
The four corners and both vertical arrows may differ; only commutativity is used.
Source: blueprint `def:direct-image-exchange` and `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteExchange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (w : gX ≫ f = f' ≫ gY) :
    proEtaleConstantDerivedDirectImage f A ⋙ sfIntrinsicDerivedPullback A gY ⟶
      sfIntrinsicDerivedPullback A gX ⋙ proEtaleConstantDerivedDirectImage f' A :=
  (mateEquiv
    (sfIntrinsicConstantModuleAdjunction f A).mapDerivedCategoryRightDerivedAdjunction
    (sfIntrinsicConstantModuleAdjunction f' A).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _
      ((sfIntrinsicDerivedPullbackComp A f' gY).symm ≪≫
        eqToIso (congrArg (fun h ↦ sfIntrinsicDerivedPullback A h) w.symm) ≪≫
        sfIntrinsicDerivedPullbackComp A gX f).hom)).natTrans

/-- The ambient mate in the recorded tensor-pullback coordinates. Both coordinate
changes are uniquely fixed by the ordinary units, so this is the ambient ringed mate.
Source: blueprint `def:direct-image-exchange`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteTensorExchange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (gX : X' ⟶ X) (gY : Y' ⟶ Y) (w : gX ≫ f = f' ≫ gY) :
    proEtaleConstantDerivedDirectImage f A ⋙ proEtaleConstantRingDerivedPullback A gY ⟶
      proEtaleConstantRingDerivedPullback A gX ⋙ proEtaleConstantDerivedDirectImage f' A :=
  whiskerLeft (proEtaleConstantDerivedDirectImage f A)
      (openSquareDerivedPullbackModel A gY).hom ≫
    finiteExchange A f f' gX gY w ≫
    whiskerRight (openSquareDerivedPullbackModel A gX).inv
      (proEtaleConstantDerivedDirectImage f' A)


variable (A : Type u) [CommRing A] [Finite A]




section Systems
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite chosen-compactification exchange, literally the proper mate followed
by proper image of the canonical open-adjunction exchange.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def finiteCompact (n : ℕ) (hn : 1 ≤ n) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    letI := Padic.finite_coefficientExtensionRing l E n hn
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ⋙
        proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gY ⟶
      proEtaleConstantRingDerivedPullback (Padic.coefficientExtensionRing l E n) gX ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) := by
  letI := Padic.finite_coefficientExtensionRing l E n hn
  exact whiskerLeft (sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) c.i)
      (finiteTensorExchange (Padic.coefficientExtensionRing l E n) c.g c.g gB gY wp) ≫
    whiskerRight (constantOpenSquareExchange l E n hn gX c.i c.i gB sj).hom
      (proEtaleConstantDerivedDirectImage c.g (Padic.coefficientExtensionRing l E n))

/-- Additivity of the sectionwise direct image on the strict varying-ring diagram.
Source: Zheng 4.1 and 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization).
Proof: addition is sectionwise, and precomposition and scalar restriction leave
addition unchanged, at every index and every vertical object. -/
theorem systemDirect_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (integralComparisonSequenceDirectImage l E f).Additive := by
  sorry

attribute [instance] systemDirect_additive

/-- Strict coefficient systems admit simultaneous K-injective resolutions.
Source: Zheng 4.10; Stacks 079P, 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: these systems are module sheaves on the small vertical sequence site.
The Grothendieck module-sheaf theorem gives functorial K-injective resolutions
in its ordinary unbounded derived category. -/
theorem system_hasKInjectives (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (coefficientSequenceModules l E X) := by
  sorry

attribute [instance] system_hasKInjectives

/-- Total right-derived direct image of entire strict semilinear coefficient systems.
Source: Zheng 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
abbrev systemDirect {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  (integralComparisonSequenceDirectImage l E f).rightDerivedFunctor

/-- The derived adjunction is derived from the actual ordinary system adjunction.
Source: Zheng 4.10; Stacks 07A4
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integralComparisonDerivedSequencePullback l E f ⊣ systemDirect l E f :=
  letI : (integralComparisonSequenceDirectImage l E f).leftAdjoint.Additive :=
    inferInstanceAs (integralComparisonSequencePullback l E f).Additive
  letI : PreservesFiniteLimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
    inferInstanceAs (PreservesFiniteLimits (integralComparisonSequencePullback l E f))
  letI : PreservesFiniteColimits (integralComparisonSequenceDirectImage l E f).leftAdjoint :=
    inferInstanceAs (PreservesFiniteColimits (integralComparisonSequencePullback l E f))
  (Adjunction.ofIsRightAdjoint
    (integralComparisonSequenceDirectImage l E f)).mapDerivedCategoryRightDerivedAdjunction

/-- The square comparison on the derived category of whole strict systems.
It is obtained before evaluation, from the section-normalized ordinary compositor.
Source: Zheng 4.10; blueprint `def:direct-image-exchange`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) :
    integralComparisonDerivedSequencePullback l E gY ⋙
        integralComparisonDerivedSequencePullback l E f ≅
      integralComparisonDerivedSequencePullback l E f ⋙
        integralComparisonDerivedSequencePullback l E gX :=
  (integralComparisonSystemComposition l E f gY).symm ≪≫
    eqToIso (congrArg (fun h ↦ integralComparisonDerivedSequencePullback l E h) w.symm) ≪≫
    integralComparisonSystemComposition l E gX f

/-- The specified system mate, formed before finite evaluation or derived inverse limit.
Source: Zheng 4.10; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemExchange {X Y : Scheme.{u}} (f : X ⟶ Y) (gX : X ⟶ X) (gY : Y ⟶ Y)
    (w : gX ≫ f = f ≫ gY) :
    systemDirect l E f ⋙ integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙ systemDirect l E f :=
  (mateEquiv (systemAdjunction l E f) (systemAdjunction l E f)
    (TwoSquare.mk _ _ _ _ (systemSquare l E f gX gY w).hom)).natTrans

/-- A simultaneous quotient-complex presentation of the published integral operations.
Its reduction, total limit and pullback realizations carry the dependency's full
K-flat quotient-generator and K-injective Roos normalizations.
Source: Stacks 099N(5), 0941; blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def models : IntegralComparisonCoefficientData l E :=
  ((integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose).coefficient E

/-- The coherent reduction system of one integral object, including all quotient maps.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
abbrev reduction (X : Scheme.{u}) := (models l E).system X |>.reduction

/-- Realize an actual system operation by reduction, that operation, exact scalar
restriction, and total right-derived inverse limit, in that order.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def realize {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (scalarReductionSource l E Y) :=
  reduction l E X ⋙ H ⋙ coefficientSequenceLimit l E Y

/-- The canonical operation-reduction map is the whole-system adjunction counit.
Source: blueprint integral operation comparisons
(blueprint: def-weil-system-operation-exchange-realization). -/
def operationReduction {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    realize l E H ⋙ reduction l E Y ⟶ reduction l E X ⋙ H :=
  whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit

/-- Integral direct image in the simultaneous-system presentation.
Source: blueprint `def:weil-direct-image-object`, integral paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def integralDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  realize l E (systemDirect l E f)

/-- The operation comparison on the source is the pullback realization followed
by pullback of the entire-system counit. It is constructed before evaluation.
Source: blueprint `def:weil-direct-image-object`, alpha-star
(blueprint: def-weil-system-operation-exchange-realization). -/
def sourceComparison {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (gY : Y ⟶ Y) :
    realize l E H ⋙ integralDerivedPullback l E gY ⟶
      reduction l E X ⋙ H ⋙ integralComparisonDerivedSequencePullback l E gY ⋙
        coefficientSequenceLimit l E Y :=
  whiskerLeft (realize l E H) ((models l E).pullback gY).realization.hom ≫
    whiskerRight
      (whiskerRight
        (whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit)
        (integralComparisonDerivedSequencePullback l E gY))
      (coefficientSequenceLimit l E Y)

/-- The canonical reduction comparison for pullback is inverted on the integral
constructible domain, using the dependency's whole-system effectivity assertion.
Source: blueprint `def:weil-direct-image-object`, beta-star
(blueprint: def-weil-system-operation-exchange-realization). -/
def reductionPullbackIso {X : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)] (gX : X ⟶ X) :
    (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E gX ⋙
        reduction l E X ≅
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequencePullback l E gX := by
  let t := whiskerLeft (sfIntegralConstructible l E X).ι
    (integralComparisonPullbackCounit l E gX ((models l E).system X)
      ((models l E).system X) ((models l E).roos X) ((models l E).pullback gX))
  letI : ∀ K : sfIntegralConstructibleCategory l E X, IsIso (t.app K) :=
    fun K ↦ (models l E).effective gX K
  letI := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The integral exchange is beta after L of the specified system map after alpha.
No morphism is chosen from its finite evaluations.
Source: blueprint `def:weil-direct-image-object`, integral exchange formula
(blueprint: def-weil-system-operation-exchange-realization). -/
def integralExchange {X Y : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y)
    (e : H ⋙ integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙ H) :
    (sfIntegralConstructible l E X).ι ⋙ realize l E H ⋙ integralDerivedPullback l E gY ⟶
      (sfIntegralConstructible l E X).ι ⋙ integralDerivedPullback l E gX ⋙ realize l E H :=
  whiskerLeft (sfIntegralConstructible l E X).ι (sourceComparison l E H gY) ≫
    whiskerRight (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X) e)
      (coefficientSequenceLimit l E Y) ≫
    whiskerRight (reductionPullbackIso l E gX).inv (H ⋙ coefficientSequenceLimit l E Y)

/-- Exact open extension exists on whole strict coefficient systems.
Source: Zheng 4.1, 4.10; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization).
Proof: localize the vertical sequence site at the open. The direct-sum extension
presheaf and sheafification give the left adjoint to restriction, independently
at every quotient index. Its sectionwise units are the actual open units.
Both kernels and cokernels are computed componentwise, so extension is exact. -/
theorem systemPullback_isRightAdjoint {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (integralComparisonSequencePullback l E j).IsRightAdjoint := by
  sorry

/-- The universal ordinary open extension, determined up to its adjunction comparison.
Source: Zheng 4.1; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  letI := systemPullback_isRightAdjoint l E j
  (integralComparisonSequencePullback l E j).leftAdjoint

/-- The actual system open adjunction, with its canonical unit and counit.
Source: Zheng 4.1; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    systemOpen l E j ⊣ integralComparisonSequencePullback l E j :=
  letI := systemPullback_isRightAdjoint l E j
  Adjunction.ofIsRightAdjoint (integralComparisonSequencePullback l E j)

/-- Exactness of the specified open extension on strict coefficient systems.
Source: Zheng 4.1, 4.10; Stacks 03DI, 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: identify this left adjoint with the localized extension presheaf followed
by sheafification via the unique adjunction-compatible comparison. The open
extension is exact at every level, hence exact on the abelian system category. -/
theorem systemOpen_exact {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (systemOpen l E j).Additive ∧ PreservesFiniteLimits (systemOpen l E j) ∧
      PreservesFiniteColimits (systemOpen l E j) := by
  sorry

/-- The additive structure from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenAdditive {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (systemOpen l E j).Additive := (systemOpen_exact l E j).1

/-- Finite-limit preservation from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteLimits (systemOpen l E j) := (systemOpen_exact l E j).2.1

/-- Finite-colimit preservation from exact system open extension.
Source: Zheng 4.1 (blueprint: def-weil-system-operation-exchange-realization). -/
instance systemOpenColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PreservesFiniteColimits (systemOpen l E j) := (systemOpen_exact l E j).2.2

/-- Termwise open extension descends exactly to the ordinary derived system category.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
abbrev systemDerivedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (systemOpen l E j).mapDerivedCategory

/-- The derived open adjunction is the exact descent of the ordinary one.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemDerivedOpenAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    systemDerivedOpen l E j ⊣ integralComparisonDerivedSequencePullback l E j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (systemOpenAdjunction l E j)

/-- Ordinary direct image commutes strictly with vertical evaluation. The coefficient
maps are the same constant sections; both functors evaluate M at (n, X ×_Y U).
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: unfold the two sectionwise pushforwards and vertical evaluation. Their
base-change functors agree on objects and maps. Their ring maps send each constant
section to the same section. Module and functor extensionality, followed by proof
irrelevance for sheaf conditions and ring-map compatibility, gives equality. -/
theorem systemDirectEvaluationOrdinary_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonSequenceDirectImage l E f ⋙ coefficientSequenceEvaluation l E Y n =
      coefficientSequenceEvaluation l E X n ⋙
        proEtaleConstantModuleDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) := by
  sorry

/-- Inverse-image evaluation is the conjugate of the actual sectionwise equality.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemPullEvaluationOrdinaryInv {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficientSequenceEvaluation l E Y n ⋙
        sfIntrinsicPullback (Padic.coefficientExtensionRing l E (n + 1)) f ⟶
      integralComparisonSequencePullback l E f ⋙ coefficientSequenceEvaluation l E X n :=
  ((mateEquiv (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (sfIntrinsicConstantModuleAdjunction f (Padic.coefficientExtensionRing l E (n + 1)))).symm
    (TwoSquare.mk _ _ _ _ (eqToIso (systemDirectEvaluationOrdinary_eq l E f n)).hom)).natTrans

/-- The section-normalized inverse-image evaluation mate is invertible.
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: the ordinary inverse image on the sequence site is vertical inverse image
at each level. The displayed mate sends every tensor generator to its identical
inverse-image generator. The generator map and its inverse preserve vertical
restriction and quotient transitions, and hence are mutually inverse sheaf maps. -/
theorem systemPullEvaluationOrdinaryInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (systemPullEvaluationOrdinaryInv l E f n) := by
  sorry

/-- Exact descent of the uniquely unit-normalized inverse-image evaluation mate.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemPullEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    coefficientSequenceDerivedEvaluation l E Y n ⋙
        sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f ≅
      integralComparisonDerivedSequencePullback l E f ⋙
        coefficientSequenceDerivedEvaluation l E X n := by
  letI := systemPullEvaluationOrdinaryInv_isIso l E f n
  letI := coefficientSequenceEvaluation_additiveInstance l E X n
  letI := coefficientSequenceEvaluation_additiveInstance l E Y n
  letI := coefficientSequenceEvaluation_limits l E X n
  letI := coefficientSequenceEvaluation_limits l E Y n
  letI := coefficientSequenceEvaluation_colimits l E X n
  letI := coefficientSequenceEvaluation_colimits l E Y n
  letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  letI := sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing l E (n + 1)) f
  exact (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (systemPullEvaluationOrdinaryInv l E f n)) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- Direct-image evaluation is the derived adjunction mate of that same pullback map.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemDirectEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    systemDirect l E f ⋙ coefficientSequenceDerivedEvaluation l E Y n ⟶
      coefficientSequenceDerivedEvaluation l E X n ⋙
        proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1)) :=
  (mateEquiv (systemAdjunction l E f)
    (sfIntrinsicConstantModuleAdjunction f
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (systemPullEvaluation l E f n).hom)).natTrans

/-- The specified direct-image evaluation mate is invertible.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization).
Proof: use the simultaneous-resolution calculus of Zheng 4.10 for sectionwise
system direct image and its finite evaluations. Resolve the whole system in the
common acyclic class for these section direct images; the same resolution then
computes each finite direct image. The ordinary sectionwise equality identifies
their comparison. The evaluated units identify this comparison with the displayed
mate, proving invertibility. No exactness of finite quotient tensor is required. -/
theorem systemDirectEvaluation_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (systemDirectEvaluation l E f n) := by
  sorry

/-- Evaluation of the actual whole-system exchange is the finite ambient mate,
through the specified evaluation comparisons `systemDirectEvaluation` and
`systemPullEvaluation`. These comparisons are not inputs to the construction of
the system morphism.
Source: Zheng 4.10; blueprint integral direct-image paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: evaluation is exact on the vertical sequence site. Its finite left
extensions show that evaluation of the derived section direct image is the
finite derived section direct image. Evaluate the ordinary section-normalized
pullback adjunction, then descend on simultaneous K-injective resolutions.
The evaluated units and counits are the finite ones, and the evaluated system
compositors are the finite compositors. Expanding mateEquiv and pasting the
mates gives the displayed equality. In particular this uses the constructed
whole-system mate, not detection of equality by evaluation. -/
theorem systemExchange_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y)
    (gX : X ⟶ X) (gY : Y ⟶ Y) (w : gX ≫ f = f ≫ gY) (n : ℕ) :
    let A := Padic.coefficientExtensionRing l E (n + 1)
    letI := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    ∀ K : coefficientSequenceDerived l E X,
      (coefficientSequenceDerivedEvaluation l E Y n).map
          ((systemExchange l E f gX gY w).app K) ≫
        (systemDirectEvaluation l E f n).app
          ((integralComparisonDerivedSequencePullback l E gX).obj K) ≫
        (proEtaleConstantDerivedDirectImage f A).map
          ((systemPullEvaluation l E gX n).inv.app K) =
      (systemPullEvaluation l E gY n).inv.app ((systemDirect l E f).obj K) ≫
        (sfIntrinsicDerivedPullback A gY).map ((systemDirectEvaluation l E f n).app K) ≫
        (finiteExchange A f f gX gY w).app
          ((coefficientSequenceDerivedEvaluation l E X n).obj K) := by
  sorry

/-- Open-extension evaluation is the left mate of normalized pullback evaluation.
Source: Zheng 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenEvaluationInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    coefficientSequenceDerivedEvaluation l E U n ⋙
        sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E (n + 1)) j ⟶
      systemDerivedOpen l E j ⋙ coefficientSequenceDerivedEvaluation l E X n :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j)
    (SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
      (sfIntrinsicOpenAdjunction (Padic.coefficientExtensionRing l E (n + 1)) j))).symm
    (TwoSquare.mk _ _ _ _ (systemPullEvaluation l E j n).inv)).natTrans

/-- The open evaluation mate is invertible with the original open units.
Source: Zheng 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization).
Proof: exact open extension on the vertical sequence site is extension by zero
on every level. Its unit is the identity on the open, and both sides vanish off
that open. These identities identify the specified mate and its inverse before
localization. Exact descent preserves their two inverse equations. -/
theorem systemOpenEvaluationInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) : IsIso (systemOpenEvaluationInv l E j n) := by
  sorry

/-- Finite evaluation of the actual compact system, fixed by both adjunction mates.
Source: Bhatt--Scholze 6.7.6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactFiniteEvaluation {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) :
    reduction l E X ⋙ (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        coefficientSequenceDerivedEvaluation l E Y n ≅
      scalarReductionDerivedExtension l E X n ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) := by
  letI := systemDirectEvaluation_isIso l E c.g n
  letI := systemOpenEvaluationInv_isIso l E c.i n
  exact isoWhiskerLeft (reduction l E X ⋙ systemDerivedOpen l E c.i)
      (asIso (systemDirectEvaluation l E c.g n)) ≪≫
    isoWhiskerRight (isoWhiskerLeft (reduction l E X)
      (asIso (systemOpenEvaluationInv l E c.i n)).symm)
        (proEtaleConstantDerivedDirectImage c.g
          (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    isoWhiskerRight (((models l E).system X).reductionEvaluation n)
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))

/-- The inverse open exchange is the left mate of the inverse pullback square.
Source: Zheng 4.10; blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenExchangeInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (w : gU ≫ j = j ≫ gX) :
    integralComparisonDerivedSequencePullback l E gU ⋙ systemDerivedOpen l E j ⟶
      systemDerivedOpen l E j ⋙ integralComparisonDerivedSequencePullback l E gX :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j) (systemDerivedOpenAdjunction l E j)).symm
    (TwoSquare.mk _ _ _ _ (systemSquare l E j gU gX w).inv)).natTrans

/-- The open mate is invertible for a Cartesian open square.
Source: Stacks 03S6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization).
Proof: on the localized vertical site the open-adjunction mate is the identity
on the pulled-back open and the unique map between zero values off that open.
The Cartesian condition identifies these opens, giving the inverse sectionwise.
This is a map of whole systems, since both maps commute with quotient restrictions.
Exact descent gives an inverse in the ordinary derived category before evaluation. -/
theorem systemOpenExchangeInv_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (gU : U ⟶ U) (gX : X ⟶ X)
    (sq : IsPullback gU j j gX) :
    IsIso (systemOpenExchangeInv l E j gU gX sq.w) := by
  sorry

/-- The canonical open-system exchange, inverse to the specified open-adjunction mate.
Source: Stacks 03S6; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenExchange {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (gU : U ⟶ U) (gX : X ⟶ X) (sq : IsPullback gU j j gX) :
    systemDerivedOpen l E j ⋙ integralComparisonDerivedSequencePullback l E gX ≅
      integralComparisonDerivedSequencePullback l E gU ⋙ systemDerivedOpen l E j :=
  (@asIso _ _ _ _ (systemOpenExchangeInv l E j gU gX sq.w)
    (systemOpenExchangeInv_isIso l E j gU gX sq)).symm

/-- The compactification-relative system composite: proper mate, then proper image
of open exchange, using the same compactification at every quotient level.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemCompactExchange {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y)
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequencePullback l E gY ⟶
      integralComparisonDerivedSequencePullback l E gX ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) :=
  whiskerLeft (systemDerivedOpen l E c.i) (systemExchange l E c.g gB gY wp) ≫
    whiskerRight (systemOpenExchange l E c.i gX gB sj).hom (systemDirect l E c.g)

section ScalarSystems
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- The scalar realization uses the same single global normalized system as models.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarModels : IntegralComparisonScalarData l E L ι (models l E) (models l L) :=
  ((integralPullbackComparisonRealization l (ULift.{u} ℚ_[l]) (ULift.{u} ℚ_[l])
    (AlgHom.id ℚ_[l] (ULift.{u} ℚ_[l]))).choose).scalar E L ι

/-- Coefficient change of direct image is the actual mate of normalized tensor pullback.
It is formed on whole strict systems, before any evaluation or inverse limit.
Source: lem-fix-operation-reduction; Zheng 4.10
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemDirectScalar {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemDirect l E f ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ systemDirect l L f :=
  (mateEquiv (systemAdjunction l E f) (systemAdjunction l L f)
    (TwoSquare.mk _ _ _ _ (integralComparisonSystemScalarPullback l E L ι f).inv)).natTrans

/-- The inverse open coefficient exchange is the actual left-adjunction mate.
Source: Zheng 4.1, 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenScalarInv {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    integralComparisonDerivedSequenceScalar l E L ι X ⋙ systemDerivedOpen l L j ⟶
      systemDerivedOpen l E j ⋙ integralComparisonDerivedSequenceScalar l E L ι B :=
  ((mateEquiv (systemDerivedOpenAdjunction l E j)
    (systemDerivedOpenAdjunction l L j)).symm
    (TwoSquare.mk _ _ _ _ (integralComparisonSystemScalarPullback l E L ι j).hom)).natTrans

/-- Tensor extension commutes with the specified exact open extension.
Source: Zheng 4.1, 4.10; Stacks 03DI
(blueprint: def-weil-system-operation-exchange-realization).
Proof: on the open, the inverse mate is the tensor identity; off the open both
sides are zero. The ordinary balanced tensor maps commute with all quotient
transitions. Localizing their actual inverse chain maps proves the assertion. -/
theorem systemOpenScalarInv_isIso {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :
    IsIso (systemOpenScalarInv l E L ι j) := by
  sorry

/-- The forward open scalar comparison is the inverse of that specified mate.
Source: Zheng 4.10 (blueprint: def-weil-system-operation-exchange-realization). -/
def systemOpenScalar {X B : Scheme.{u}} (j : X ⟶ B) [IsOpenImmersion j] :=
  letI := systemOpenScalarInv_isIso l E L ι j
  (asIso (systemOpenScalarInv l E L ι j)).symm

/-- The proper/open scalar comparison uses the same compactification at every level.
Source: lem-fix-operation-reduction, compact-support paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def systemCompactScalar {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙
        (systemDerivedOpen l L c.i ⋙ systemDirect l L c.g) :=
  whiskerLeft (systemDerivedOpen l E c.i) (systemDirectScalar l E L ι c.g) ≫
    whiskerRight (systemOpenScalar l E L ι c.i).hom (systemDirect l L c.g)

/-- Canonical alpha for coefficient change of an actual system operation.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarSourceComparison {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y) :
    realize l E H ⋙ integralScalarExtensionOfUniverses l E L ι Y ⟶
      reduction l E X ⋙ H ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⋙
        coefficientSequenceLimit l L Y :=
  whiskerLeft (realize l E H) ((scalarModels l E L ι).model Y).realization.hom ≫
    whiskerRight
      (whiskerRight
        (whiskerLeft (reduction l E X ⋙ H) ((models l E).system Y).adjunction.counit)
        (integralComparisonDerivedSequenceScalar l E L ι Y))
      (coefficientSequenceLimit l L Y)

/-- Whole-system effectivity of the specified coefficient-reduction counit.
Source: Stacks 06YY, 0941 (blueprint: def-weil-system-operation-exchange-realization). -/
def scalarReductionIso (X : Scheme.{u}) :
    (sfIntegralConstructible l E X).ι ⋙ integralScalarExtensionOfUniverses l E L ι X ⋙
        reduction l L X ≅
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequenceScalar l E L ι X := by
  let t := whiskerLeft (sfIntegralConstructible l E X).ι
    (integralComparisonScalarCounit l E L ι X ((models l E).system X)
      ((models l L).system X) ((models l L).roos X) ((scalarModels l E L ι).model X))
  letI : ∀ K : sfIntegralConstructibleCategory l E X, IsIso (t.app K) :=
    fun K ↦ (scalarModels l E L ι).effective X K
  letI := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- Realize a specified coefficient-system mate, rather than lift finite evaluations.
Source: lem-fix-operation-reduction; Stacks 06YY, 0941
(blueprint: def-weil-system-operation-exchange-realization). -/
def coefficientExchange {X Y : Scheme.{u}}
    (H : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y)
    (H' : coefficientSequenceDerived l L X ⥤ coefficientSequenceDerived l L Y)
    (e : H ⋙ integralComparisonDerivedSequenceScalar l E L ι Y ⟶
      integralComparisonDerivedSequenceScalar l E L ι X ⋙ H') :
    (sfIntegralConstructible l E X).ι ⋙ realize l E H ⋙
        integralScalarExtensionOfUniverses l E L ι Y ⟶
      (sfIntegralConstructible l E X).ι ⋙ integralScalarExtensionOfUniverses l E L ι X ⋙
        realize l L H' :=
  whiskerLeft (sfIntegralConstructible l E X).ι (scalarSourceComparison l E L ι H) ≫
    whiskerRight (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X) e)
      (coefficientSequenceLimit l L Y) ≫
    whiskerRight (scalarReductionIso l E L ι X).inv (H' ⋙ coefficientSequenceLimit l L Y)

end ScalarSystems

end Systems

section ConstructibleOperations
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [xo : X.Over (Spec (.of K₀))] [yo : Y.Over (Spec (.of K₀))]
  [xft : LocallyOfFiniteType (X ↘ Spec (.of K₀))] [xqc : QuasiCompact (X ↘ Spec (.of K₀))]
  [yft : LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [yqc : QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [fo : f.IsOver (Spec (.of K₀))]

include hl xo yo xft xqc yft yqc fo

/-- The simultaneous direct-image realization is bounded constructible.
Source: blueprint integral direct-image paragraph; Bhatt--Scholze 6.5, 6.7
(blueprint: def-weil-system-operation-exchange-realization).
Proof: derive the actual system direct image on a single system resolution.
Evaluation is its canonical finite direct image, including the scalar-transition
mates, by the finite left adjoints to evaluation. Exact scalar restriction and
the canonical total-limit projections identify the resulting object with the
Roos triangle of SfIntegralDirectImage. Apply
lem-sf-integral-direct-image-constructible, including its empty-scheme case. -/
theorem directImage_constructible (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E Y ((integralDirectImage l E f).obj K.obj) := by
  sorry

/-- The actual direct-image action on the recorded full constructible categories.
Source: blueprint integral direct-image paragraph
(blueprint: def-weil-system-operation-exchange-realization). -/
def directImageFunctor :
    sfIntegralConstructibleCategory l E X ⥤ sfIntegralConstructibleCategory l E Y :=
  (sfIntegralConstructible l E Y).lift
    ((sfIntegralConstructible l E X).ι ⋙ integralDirectImage l E f)
    (directImage_constructible l E K₀ hl f)

/-- The integral direct-image construction is the recorded Roos object, not a
replacement functor inferred from its reductions.
Source: blueprint integral direct-image paragraph; Stacks 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: evaluate the derived system direct image by the normalized sectionwise
adjunction. The quotient maps become exactly sfDirectImageTransition. Restrict
scalars and use the total-limit Roos triangle, with its specified projections.
This gives the displayed SfIntegralDirectImage presentation with the same object.
Countable products exist by the completed-module Grothendieck construction. -/
theorem directImage_roos (K : sfIntegralConstructibleCategory l E X) :
    ∃ hprod : HasProduct (sfDirectImageTerm l E f K.obj),
      ∃ M : @SfIntegralDirectImage l _ E _ _ _ X Y f K.obj hprod,
        M.obj = (integralDirectImage l E f).obj K.obj := by
  sorry

/-- Additivity and constant-coefficient linearity of the actual direct-image action.
Source: blueprint scalar-localization paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: reduction, the sectionwise system direct image and exact scalar restriction
commute with addition and the constant O_E action. Derive these identities and
pass through the total-limit universal map. The full inclusion reflects them. -/
theorem directImage_linear :
    (directImageFunctor l E K₀ hl f).Additive ∧
      (directImageFunctor l E K₀ hl f).Linear (Padic.coefficientExtensionIntegers l E) := by
  sorry


variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

/-- Alpha-star is the canonical operation isomorphism on the stated domain.
This is an assertion about sourceComparison, already constructed on whole systems.
Source: blueprint alpha-star; Zheng 4.10; Stacks 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: the normalized system direct image of a coherent quotient system is the
coherent finite-direct-image system. Finite-type direct-image constructibility
and its finite reduction comparisons make it cartesian. Reconstruction's
whole-system counit is therefore invertible on this system. Pullback by the
scheme isomorphism g preserves the normalized inverse-limit computation.
The composite defining sourceComparison is consequently invertible. -/
theorem directAlpha_isIso (g : Y ⟶ Y) [IsIso g]
    (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((sourceComparison l E (systemDirect l E f) g).app K.obj) := by
  sorry

/-- Integral direct exchange: the constructed whole-system mate, realized by
beta, total derived limit and alpha, on its bounded constructible domain.
The semilinear horizontal arrows have no K₀-linearity assumption.
Source: blueprint `def:weil-direct-image-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def directIntegral (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (w : gX ≫ f = f ≫ gY) :
    directImageFunctor l E K₀ hl f ⋙ constructibleIntegralPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙ directImageFunctor l E K₀ hl f where
  app K := ObjectProperty.homMk
    ((integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)).app K)
  naturality _K _L a := ObjectProperty.hom_ext _
    ((integralExchange l E (systemDirect l E f) gX gY
      (systemExchange l E f gX gY w)).naturality a)

variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The actual integral chosen-compactification operation on simultaneous systems.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactImage (c : Compactification f) :=
  realize l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g)

/-- Whole-system compact support has the bounded integral output of the recorded
compact-support operation.
Source: Bhatt--Scholze 6.7.6--6.7.7; blueprint compact-support paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: the exact system open extension evaluates to the normalized finite j_!.
The derived proper image evaluates to Rp_*, with their quotient transition mates.
Use the same c at every index. The restricted total limit is the compact-support
Roos construction. Apply lem-sf-integral-compact-support-constructible. -/
theorem compactImage_constructible (c : Compactification f)
    (K : sfIntegralConstructibleCategory l E X) :
    sfIntegralConstructible l E Y ((compactImage l E f c).obj K.obj) := by
  sorry

/-- Fix the comparison with the recorded integral Rf_! by its actual Roos projections.
Both sides use this one compactification and the positive exponent n+1.
Source: Bhatt--Scholze 6.7.6; sfQcqsCompactSupportRealization normalization
(blueprint: def-weil-system-operation-exchange-realization). -/
def CompactRealizationSpec (c : Compactification f)
    (τ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ compactImage l E f c) : Prop :=
  ∀ (K : sfIntegralConstructibleCategory l E X) (n : ℕ),
    (scalarReductionDerivedExtension l E Y n).map (τ.hom.app K) ≫
        (((models l E).system Y).reductionEvaluation n).inv.app
          ((compactImage l E f c).obj K.obj) ≫
        (coefficientSequenceDerivedEvaluation l E Y n).map
          ((operationReduction l E (systemDerivedOpen l E c.i ⋙
            systemDirect l E c.g)).app K.obj) ≫
        (compactFiniteEvaluation l E c n).hom.app K.obj =
      (sfCompactSupportFiniteReductionIso l K₀ hl c E K n).hom

/-- There is a unique projection-normalized identification of the recorded Rf_!
with the simultaneous system realization, on the entire constructible category.
Source: Bhatt--Scholze 6.7.6--6.7.7; Stacks 0941
(blueprint: def-weil-system-operation-exchange-realization).
Proof: compare the completed proper/open functor with its single coherent quotient
system. Exact open extension gives the open scalar mate; proper direct image gives
its right-adjunction mate and commutes with the total derived limit. Evaluate the
comparison using the actual ordinary section equality and open units defining
compactFiniteEvaluation. Its projection is exactly the finite scalar mate in
SfQcqsCompactSupportRealizationSpec. Compose this comparison with the inverse of
sfQcqsCompactSupportRealization to obtain τ. Its projection equation is the one
above, since sfCompactSupportFiniteReductionIso is the chosen Roos projection
adjunct. The same simultaneous resolution identifies both signed Roos coordinates;
the normalized limit comparison and naturality on roofs determine τ uniquely.
No isomorphism is chosen from agreement of bare reduction isomorphism classes. -/
theorem compactRealization_existsUnique (c : Compactification f) :
    ∃! τ : sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ compactImage l E f c,
      CompactRealizationSpec l E K₀ hl f c τ := by
  sorry

/-- The identification determined by the actual integral compact-support projections.
Source: Bhatt--Scholze 6.7.6 (blueprint: def-weil-system-operation-exchange-realization). -/
def compactRealization (c : Compactification f) :=
  (compactRealization_existsUnique l E K₀ hl f c).exists.choose

/-- Alpha-shriek starts at the recorded integral Rf_!, uses its uniquely normalized
identification, then the actual system pullback realization and counit.
Source: blueprint alpha-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactAlpha (c : Compactification f) (gY : Y ⟶ Y) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E gY ⟶
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙
        integralComparisonDerivedSequencePullback l E gY ⋙ coefficientSequenceLimit l E Y :=
  whiskerRight (compactRealization l E K₀ hl f c).hom (integralDerivedPullback l E gY) ≫
    whiskerLeft (sfIntegralConstructible l E X).ι
      (sourceComparison l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) gY)

/-- Beta-shriek is the effective pullback counit inverse followed by the inverse
of that same projection-normalized Rf_! identification, on the pulled input.
Source: blueprint beta-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactBeta (c : Compactification f) (gX : X ⟶ X) :
    (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        integralComparisonDerivedSequencePullback l E gX ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙ coefficientSequenceLimit l E Y ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι :=
  whiskerRight (reductionPullbackIso l E gX).inv
      ((systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) ⋙ coefficientSequenceLimit l E Y) ≫
    whiskerLeft (constructibleIntegralPullback l E gX)
      (compactRealization l E K₀ hl f c).inv

/-- Reduction of the recorded operation, transported by the fixed identification.
Source: blueprint compact operation comparisons
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactOperationReduction (c : Compactification f) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ reduction l E Y ⟶
      (sfIntegralConstructible l E X).ι ⋙ reduction l E X ⋙
        (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g) :=
  whiskerRight (compactRealization l E K₀ hl f c).hom (reduction l E Y) ≫
    whiskerLeft (sfIntegralConstructible l E X).ι
      (operationReduction l E (systemDerivedOpen l E c.i ⋙ systemDirect l E c.g))

/-- Alpha-shriek is the same whole-system comparison for the fixed proper/open
composite, before evaluation at any finite coefficient exponent.
Source: blueprint alpha-shriek; Bhatt--Scholze 6.7.6--6.7.7
(blueprint: def-weil-system-operation-exchange-realization).
Proof: exact open extension and proper direct image preserve the quotient
cartesian condition on these constructible systems. Their Roos realization
has the common finite Tor interval supplied by compact-support constructibility.
Its reconstruction counit is invertible. Scheme-isomorphism pullback preserves
this computation, giving invertibility of the already defined alpha composite. -/
theorem compactAlpha_isIso (c : Compactification f) (g : Y ⟶ Y) [IsIso g]
    (K : sfIntegralConstructibleCategory l E X) :
    IsIso ((compactAlpha l E K₀ hl f c g).app K) := by
  sorry

/-- Integral compact exchange: proper system mate followed by the system open
exchange, then the single specified total-limit realization composite.
Source: blueprint `def:weil-compact-support-object`
(blueprint: def-weil-system-operation-exchange-realization). -/
def compactIntegralAmbient (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙
        (sfIntegralConstructible l E Y).ι ⋙ integralDerivedPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ (sfIntegralConstructible l E Y).ι :=
  compactAlpha l E K₀ hl f c gY ≫
    whiskerRight
      (whiskerLeft ((sfIntegralConstructible l E X).ι ⋙ reduction l E X)
        (systemCompactExchange l E c gX gB gY wp sj)) (coefficientSequenceLimit l E Y) ≫
    compactBeta l E K₀ hl f c gX

/-- Integral compact exchange on the recorded integral compact-support functor.
Its underlying map is exactly alpha-shriek, L(e), beta-shriek above.
Source: blueprint FrEx-shriek (blueprint: def-weil-system-operation-exchange-realization). -/
def compactIntegral (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB) :
    sfCompactSupportFiniteIntegralFunctor l K₀ hl c E ⋙ constructibleIntegralPullback l E gY ⟶
      constructibleIntegralPullback l E gX ⋙
        sfCompactSupportFiniteIntegralFunctor l K₀ hl c E where
  app K := ObjectProperty.homMk
    ((compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj).app K)
  naturality _K _L a := ObjectProperty.hom_ext _
    ((compactIntegralAmbient l E K₀ hl f c gX gB gY wp sj).naturality a)

/-- Reduction of the constructed integral direct exchange is its specified
whole-system exchange, through the actual operation and pullback counits.
Source: blueprint integral direct-image paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: substitute the alpha-L(e)-beta definition. Naturality of the system
adjunction counit moves e through reduction; its triangular identity cancels
the inserted reduction/limit pair. The remaining pullback counits are precisely
the displayed factors. Finite evaluation and systemExchange_evaluation then
give the prescribed finite exchange on every reduction of K. -/
theorem directIntegral_reduction (gX : X ⟶ X) (gY : Y ⟶ Y)
    [IsIso gX] [IsIso gY] (w : gX ≫ f = f ≫ gY)
    (K : sfIntegralConstructibleCategory l E X) :
    (reduction l E Y).map ((directIntegral l E K₀ hl f gX gY w).app K).hom ≫
        (operationReduction l E (systemDirect l E f)).app
          ((constructibleIntegralPullback l E gX).obj K).obj ≫
        (systemDirect l E f).map ((reductionPullbackIso l E gX).hom.app K) =
      (reductionPullbackIso l E gY).hom.app ((directImageFunctor l E K₀ hl f).obj K) ≫
        (integralComparisonDerivedSequencePullback l E gY).map
          ((operationReduction l E (systemDirect l E f)).app K.obj) ≫
        (systemExchange l E f gX gY w).app ((reduction l E X).obj K.obj) := by
  sorry

/-- Reduction of the constructed compact exchange is the specified proper/open
system composite through the same operation and pullback counits.
Source: blueprint integral compact-support paragraph
(blueprint: def-weil-system-operation-exchange-realization).
Proof: apply the counit naturality and triangle calculation used for direct
exchange to H = J_j followed by F_p. Exact open descent identifies its finite
evaluation with the canonical open-adjunction exchange. Evaluate the proper
mate by systemExchange_evaluation and preserve their specified composition.
The same c is used throughout, including the empty input and identity square. -/
theorem compactIntegral_reduction (c : Compactification f)
    (gX : X ⟶ X) (gB : c.Z ⟶ c.Z) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (wp : gB ≫ c.g = c.g ≫ gY) (sj : IsPullback gX c.i c.i gB)
    (K : sfIntegralConstructibleCategory l E X) :
    let H := systemDerivedOpen l E c.i ⋙ systemDirect l E c.g
    (reduction l E Y).map ((compactIntegral l E K₀ hl f c gX gB gY wp sj).app K).hom ≫
        (compactOperationReduction l E K₀ hl f c).app
          ((constructibleIntegralPullback l E gX).obj K) ≫
        H.map ((reductionPullbackIso l E gX).hom.app K) =
      (reductionPullbackIso l E gY).hom.app
          ((sfCompactSupportFiniteIntegralFunctor l K₀ hl c E).obj K) ≫
        (integralComparisonDerivedSequencePullback l E gY).map
          ((compactOperationReduction l E K₀ hl f c).app K) ≫
        (systemCompactExchange l E c gX gB gY wp sj).app ((reduction l E X).obj K.obj) := by
  sorry

end ConstructibleOperations

end WeilConjectures.FrobeniusExchange
