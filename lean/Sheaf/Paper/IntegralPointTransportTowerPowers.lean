/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralPointTransportComparisons
public import Sheaf.Paper.CoefTowerCoaugmentation
public import Sheaf.Paper.IntegralPullbackComparisonRealization
public import Sheaf.Paper.InverseImagePullbackComparisonDerived
public import Sheaf.TraceFormula.PointTransportComposition
import all Sheaf.Paper.OrdinaryQuotientPullbackTowerComparison
import Sheaf.Paper.PointIntegralRestrictionNatural
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization

/-!
# Point transport on whole integral coefficient systems

Source: Weil blueprint, main-20261015, `sec-trace-formula/sk-d-weil`,
`prop-trf-rational-frobenius-integral-model.proof.md`, prerequisite to clause (3)
(blueprint: lem-trf-integral-point-transport-tower-powers).

The definitions below specify the strict-system map before localization, its naturality
and power law, and the normalized comparison with the completed integral realization.

## Main definitions and statements

* `IntegralPointTransportTower.transport`: the section-normalized whole-system map.
* `IntegralPointTransportTower.nu` and `zeta`: the normalized derived-limit comparisons.
* `IntegralPointTransportTower.Laws`: all power, evaluation and realization identities.
* `integralPointTransportTowerPowers`: the complete ten-step assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.pointReductionModuleDerived
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

namespace IntegralPointTransportTower

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Finite sections with their actual quotient R-action.
Source: blueprint proof steps 1--3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev finiteSections (n : ℕ) :=
  (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory ⋙
    (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointReductionQuotient l E n)).mapDerivedCategory

/-- The ordinary finite section composite, with its actual R-action.
Source: blueprint proof step 2 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
abbrev ordinaryFiniteSections (n : ℕ) :=
  pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)) ⋙
    ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n)

/-- Additivity is transported through the recorded identity-on-sections comparison.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance ordinaryFiniteSectionsAdditive (n : ℕ) : (ordinaryFiniteSections D l E n).Additive :=
  Functor.additive_of_iso (CoefTower.finiteSectionsRestriction D l E n)

/-- Left exactness is transported by the same canonical scalar-action comparison.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance ordinaryFiniteSectionsLimits (n : ℕ) : PreservesFiniteLimits
    (ordinaryFiniteSections D l E n) :=
  preservesFiniteLimits_of_natIso (CoefTower.finiteSectionsRestriction D l E n)

/-- Right exactness is transported by the same canonical scalar-action comparison.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
instance ordinaryFiniteSectionsColimits (n : ℕ) : PreservesFiniteColimits
    (ordinaryFiniteSections D l E n) :=
  preservesFiniteColimits_of_natIso (CoefTower.finiteSectionsRestriction D l E n)

/-- Whiskering by sections and then evaluating has exactly the component composite.
Source: blueprint proof step 2 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: evaluation of a whiskered tower is sections of the evaluated module; on
morphisms both maps are sections of the same n-th component. Functor extensionality
identifies these data and their identical equations. -/
theorem ordinarySectionsEvaluation_eq (n : ℕ) :
    ordinarySections D l E ⋙
        (evaluation ℕᵒᵖ (ModuleCat.{u + 1} (CoefTower.coefficient l E))).obj (op n) =
      (coefficientSequenceRestriction l E (Spec (.of D.k)) ⋙
        (evaluation ℕᵒᵖ (scalarReductionSource l E (Spec (.of D.k)))).obj (op n)) ⋙
          pointIntegralSections l E D.k := by
  rfl

/-- Evaluation uses the recorded restriction identity and finite scalar comparison.
Source: blueprint proof steps 2--3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def finiteSectionsWhisker (n : ℕ) :
    coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
        (scalarReductionRestriction l E (Spec (.of D.k)) n ⋙ pointIntegralSections l E D.k) ≅
      coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ ordinaryFiniteSections D l E n :=
  Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
    (CoefTower.finiteSectionsRestriction D l E n)

/-- The evaluation comparison with explicit functor associativity.
Source: blueprint proof steps 2--3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def ordinarySectionsEvaluation (n : ℕ) :
    ordinarySections D l E ⋙
        (evaluation ℕᵒᵖ (ModuleCat.{u + 1} (CoefTower.coefficient l E))).obj (op n) ≅
      coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙ ordinaryFiniteSections D l E n :=
  eqToIso (ordinarySectionsEvaluation_eq D l E n) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (coefficientSequenceRestriction_evaluation l E (Spec (.of D.k)) n))
      (pointIntegralSections l E D.k) ≪≫
    Functor.associator (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
      (scalarReductionRestriction l E (Spec (.of D.k)) n) (pointIntegralSections l E D.k) ≪≫
    finiteSectionsWhisker D l E n

/-- Localize that same comparison in the point-fibre derived presentation.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def sectionsEvaluation (n : ℕ) :
    sections D l E ⋙ moduleEvaluation l E n ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙ finiteSections D l E n :=
  letI := ordinaryFiniteSectionsAdditive D l E n
  letI := ordinaryFiniteSectionsLimits D l E n
  letI := ordinaryFiniteSectionsColimits D l E n
  Functor.isoWhiskerRight (sectionsFactors D l E).symm (moduleEvaluation l E n) ≪≫
    (Functor.mapDerivedCategoryCompIso (ordinarySections D l E)
      ((evaluation ℕᵒᵖ (ModuleCat.{u + 1} (CoefTower.coefficient l E))).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinarySectionsEvaluation D l E n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
      (ordinaryFiniteSections D l E n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n)
      (Functor.mapDerivedCategoryCompIso
        (pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1)))
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointReductionQuotient l E n)))

section OrdinaryEvaluationProof
attribute [local irreducible] OrdinaryTowerProof.inverseEvaluation

/-- Evaluation of system pullback is fixed on every tensor-unit generator.
Source: blueprint proof steps 1--2 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: restriction to a vertical slice preserves the actual inverse-image colimit,
sheafification and tensor insertion. Both sides are the same finite module pullback.
The equation on every generator, over every site object, fixes its adjunction unit,
so determines the comparison uniquely and gives its inverse. -/
theorem ordinaryEvaluationComparison_existsUnique (r n : ℕ) :
    ∃! e : ordinaryPullback D l E r ⋙ coefficientSequenceEvaluation l E (Spec (.of D.k)) n ≅
        coefficientSequenceEvaluation l E (Spec (.of D.k)) n ⋙
          integralOperationsLevelPullback l E ((pointFrobeniusAut D) ^ r).hom n,
      ∀ (M : coefficientSequenceModules l E (Spec (.of D.k))) (U : (Spec (.of D.k)).ProEt)
        (x : M.val.obj (op (n, U))),
        (e.hom.app M).val.app
            (op ((proEtaleBaseChange ((pointFrobeniusAut D) ^ r).hom).obj U))
            (coefficientEvaluationSection l E (Spec (.of D.k))
              ((ordinaryPullback D l E r).obj M) n
              (op ((proEtaleBaseChange ((pointFrobeniusAut D) ^ r).hom).obj U))
              (integralComparisonSequenceGenerator l E ((pointFrobeniusAut D) ^ r).hom
                M n U x)) =
          integralOperationsPullbackGenerator l E ((pointFrobeniusAut D) ^ r).hom n
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M) U
            (coefficientEvaluationSection l E (Spec (.of D.k)) M n (op U) x) := by
  let g := ((pointFrobeniusAut D) ^ r).hom
  let e := (OrdinaryTowerProof.inverseEvaluation l E g n).symm
  refine ⟨e, ?_, ?_⟩
  · exact OrdinaryTowerProof.inverseEvaluation_inv_unit l E g n
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi ((OrdinaryTowerProof.inverseEvaluation l E g n).hom.app M)).1
    let adj := coefficientProEtaleModuleAdjunction.{u, u} g
      (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    ext U x
    let x₀ := (eqToHom (coefficientSequenceEvaluationAb_eq l E (Spec (.of D.k)) M n U)) x
    have hx : coefficientEvaluationSection l E (Spec (.of D.k)) M n U x₀ = x := by
      dsimp only [coefficientEvaluationSection, x₀]
      rw [← CategoryTheory.comp_apply, eqToHom_trans, eqToHom_refl, CategoryTheory.id_apply]
    change (e'.hom.app M).val.app (op ((proEtaleBaseChange g).obj U.unop))
        (((OrdinaryTowerProof.inverseEvaluation l E g n).hom.app M).val.app
          (op ((proEtaleBaseChange g).obj U.unop))
          (integralOperationsPullbackGenerator l E g n
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M) U.unop x)) =
      (e.hom.app M).val.app (op ((proEtaleBaseChange g).obj U.unop))
        (((OrdinaryTowerProof.inverseEvaluation l E g n).hom.app M).val.app
          (op ((proEtaleBaseChange g).obj U.unop))
          (integralOperationsPullbackGenerator l E g n
            ((coefficientSequenceEvaluation l E (Spec (.of D.k)) n).obj M) U.unop x))
    rw [← hx, OrdinaryTowerProof.inverseEvaluation_unit]
    exact (he' M U.unop x₀).trans
      (OrdinaryTowerProof.inverseEvaluation_inv_unit l E g n M U.unop x₀).symm

end OrdinaryEvaluationProof

/-- The unique generator-normalized ordinary finite evaluation comparison.
Source: blueprint proof step 2 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def ordinaryEvaluationComparison (r n : ℕ) :=
  (ordinaryEvaluationComparison_existsUnique D l E r n).exists.choose

/-- The same comparison localized, in the recorded intrinsic finite pullback presentation.
Source: blueprint proof step 3 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def evaluationComparison (r n : ℕ) :
    pullback D l E r ⋙ coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ≅
      coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n ⋙
        finiteDerivedPullback l E n ((pointFrobeniusAut D) ^ r).hom :=
  letI := integralOperationsLevelPullback_additive l E ((pointFrobeniusAut D) ^ r).hom n
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  letI := sfIntrinsicPullback_additive (Padic.coefficientExtensionRing l E (n + 1))
    ((pointFrobeniusAut D) ^ r).hom
  letI := sfIntrinsicPullback_preservesFiniteLimits
    (Padic.coefficientExtensionRing l E (n + 1)) ((pointFrobeniusAut D) ^ r).hom
  letI := sfIntrinsicPullback_preservesFiniteColimits
    (Padic.coefficientExtensionRing l E (n + 1)) ((pointFrobeniusAut D) ^ r).hom
  let e := inverseImageFiniteIntrinsicPullbackComparison ((pointFrobeniusAut D) ^ r).hom
    (Padic.coefficientExtensionRing l E (n + 1))
  let : PreservesFiniteLimits
      (integralOperationsLevelPullback l E ((pointFrobeniusAut D) ^ r).hom n) :=
    preservesFiniteLimits_of_natIso e.symm
  let : PreservesFiniteColimits
      (integralOperationsLevelPullback l E ((pointFrobeniusAut D) ^ r).hom n) :=
    preservesFiniteColimits_of_natIso e.symm
  (Functor.mapDerivedCategoryCompIso (ordinaryPullback D l E r)
    (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryEvaluationComparison D l E r n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E (Spec (.of D.k)) n)
      (integralOperationsLevelPullback l E ((pointFrobeniusAut D) ^ r).hom n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n)
      (Functor.mapDerivedCategoryNatIso
        (inverseImageFiniteIntrinsicPullbackComparison ((pointFrobeniusAut D) ^ r).hom
          (Padic.coefficientExtensionRing l E (n + 1))))

/-- The specified integral kappa of part (b), evaluated at the actual derived object.
Source: blueprint proof step 7 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def kappa (hl : l ≠ D.p) (r : ℕ)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  inverseImagePullbackComparisonDerived l E ((pointFrobeniusAut D) ^ r).hom
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) N

/-- The actual kappa is invertible on the stated bounded constructible domain.
Source: blueprint proof step 7 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: on a flat-term K-flat resolution, apply exact inverse image to the canonical
completion augmentation. Derived completeness makes that augmentation invertible.
The product comparison and finite tensor-unit isomorphisms identify its image with
the zero-homotopy cone map defining kappa, on both cone coordinates. Thus this
specified map, rather than merely some map with the same reductions, is invertible. -/
theorem kappa_isIso (hl : l ≠ D.p) (r : ℕ)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hN : sfIntegralConstructible l E (Spec (.of D.k)) N) : IsIso (kappa D l E hl r N) := by
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := le_rfl
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := Nat.ne_of_lt (Nat.lt_of_succ_le hp)
  have hc : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) N :=
    ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E (Spec (.of D.k)) D₀ hl₀ N).mp hN.1⟩
  obtain ⟨S, hS⟩ := coefficientDerivedSystemEvaluationCalculus l E (Spec (.of D.k))
  obtain ⟨_, _, _, κinv, hleft, hright, _⟩ :=
    isomorphismDerivedPullbackComparisonNormalization l E ((pointFrobeniusAut D) ^ r).hom
      (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) S hS N hc
  exact ⟨⟨κinv, hright, hleft⟩⟩

/-- nu is a_r after the inverse of the actual kappa, only on the asserted domain.
Source: blueprint proof step 8 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def nu (hl : l ≠ D.p) (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)) :
    (integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).obj
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≅
      (coefficientSequenceLimit l E (Spec (.of D.k))).obj ((pullback D l E r).obj C) :=
  letI := kappa_isIso D l E hl r _ hC
  (asIso (kappa D l E hl r _)).symm ≪≫ (inverseLimitComparison D l E r).app C

/-- Power-r sigma is the same recorded integral restriction recipe at h^r.
Source: blueprint proof steps 1 and 8 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: restriction at h^r is linear for the transported coefficient action. It
commutes with differentials. The sectionwise colimit identification makes insertion
and sheafification the identity on these section carriers. Every term section is
specified below, proving uniqueness. At r=1 this is frobeniusPointIntegralSigma. -/
theorem integralSigma_existsUnique (r : ℕ)
    (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    ∃! f : ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj K ⟶
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
          ((Functor.mapHomologicalComplex
            (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom) (.up ℤ)).obj K),
      ∀ (i : ℤ) (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        f.f i x = (K.X i).val.map (pointPowerRestriction D r).op x := by
  let sigma := (PointIntegralRestrictionNatural.existsUnique D l E r).exists.choose
  have hsigma := (PointIntegralRestrictionNatural.existsUnique D l E r).exists.choose_spec
  let f : ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj
        (((inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom).mapHomologicalComplex
          (.up ℤ)).obj K) :=
    { f i := sigma.app (K.X i)
      comm' i j _ := (sigma.naturality (K.d i j)).symm }
  refine ⟨f, fun i x ↦ hsigma (K.X i) x, ?_⟩
  intro g hg
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  exact (hg i x).trans (hsigma (K.X i) x).symm

/-- The uniquely specified power-r extension of integral sigma.
Source: blueprint proof step 8 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def integralSigma (r : ℕ) (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :=
  (integralSigma_existsUnique D l E r K).exists.choose

/-- The actual derived sigma, conjugated by the localization's representative isomorphism.
Source: blueprint proof steps 3 and 8
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def derivedSigma (r : ℕ) (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :
    (pointFibreIntegralAmbient D l E).obj N ⟶
      (pointFibreIntegralAmbient D l E).obj
        ((inverseImageIntegralDerived l E ((pointFrobeniusAut D) ^ r).hom).obj N) :=
  (pointFibreIntegralAmbient D l E).map (DerivedCategory.Q.objObjPreimageIso N).inv ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
      (DerivedCategory.Q.objPreimage N) ≫
    DerivedCategory.Q.map (integralSigma D l E r (DerivedCategory.Q.objPreimage N)) ≫
    (pointIntegralSections l E D.k).mapDerivedCategoryFactors.inv.app
      ((Functor.mapHomologicalComplex
        (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom) (.up ℤ)).obj
          (DerivedCategory.Q.objPreimage N)) ≫
    (pointFibreIntegralAmbient D l E).map
      ((Functor.mapDerivedCategoryFactors
        (inverseImageIntegralModules l E ((pointFrobeniusAut D) ^ r).hom)).inv.app
          (DerivedCategory.Q.objPreimage N)) ≫
    (pointFibreIntegralAmbient D l E).map
      ((inverseImageIntegralDerived l E ((pointFrobeniusAut D) ^ r).hom).map
        (DerivedCategory.Q.objObjPreimageIso N).hom)

/-- The integral transport is Gamma(kappa) after the actual sigma, for every power.
Source: blueprint proof step 8 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def iota (hl : l ≠ D.p) (r : ℕ)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))) :=
  derivedSigma D l E r N ≫ (pointFibreIntegralAmbient D l E).map (kappa D l E hl r N)

/-- Constructibility needed to define the next nu, with no assumption on the input system.
Source: blueprint proof step 9 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: pullback by an isomorphism preserves bounded constructible integral objects.
The already specified nu identifies its output with the limit of G_r C. -/
theorem pullbackLimitConstructible (hl : l ≠ D.p) (r : ℕ)
    (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)) :
    sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj ((pullback D l E r).obj C)) := by
  let := frobeniusPointPrimeInvertible D l hl
  exact (sfIntegralConstructible l E _).prop_of_iso (nu D l E hl r C hC)
    ((integralOperations_preserve_constructible l E
      ((pointFrobeniusAut D) ^ r).hom).1 _ hC).1

/-- c^E is exactly the compositor specified by integralComparisonComposition.
The argument B records the already normalized realization conventions of that dependency.
Source: blueprint proof step 9 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def integralCompositor (hl : l ≠ D.p) (B : IntegralComparisonSystem.{u} l) (m : ℕ)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hN : sfIntegralConstructible l E (Spec (.of D.k)) N) :
    (integralDerivedPullback l E ((pointFrobeniusAut D) ^ (m + 1)).hom).obj N ≅
      (integralDerivedPullback l E (pointFrobeniusAut D).hom).obj
        ((integralDerivedPullback l E ((pointFrobeniusAut D) ^ m).hom).obj N) :=
  letI := frobeniusPointPrimeInvertible D l hl
  eqToIso (congrArg (fun f ↦ (integralDerivedPullback l E f).obj N) (powerHom D m).symm) ≪≫
    integralComparisonComposition l E B (pointFrobeniusAut D).hom
      ((pointFrobeniusAut D) ^ m).hom ⟨N, hN⟩

/-- The whole-system realized arrow, transported by its specified nu and zeta.
Source: blueprint proof steps 8--10
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def realizedTransport (hl : l ≠ D.p) (r : ℕ)
    (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)) :=
  (zeta D l E).inv.app C ≫
    (moduleLimit l E).map ((transport D l E r).app C) ≫
    (zeta D l E).hom.app ((pullback D l E r).obj C) ≫
    (pointFibreIntegralAmbient D l E).map (nu D l E hl r C hC).inv

/-- The fixed quotient augmentation, made an isomorphism by derived completeness.
Source: blueprint proof step 10 (blueprint: lem-trf-integral-point-transport-tower-powers). -/
def reductionComparison (B : IntegralComparisonSystem.{u} l)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hN : sfIntegralConstructible l E (Spec (.of D.k)) N) :=
  letI := (B.coefficient E).complete (Spec (.of D.k)) ⟨N, hN⟩
  asIso (((B.coefficient E).system (Spec (.of D.k))).adjunction.unit.app N)

/-- The limit of the simultaneous derived reduction is the original constructible input.
Source: blueprint proof step 10 (blueprint: lem-trf-integral-point-transport-tower-powers).
Proof: the completion augmentation is reductionComparison, which is an isomorphism
by completeness. Bounded constructibility is invariant under that isomorphism. -/
theorem reductionLimitConstructible (B : IntegralComparisonSystem.{u} l)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hN : sfIntegralConstructible l E (Spec (.of D.k)) N) :
    sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj
        (((B.coefficient E).system (Spec (.of D.k))).reduction.obj N)) := by
  exact (sfIntegralConstructible l E _).prop_of_iso (reductionComparison D l E B N hN) hN

/-- All clauses are propositions about the specified constructions, with no free maps.
Source: blueprint clause (3) and the Global powers paragraph
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
def Laws (hl : l ≠ D.p) : Prop :=
  (∀ (r : ℕ) (C C' : coefficientSequenceDerived l E (Spec (.of D.k))) (f : C ⟶ C'),
    (sections D l E).map f ≫ (transport D l E r).app C' =
      (transport D l E r).app C ≫ (sections D l E).map ((pullback D l E r).map f)) ∧
  (∀ (m : ℕ), 1 ≤ m → ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
    (transport D l E (m + 1)).app C = (transport D l E m).app C ≫
      (transport D l E 1).app ((pullback D l E m).obj C) ≫
      (sections D l E).map ((compositor D l E m).hom.app C)) ∧
  (∀ (r n : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k))),
    intrinsicFiniteTorsionConstructible l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
        ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) →
    (moduleEvaluation l E n).map ((transport D l E r).app C) ≫
        (sectionsEvaluation D l E n).hom.app ((pullback D l E r).obj C) ≫
        (finiteSections D l E n).map ((evaluationComparison D l E r n).hom.app C) =
      (sectionsEvaluation D l E n).hom.app C ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory.map
          (pointPowerTransportFinite D l hl E r n
            ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C))) ∧
  (∀ (r : ℕ) (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))),
    sfIntegralConstructible l E (Spec (.of D.k)) N → IsIso (kappa D l E hl r N)) ∧
  (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k)))
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
    (moduleLimit l E).map ((transport D l E r).app C) ≫
        (zeta D l E).hom.app ((pullback D l E r).obj C) =
      (zeta D l E).hom.app C ≫
        iota D l E hl r ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
        (pointFibreIntegralAmbient D l E).map (nu D l E hl r C hC).hom) ∧
  (∀ (r : ℕ) (C C' : coefficientSequenceDerived l E (Spec (.of D.k))) (f : C ⟶ C')
    (hC : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C))
    (hC' : sfIntegralConstructible l E (Spec (.of D.k))
      ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C')),
    (integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).map
        ((coefficientSequenceLimit l E (Spec (.of D.k))).map f) ≫
        (nu D l E hl r C' hC').hom =
      (nu D l E hl r C hC).hom ≫
        (coefficientSequenceLimit l E (Spec (.of D.k))).map ((pullback D l E r).map f)) ∧
  (∀ (r : ℕ) (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))),
    sfIntegralConstructible l E (Spec (.of D.k)) N →
      sfIntegralConstructible l E (Spec (.of D.k))
        ((integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).obj N)) ∧
  (∀ (B : IntegralComparisonSystem.{u} l) (m : ℕ), 1 ≤ m →
    ∀ (C : coefficientSequenceDerived l E (Spec (.of D.k)))
      (hC : sfIntegralConstructible l E (Spec (.of D.k))
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
    (nu D l E hl (m + 1) C hC).hom =
      (integralCompositor D l E hl B m
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) hC).hom ≫
      (integralDerivedPullback l E (pointFrobeniusAut D).hom).map
        (nu D l E hl m C hC).hom ≫
      (nu D l E hl 1 ((pullback D l E m).obj C)
        (pullbackLimitConstructible D l E hl m C hC)).hom ≫
      (coefficientSequenceLimit l E (Spec (.of D.k))).map ((compositor D l E m).hom.app C)) ∧
  (∀ K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ,
    HEq (integralSigma D l E 1 K) (frobeniusPointIntegralSigma D l E K)) ∧
  (∀ N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))),
    HEq (iota D l E hl 1 N) (frobeniusPointTransportIntegral D l hl E N)) ∧
  (∀ (B : IntegralComparisonSystem.{u} l) (r : ℕ)
    (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
    (hN : sfIntegralConstructible l E (Spec (.of D.k)) N),
    (pointFibreIntegralAmbient D l E).map (reductionComparison D l E B N hN).hom ≫
        realizedTransport D l E hl r
          (((B.coefficient E).system (Spec (.of D.k))).reduction.obj N)
          (reductionLimitConstructible D l E B N hN) ≫
        (pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).map
            (reductionComparison D l E B N hN).inv) = iota D l E hl r N)

end IntegralPointTransportTower

/-- Remaining power, evaluation, realization, naturality, and reduction clauses assembled from the
unresolved whole-system transport steps. Source: the proof plan for the ten steps
(blueprint: lem-trf-integral-point-transport-tower-powers). -/
theorem integralPointTransportTowerPowers_remaining
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    (∀ (m : ℕ), 1 ≤ m → ∀ C : coefficientSequenceDerived l E (Spec (.of D.k)),
      (IntegralPointTransportTower.transport D l E (m + 1)).app C =
        (IntegralPointTransportTower.transport D l E m).app C ≫
          (IntegralPointTransportTower.transport D l E 1).app
            ((IntegralPointTransportTower.pullback D l E m).obj C) ≫
          (IntegralPointTransportTower.sections D l E).map
            ((IntegralPointTransportTower.compositor D l E m).hom.app C)) ∧
    (∀ (r n : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k))),
      intrinsicFiniteTorsionConstructible l E (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) (Spec (.of D.k))
        ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C) →
      (IntegralPointTransportTower.moduleEvaluation l E n).map
          ((IntegralPointTransportTower.transport D l E r).app C) ≫
        (IntegralPointTransportTower.sectionsEvaluation D l E n).hom.app
          ((IntegralPointTransportTower.pullback D l E r).obj C) ≫
        (IntegralPointTransportTower.finiteSections D l E n).map
          ((IntegralPointTransportTower.evaluationComparison D l E r n).hom.app C) =
      (IntegralPointTransportTower.sectionsEvaluation D l E n).hom.app C ≫
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointReductionQuotient l E n)).mapDerivedCategory.map
        (pointPowerTransportFinite D l hl E r n
          ((coefficientSequenceDerivedEvaluation l E (Spec (.of D.k)) n).obj C))) ∧
    (∀ (r : ℕ) (C : coefficientSequenceDerived l E (Spec (.of D.k)))
      (hC : sfIntegralConstructible l E (Spec (.of D.k))
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
      (IntegralPointTransportTower.moduleLimit l E).map
          ((IntegralPointTransportTower.transport D l E r).app C) ≫
        (IntegralPointTransportTower.zeta D l E).hom.app
          ((IntegralPointTransportTower.pullback D l E r).obj C) =
      (IntegralPointTransportTower.zeta D l E).hom.app C ≫
        IntegralPointTransportTower.iota D l E hl r
          ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) ≫
        (pointFibreIntegralAmbient D l E).map
          (IntegralPointTransportTower.nu D l E hl r C hC).hom) ∧
    (∀ (r : ℕ) (C C' : coefficientSequenceDerived l E (Spec (.of D.k))) (f : C ⟶ C')
      (hC : sfIntegralConstructible l E (Spec (.of D.k))
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C))
      (hC' : sfIntegralConstructible l E (Spec (.of D.k))
        ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C')),
      (integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).map
          ((coefficientSequenceLimit l E (Spec (.of D.k))).map f) ≫
        (IntegralPointTransportTower.nu D l E hl r C' hC').hom =
      (IntegralPointTransportTower.nu D l E hl r C hC).hom ≫
        (coefficientSequenceLimit l E (Spec (.of D.k))).map
          ((IntegralPointTransportTower.pullback D l E r).map f)) ∧
    (∀ (B : IntegralComparisonSystem.{u} l) (m : ℕ), 1 ≤ m →
      ∀ (C : coefficientSequenceDerived l E (Spec (.of D.k)))
        (hC : sfIntegralConstructible l E (Spec (.of D.k))
          ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C)),
      (IntegralPointTransportTower.nu D l E hl (m + 1) C hC).hom =
        (IntegralPointTransportTower.integralCompositor D l E hl B m
          ((coefficientSequenceLimit l E (Spec (.of D.k))).obj C) hC).hom ≫
        (integralDerivedPullback l E (pointFrobeniusAut D).hom).map
          (IntegralPointTransportTower.nu D l E hl m C hC).hom ≫
        (IntegralPointTransportTower.nu D l E hl 1
          ((IntegralPointTransportTower.pullback D l E m).obj C)
          (IntegralPointTransportTower.pullbackLimitConstructible D l E hl m C hC)).hom ≫
        (coefficientSequenceLimit l E (Spec (.of D.k))).map
          ((IntegralPointTransportTower.compositor D l E m).hom.app C)) ∧
    (∀ (K : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ),
      HEq (IntegralPointTransportTower.integralSigma D l E 1 K)
        (frobeniusPointIntegralSigma D l E K)) ∧
    (∀ (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k)))),
      HEq (IntegralPointTransportTower.iota D l E hl 1 N)
        (frobeniusPointTransportIntegral D l hl E N)) ∧
    (∀ (B : IntegralComparisonSystem.{u} l) (r : ℕ)
      (N : DerivedCategory (integralTowerModules l E (Spec (.of D.k))))
      (hN : sfIntegralConstructible l E (Spec (.of D.k)) N),
      (pointFibreIntegralAmbient D l E).map
          (IntegralPointTransportTower.reductionComparison D l E B N hN).hom ≫
        IntegralPointTransportTower.realizedTransport D l E hl r
          (((B.coefficient E).system (Spec (.of D.k))).reduction.obj N)
          (IntegralPointTransportTower.reductionLimitConstructible D l E B N hN) ≫
        (pointFibreIntegralAmbient D l E).map
          ((integralDerivedPullback l E ((pointFrobeniusAut D) ^ r).hom).map
            (IntegralPointTransportTower.reductionComparison D l E B N hN).inv) =
      IntegralPointTransportTower.iota D l E hl r N) := by
  sorry


/-- Whole-system point transport, its powers, and its integral realization.

Source: the complete prerequisite to clause (3) of
`prop-trf-rational-frobenius-integral-model.proof.md`
(blueprint: lem-trf-integral-point-transport-tower-powers).

Proof plan from the DAG, with its ten steps and exact comparison normalizations:
1. Put $F_r=(h^r)^{-1}$, with the module action transported through the specified coefficient
isomorphism. The site-equivalence description in [lem-weil-proetale-isomorphism-inverse-image](1)
identifies $(F_rM)(U\to s)$ with $M(U\xrightarrow{h^r\circ u}s)$. Under it the
restriction/colimit-insertion/sheafification map $\sigma_{r,M}$ in
[def-weil-frobenius-point-transport] is exactly restriction along $h^r$ at the final object. Indeed
its colimit index is $(s\xrightarrow{h^r}s)$ and its coprojection is the reindexing identification
at that object. The coefficient isomorphism sends the insertion of a constant $a\in A_n$ to the same
constant $a$, by its definition in [def-weil-proetale-inverse-image]. Thus $\sigma_{r,M}$ is
$A_n$-linear. The finite tensor comparison $j_{r,M}:F_rM\to(h^r)^*M$, $x\mapsto x\otimes1$, has
inverse $x\otimes a\mapsto c_n^{-1}(a)x$, by balancing. These formulas hold for every module,
without constructibility. They identify the tensor-pullback model of $G_r$ with $F_r$; below we
retain $j_r$ whenever the tensor model is used.
Uses: lem-weil-proetale-isomorphism-inverse-image, def-weil-proetale-inverse-image,
def-weil-frobenius-point-transport, def-weil-inverse-image-pullback-comparison.

2. Represent $C$ by a complex of strict semilinear systems $M$. At level $n$ define
$u_{r,n}=\Gamma(j_{r,M_n})\sigma_{r,M_n}$. A differential or a transition
$v:M_{n+1}\to\operatorname{Res}M_n$ is a map of underlying sheaves. Its restrictions commute with
$\operatorname{res}_{h^r}$, and its inverse image commutes with the colimit coprojections and
sheafification maps. At the tensor insertion, applying the coefficient quotient $\rho_n:B_{n+1}\to
B_n$ sends $x\otimes1$ to $v(x)\otimes\rho_n(1)=v(x)\otimes1$. The coefficient square
$\pi_nc_{\widehat R}=c_nF_r(\pi_n)$ in [def-weil-inverse-image-pullback-comparison] makes this
equation $\widehat R_s$-linear after restriction. Hence $u_{r,\bullet}$ is a chain map of whole
$R$-module towers, with the original transitions of $M$. A chain map $f:M\to M'$ satisfies
$\Gamma_\bullet(G_rf)u_{r,M}=u_{r,M'}\Gamma_\bullet(f)$ by the same restriction and tensor formulas.
Its level $n$ is the stated finite point transport whenever that derived evaluation is bounded
constructible, since this is its defining recipe.
Uses: def-weil-frobenius-point-transport, def-weil-inverse-image-pullback-comparison.

3. Restriction of scalars is exact: it changes only the scalar action, leaving kernels and cokernels
of underlying abelian sheaves unchanged. Exactness of systems is componentwise, as in
[lem-coef-derived-system-evaluation-calculus]. The functor $G_r$ is exact by the equivalence of
[lem-weil-proetale-isomorphism-inverse-image], and sections are exact by
[lem-weil-point-proetale-sections-exact]. Consequently the two functors between complex categories
used in step 2 preserve quasi-isomorphisms. Their natural chain transformation therefore localizes
to a specified $I_r$ on $D(\mathscr S_s)$. Explicitly, the commutative square of step 2 for each
arrow of a roof $C\xleftarrow{a}M\xrightarrow{b}D$, with $a$ a quasi-isomorphism of systems, also
commutes after inverting the images of $a$. This proves the asserted naturality for every derived
SYSTEM morphism, without trying to lift an arbitrary family of evaluated maps.
Uses: lem-coef-derived-system-evaluation-calculus, lem-weil-proetale-isomorphism-inverse-image,
lem-weil-point-proetale-sections-exact.

4. Check the power formula before localization in the reindexing model of step 1. The two successive
restrictions, first along $h^m$ and then along $h$, are restriction along $h^m\circ h=h^{m+1}$ by
the sheaf restriction axiom. The inverse-image compositor identifies $F_1F_mM$ with $F_{m+1}M$ by
associating these same site reindexings. In the tensor model its inverse is the termwise canonical
module-pullback comparison of [lem-weil-pbc-proetale-derived-pullback-composition]; multiplying the
two inserted units sends $(x\otimes1)\otimes1$ to $x\otimes1$. Thus it is precisely the specified
$t_m$, and on the whole strict tower $u_{m+1,M}=\Gamma_\bullet(t_{m,M})u_{1,G_mM}u_{m,M}$. This is
an equality of chain maps: the restriction calculation is in every degree and commutes with the
actual transitions checked in step 2. Localization gives the displayed power identity in the derived
tower category.
Uses: lem-weil-proetale-isomorphism-inverse-image,
lem-weil-pbc-proetale-derived-pullback-composition, def-weil-frobenius-point-transport.

5. For a strict tower complex $X$, use $H(X)=\operatorname{Cone}(1-s_X)[-1]$ in the coordinates
$H(X)^i=(\prod_nX_n^{i-1})\oplus(\prod_nX_n^i)$, $d(b,a)=(-db-(1-s_X)a,da)$. Products of sheaf
modules on $s_{\mathrm{proet}}$ are sectionwise and exact by
[lem-weil-proetale-countable-products-exact]. Products of $R$-modules are exact too: choose a
preimage in each coordinate of a family of surjections. Regard $R$-modules as modules on the
one-object trivial site. Thus [lem-weil-strict-roos-comparison] identifies these cone functors,
including their maps and strict augmentations, with TOTAL derived inverse limit. The
completed-module functor $F_r$ is exact by [def-weil-inverse-image-pullback-comparison] and
preserves products by the site reindexing of step 1. Sections are exact by
[lem-weil-point-proetale-sections-exact] and preserve products because they are sectionwise. Apply
[lem-cbc-exact-product-functor-strict-limit] to these two functors. It gives the specified natural
comparisons $a_{r,C}:F_r\mathcal L_sC\xrightarrow{\sim}\mathcal L_sG_rC$ (including $j_r$) and
$\zeta_C:R\lim\Gamma_\bullet C\xrightarrow{\sim}\Gamma(s,\mathcal L_sC)$, the latter in the inverse
direction to that lemma's comparison. In cone coordinates the comparisons are the canonical product
comparisons on BOTH summands, with no extra off-diagonal term. The lemma's resolution normalization
identifies them with applying inverse image, respectively sections, to the entire limit cone.
Uses: lem-weil-proetale-countable-products-exact, lem-weil-strict-roos-comparison,
def-weil-inverse-image-pullback-comparison, lem-weil-point-proetale-sections-exact,
lem-cbc-exact-product-functor-strict-limit.

6. Write $X=U_sM$ and $N=H(X)$ for the moment. Under the comparisons of step 5, $R\lim(I_{r,C})$ is
the actual two-component chain map $H(u_r)(b,a)=((\prod_nu_{r,n})b,(\prod_nu_{r,n})a)$. This is a
chain map because the transition equation in step 2 gives $(1-s_{G_rX})\prod u_{r,n}=(\prod
u_{r,n})(1-s_X)$. On a product sheaf, restriction sends $(x_n)_n$ to $(x_n|_{h^r})_n$. Hence
$\sigma_{r,\prod X_n}$, followed by the canonical inverse-image product comparison, is
$\prod_n\sigma_{r,X_n}$. Restriction also preserves the two direct-sum coordinates in $H(X)$.
Consequently, on BOTH the shifted and unshifted coordinates, $H(u_r)$ equals sections of the cone
comparison $a_{r,C}$ after $\sigma_{r,H(X)}$. The natural normalized cone identifications of
[lem-weil-strict-roos-comparison] therefore give
$$\zeta_{G_rC}R\lim(I_{r,C})=\Gamma(s,a_{r,C})\sigma_{r,\mathcal L_sC}\zeta_C.$$
This calculation proves an equality of derived maps on whole systems; it does not infer it from
equality after projection to each $n$.
Uses: lem-weil-strict-roos-comparison, lem-cbc-exact-product-functor-strict-limit,
def-weil-frobenius-point-transport.

7. Now assume $N=\mathcal L_sC\in D^b_c(s,R)$. Choose a flat-term K-flat resolution $Q\to N$ by
[lem-pc-kflat-resolution] and write $Q_n=Q\otimes_{\widehat R_s}B_n$. The $L=E$ case of
[lem-weil-finite-free-completed-scalar-comparison] gives the natural isomorphism $\chi_N:N\to
H((\operatorname{Res}_nQ_n)_n)$, represented on $Q$ by $z\mapsto(0,(z\otimes1)_n)$. It applies
because derived completeness is part of [def-weil-derived-complete-integral-detailed]. Applying
exact $F_r$, its product comparison and the tower isomorphisms $j_{r,Q_n}$ of step 1 gives an
isomorphism
$$F_rN\xrightarrow{F_r\chi_N}F_rH(Q_\bullet)
\xrightarrow{\sim}H(F_rQ_\bullet)\xrightarrow{H(j_r)}H(((h^r)^*Q_n)_n)=P_rN.$$
On $F_rQ$ its formula is $w\mapsto(0,(j_{r,Q_n}F_r(z\mapsto z\otimes1)(w))_n)$. This is EXACTLY the
map $\tilde\theta$ defining part (b) of [def-weil-inverse-image-pullback-comparison], followed by
the inverse of $F_r(Q\to N)$. Thus the displayed isomorphism is the specified $\kappa_N$, not merely
some isomorphism with the same reductions. Independence and naturality follow from the
resolution-independent natural completion comparison, the product comparison in step 5, and the
functorial descent in [lem-pur-integral-operations-well-defined].
Uses: lem-pc-kflat-resolution, lem-weil-finite-free-completed-scalar-comparison,
def-weil-derived-complete-integral-detailed, def-weil-inverse-image-pullback-comparison,
lem-cbc-exact-product-functor-strict-limit, lem-pur-integral-operations-well-defined.

8. By definition the stated realization comparison is $\nu_{r,C}=a_{r,C}\kappa_N^{-1}$. The integral
transport of [def-weil-frobenius-point-transport], with the recipe applied to $h^r$, is
$\iota_N^{(r)}=\Gamma(s,\kappa_N)\sigma_{r,N}$. Therefore
$\Gamma(s,\nu_{r,C})\iota_N^{(r)}=\Gamma(s,a_{r,C})\sigma_{r,N}$ by cancellation of the actual
$\kappa_N$ and its inverse. Substitution into the equality of step 6 proves precisely
$$\zeta_{G_rC}R\lim(I_{r,C})=\Gamma(s,\nu_{r,C})\iota_N^{(r)}\zeta_C.$$
The assumption is only on $N$; nowhere was $C$ replaced by the reduction system of $N$.
Uses: def-weil-frobenius-point-transport, def-weil-inverse-image-pullback-comparison.

9. Naturality: the product comparisons and normalized Roos identifications are natural on the
derived tower category by [lem-cbc-exact-product-functor-strict-limit] and
[lem-weil-strict-roos-comparison], and step 7 makes $\kappa_N$ natural and invertible on
$D^b_c(s,R)$. Inverse-image side: put $d_m:F_1F_m\xrightarrow{\sim}F_{m+1}$ for site reindexing. On
either cone summand
$$a_{m+1,C}d_{m,N}=\mathcal L_s(t_{m,C})a_{1,G_mC}F_1(a_{m,C}),$$
since projecting either product gives the same twice-reindexed projection with the same tensor units
multiplied, as in step 4, and the universal property of the product identifies the summand maps.
Pullback side: $P_mN\in D^b_c(s,R)$ by [lem-weil-isomorphism-derived-pullback], and
[lem-trf-integral-inverse-image-comparison-composition] for $h$ followed by $h^m$ gives
$c^E_{m,N}\kappa^{(m+1)}_Nd_{m,N}=\kappa^{(1)}_{P_mN}F_1(\kappa^{(m)}_N)$, with $c^E$ as in
[lem-trf-integral-pullback-comparison-realization]. Naturality of $\kappa^{(1)}$ at the isomorphism
$\nu_{m,C}=a_{m,C}(\kappa^{(m)}_N)^{-1}$ gives $(\kappa^{(1)}_{\mathcal
L_sG_mC})^{-1}P_1(\nu_{m,C})=F_1(a_{m,C})F_1(\kappa^{(m)}_N)^{-1}(\kappa^{(1)}_{P_mN})^{-1}$. Hence
$$\mathcal L_s(t_{m,C})\nu_{1,G_mC}P_1(\nu_{m,C})c^E_{m,N}=\mathcal
L_s(t_{m,C})a_{1,G_mC}F_1(a_{m,C})d_{m,N}^{-1}(\kappa^{(m+1)}_N)^{-1}
=a_{m+1,C}(\kappa^{(m+1)}_N)^{-1}=\nu_{m+1,C}.$$
With step 4 this is the stated compositor compatibility. No equality is deduced from individual
derived evaluations.
Uses: lem-cbc-exact-product-functor-strict-limit, lem-weil-strict-roos-comparison,
def-weil-inverse-image-pullback-comparison, lem-weil-pbc-proetale-derived-pullback-composition,
lem-weil-isomorphism-derived-pullback, lem-trf-integral-pullback-comparison-realization,
lem-trf-integral-inverse-image-comparison-composition.

10. For $C=\mathcal R_sN_0$, the reduction construction in
[lem-coef-derived-system-evaluation-calculus] is the strict system $(Q\otimes B_n)_n$ for one
flat-term K-flat $Q\to N_0$. If $N_0\in D^b_c(s,R)$, the same completion map of
[lem-weil-finite-free-completed-scalar-comparison] identifies $\mathcal L_sC$ with $N_0$, naturally
and with its actual quotient augmentation. Thus steps 2 and 8 identify the realized power-$r$ map
with $\iota_{N_0}^{(r)}$, which recovers the announced reduction-tower case. Conversely a
finite-output compact-support system whose derived limit is bounded constructible satisfies exactly
the hypothesis used in step 7, regardless of its normalization or Tor-amplitude. Steps 1-6 applied
to every system, and steps 7-9 only used derived completeness of that limit. This proves the final
scope assertions.
Uses: lem-coef-derived-system-evaluation-calculus, lem-weil-finite-free-completed-scalar-comparison.
-/
theorem integralPointTransportTowerPowers
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    IntegralPointTransportTower.Laws D l E hl := by
  refine ⟨?_, ?_⟩
  · intro r C C' f
    exact (IntegralPointTransportTower.transport D l E r).naturality f
  · obtain ⟨hpow, heval, hreal, hnu, hcomp, hsigma, hiota, hred⟩ :=
      integralPointTransportTowerPowers_remaining D l hl E
    exact ⟨hpow, heval, IntegralPointTransportTower.kappa_isIso D l E hl,
      hreal, hnu, (fun r N hN => by
        let := frobeniusPointPrimeInvertible D l hl
        exact (integralOperations_preserve_constructible l E
          ((pointFrobeniusAut D) ^ r).hom).1 N hN |>.1), hcomp, hsigma, hiota, hred⟩


end WeilConjectures
