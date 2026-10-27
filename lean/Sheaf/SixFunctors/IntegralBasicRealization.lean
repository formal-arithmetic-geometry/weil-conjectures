/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.SixFunctors.IntegralBasicRealizationData
import Sheaf.SixFunctors.IntegralReductionPullbackModel
import Sheaf.SixFunctors.IntegralProperTowerTransition
import Sheaf.SixFunctors.IntegralOpenMateNormalization
import Sheaf.SixFunctors.IntegralSupportTowerNormalization
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.Prime.Infinite
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import all Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Sheaf.Paper.CoefficientConstantTowerRoos

/-! # Assembly of primitive integral realization comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem primeUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)

private theorem primeUnitSections (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))] : IsUnit (l : Γ(W, ⊤)) := by
  simpa only [map_natCast] using (primeUnit l D hl).map
    ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop).hom

private theorem reconstructionUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) [W.Over (Spec (.of D.k))] (K : Integral l E W)
    (hK : sfIntegralConstructible l E W K) :
    IsIso ((calculus l E W).adjunction.unit.app K) := by
  have hunit : IsUnit (l : Γ(W, ⊤)) := by
    simpa only [map_natCast] using (primeUnit l D hl).map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (W ↘ Spec (.of D.k)).appTop).hom
  apply (purNormalizedReconstruction l E W hunit (calculus l E W)).2 K
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact p.Prime := ⟨hprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hprime
      exponent_pos := by decide
      cardinality_eq := by simp
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  have hl₀ : l ≠ D₀.p := by change l ≠ p; omega
  exact ⟨D₀, hl₀, (sfDerivedComplete_iff_legacy l E W D₀ hl₀ K).mp hK.1⟩

private def restrictedUnitIso (W : Scheme.{u}) (P : ObjectProperty (Integral l E W))
    (h : ∀ K : P.FullSubcategory,
      IsIso ((calculus l E W).adjunction.unit.app K.obj)) :
    P.ι ≅ P.ι ⋙ (calculus l E W).reduction ⋙ coefficientSequenceLimit l E W := by
  let η := Functor.whiskerLeft P.ι (calculus l E W).adjunction.unit
  haveI : ∀ K, IsIso (η.app K) := h
  exact NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun f ↦ η.naturality f)

private def properComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ∀ K : (basicUnaryDomain l E X Y (Operations.push l E o p)).FullSubcategory,
      IsIso ((calculus l E X).adjunction.unit.app K.obj)) :
    basicUnarySource l E X Y (Operations.push l E o p) ≅
      basicUnaryTarget l E X Y (Operations.push l E o p) (ringedPush l E p) :=
  Functor.isoWhiskerLeft
      ((basicUnaryDomain l E X Y (Operations.push l E o p)).ι ⋙ (calculus l E X).reduction)
      (m.push l E p) ≪≫
    Functor.isoWhiskerRight
      (restrictedUnitIso l E X (basicUnaryDomain l E X Y (Operations.push l E o p)) h).symm
      (ringedPush l E p)

private theorem properTower (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X)
    (d : (coefficientSequenceLimit l E Y).obj
      ((Operations.push l E o p).obj ((calculus l E X).reduction.obj K)) ≅
        (ringedPush l E p).obj K) : basicProperTower l E o p K d := by
  let := integralOperationsDerivedCountableProducts l E Y
  let M := (Operations.push l E o p).obj ((calculus l E X).reduction.obj K)
  let T := (coefficientSequenceDerivedRestriction l E Y).obj M
  let a (n : ℕ) : (coefficientConstantTowerEvaluation l E Y n).obj T ≅
      sfDirectImageTerm l E p K n :=
    (coefficientRestrictedEvaluationIso l E Y n).app M ≪≫
      (scalarReductionDerivedRestriction l E Y n).mapIso
        (((o.evaluation p).evaluation n).app ((calculus l E X).reduction.obj K) ≪≫
          (proEtaleConstantDerivedDirectImage p
            (Padic.coefficientExtensionRing l E (n + 1))).mapIso
              (((calculus l E X).reductionEvaluation n).app K))
  let q := fun n : ℕ ↦ (coefficientConstantTowerProjection l E Y n).app T ≫ (a n).hom
  have hR := roos_transport
    (X := fun n ↦ (coefficientConstantTowerEvaluation l E Y n).obj T)
    (Y := sfDirectImageTerm l E p K)
    (fun n ↦ (normalizedDVRTowerTransition l E Y D hl n.le_succ).app T)
    (sfDirectImageTransition l E p K) (Iso.refl _) a
    (fun n ↦ (coefficientConstantTowerProjection l E Y n).app T) q
    (integralProperTowerTransition l E D hl o p K)
    (fun n ↦ by simp only [q, Iso.refl_hom, Category.id_comp])
    (coefficientConstantTower_roos l E Y D hl T)
  obtain ⟨hp, δ, hδ⟩ := hR
  have hδ' : ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E p K)
      ((coefficientSequenceLimit l E Y).obj M) (Pi.lift q) ε := by
    simpa only using (show ∃ ε, IsDerivedLimitTriangle (sfDirectImageTransition l E p K)
      ((coefficientSequenceLimit l E Y).obj M) (Pi.lift q) ε from ⟨δ, hδ⟩)
  obtain ⟨ε, hε⟩ := hδ'
  refine ⟨{ obj := (coefficientSequenceLimit l E Y).obj M
            projection := Pi.lift q
            boundary := ε
            roos := hε }, d, ?_⟩
  intro n
  simp only [Iso.hom_inv_id_assoc, Pi.lift_π]
  simp only [q, a, coefficientSequenceProjection, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  rfl

private def openComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (hu : ∀ K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory,
      IsIso ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K.obj)))
    (hr : ∀ K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory,
      IsIso ((m.openReduction l E j).app K.obj)) :
    basicUnarySource l E X Y (Operations.shriek l E o j) ≅
      basicUnaryTarget l E X Y (Operations.shriek l E o j) (ringedOpen l E j) := by
  let P := basicUnaryDomain l E X Y (Operations.shriek l E o j)
  let r := Functor.whiskerLeft P.ι (m.openReduction l E j)
  haveI : ∀ K, IsIso (r.app K) := hr
  let η := Functor.whiskerLeft (P.ι ⋙ ringedOpen l E j) (calculus l E Y).adjunction.unit
  haveI : ∀ K, IsIso (η.app K) := hu
  exact Functor.isoWhiskerRight
    (NatIso.ofComponents (fun K ↦ asIso (r.app K)) (fun f ↦ r.naturality f))
    (coefficientSequenceLimit l E Y) ≪≫
      (NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun f ↦ η.naturality f)).symm

/-- Specified primitive integral realizations on the recorded intermediate domains.
Source: fix-prop-coherence.proof.md, primitive comparison refinement
(blueprint: lem-sf-integral-basic-realization).

Proof:
1. Choose flat-term K-flat representatives by lem-pc-kflat-resolution. The quotient
models of lem-pur-quotient-system-flat-models give single strict pullback and tensor
towers and their actual transitions, natural before localization on cochain maps.
2. Exact countable products and lem-weil-strict-roos-comparison identify their strict
total limits with the quotient-complex Roos constructions. Use precisely C(a) then
the inverse of the zero-shifted-coordinate kernel inclusion on K-injective towers.
The uniqueness in lem-pur-flat-roos-functor-descent descends this normalization to
all derived morphisms. These are the published pullback and tensor model inverses.
3. Evaluate the actual system direct image, retaining the coefficient-restriction
transitions from lem-pur-coefficient-system-derived-comparison and its unbounded
refinement. The ordinary sectionwise limit comparison and its derived adjoint
conjugate identify its total limit with integral proper image. Compose with the
inverse actual reconstruction unit. This gives the defining proper reduction tower.
4. Apply lem-sf-integral-open-reduction-comparison. Its strict quotient map is the
open-adjunction mate of model.reductionPull. Total limit of its inverse, followed
by the inverse actual unit on j_!K, is exactly the displayed open comparison.
5. Apply the same proper comparison after open extension with one fixed (j,p).
The open and proper evaluation maps and the reduction evaluation identify the
entire restricted strict tower with the recorded compact-support tower. Every
transition is the larger-level proper/open functor applied to the quotient map,
then lem-sf-compact-support-restriction-of-scalars and composition of restrictions.
Take total limits with the prescribed projections. The projection-normalized
sfQcqsCompactSupportRealization identifies this with the recorded integral functor.
All common bounds and origin witnesses are retained by the specialized domains.
No expression or generator coherence is asserted. -/
theorem integralBasicRealization (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) : HasBasicRealizations l E D o := by
  obtain ⟨model⟩ := integralReductionPullbackModel l E o
  refine ⟨model, ?_, ?_⟩
  · intro W _ _ _ K hK _
    exact reconstructionUnit l E D _hl W K hK
  refine ⟨?_, ?_⟩
  · intro X Y v _ _ _ _ _ _ _ _ _ _
    exact Functor.isoWhiskerLeft
      (basicUnaryDomain l E Y X (IntegralSystemRealization.pull l E v)).ι
      (pullbackTensorIntegralPullbackModel l E v).symm
  refine ⟨?_, ?_⟩
  · intros
    rfl
  refine ⟨?_, ?_⟩
  · intro W _ _ _
    exact Functor.isoWhiskerLeft (basicTensorDomain l E W).ι
      (pullbackTensorIntegralTensorModel l E W).symm
  refine ⟨?_, ?_⟩
  · intros
    rfl
  refine ⟨?_, ?_⟩
  · intro X Y p _ _ _ _ _ _ _ _
    exact properComparison l E o model p
      (fun K ↦ reconstructionUnit l E D _hl X K.obj K.property.1)
  refine ⟨?_, ?_⟩
  · intros
    simp only [properComparison, restrictedUnitIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      NatIso.ofComponents_inv_app, asIso_inv]
    rfl
  refine ⟨?_, ?_⟩
  · intro X Y p _ _ _ _ _ _ _ _ K
    exact properTower l E D _hl o p K.obj _
  refine ⟨?_, ?_⟩
  · intro X Y j _ _ _ _ _ _ _ _ _ K
    exact (integralOpenMateNormalization l E o model j
      (by
        simpa only [map_natCast] using (primeUnit l D _hl).map
          ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop).hom)
      (by
        simpa only [map_natCast] using (primeUnit l D _hl).map
          ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop).hom)
      K.obj K.property.1 K.property.2.1 K.property.2.2).1
  refine ⟨?_, ?_⟩
  · intro X Y j _ _ _ _ _ _ _ _ _ K
    exact (integralOpenMateNormalization l E o model j
      (by
        simpa only [map_natCast] using (primeUnit l D _hl).map
          ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (X ↘ Spec (.of D.k)).appTop).hom)
      (by
        simpa only [map_natCast] using (primeUnit l D _hl).map
          ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (Y ↘ Spec (.of D.k)).appTop).hom)
      K.obj K.property.1 K.property.2.1 K.property.2.2).2
  refine ⟨?_, ?_⟩
  · intro X Y j _ _ _ _ _ _ _ _ _
    exact openComparison l E o model j
      (fun K ↦ (integralOpenMateNormalization l E o model j
        (primeUnitSections l D _hl X) (primeUnitSections l D _hl Y)
        K.obj K.property.1 K.property.2.1 K.property.2.2).1)
      (fun K ↦ (integralOpenMateNormalization l E o model j
        (primeUnitSections l D _hl X) (primeUnitSections l D _hl Y)
        K.obj K.property.1 K.property.2.1 K.property.2.2).2)
  refine ⟨?_, ?_⟩
  · intros
    simp only [openComparison, Iso.trans_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, asIso_hom, asIso_inv]
    rfl
  exact integralSupportTowerNormalization l E D o model

end WeilConjectures.IntegralSystemRealization
