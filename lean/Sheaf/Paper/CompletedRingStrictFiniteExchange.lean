/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.Paper.CompletedFiniteComparisonModels
import Sheaf.Paper.NormalizedFiniteComparisonExistence
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange

/-!
# Strict finite open exchange over completed rings

Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before Rlim;
Stacks 03DI, 03DJ, 04J0, 06XN and 099N
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).

This identifies the simultaneous strict exchange with the canonical finite
open-unit exchange, on reductions of arbitrary unbounded completed-ring objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

private theorem finiteSourceModel_isIso (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P) :
    IsIso (cbcFiniteSourceModelMap d sq n P) := by
  have := pbcExtensionCounit_isIso (pbcAdicProjection U d n) P hP
  dsimp only [cbcFiniteSourceModelMap, cbcFiniteReductionModelMap, pbcComplexCounit]
  infer_instance

private theorem finiteTargetModel_isIso (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P) :
    IsIso (cbcFiniteTargetModelMap d sq n P) := by
  have := pbcExtensionCounit_isIso (pbcAdicProjection U d n) P hP
  dsimp only [cbcFiniteTargetModelMap, cbcFiniteReductionModelMap, pbcComplexCounit]
  infer_instance

private theorem kflat_resolutions (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (s : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P ∧
        QuasiIso s := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := pbcAdicCompletion T d) K
  exact ⟨P, s, hP, hs⟩

/-- Both finite comparison maps exist uniquely with their representative normalizations.
Source: Stacks 099N, 03DI, 06XN
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: use the normalized finite-evaluation comparison for completed tower pullback.
Open extension commutes with reduction by the summand tensor map [p] tensor b to
[p tensor b restricted to the open]. The constant-section comparisons and the
finite open/pullback scalar mates then give cbcSourceLevel and cbcTargetLevel on
ordinary models. Their tensor formulas agree with the universal counits. Flatness
of constant-to-completed coefficients makes these comparisons invertible on
K-flat representatives. Resolve an arbitrary complex and descend the natural
comparisons; the representative equations determine them uniquely. -/
theorem cbcFiniteComparisons_existsUnique (n : ℕ) :
    (∃! e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃! e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e)  := by
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := cbcNormalizedFiniteComparison_exists d sq n
  constructor
  · refine ⟨e, he, ?_⟩
    intro z hz
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (pbcModules U (pbcAdicCompletion U d)) (.up ℤ))
    intro K
    obtain ⟨P, s, hP, hs⟩ := kflat_resolutions d U K
    have : QuasiIso s := hs
    have hmodel := finiteSourceModel_isIso d sq n P hP
    have hp : z.hom.app (DerivedCategory.Q.obj P) = e.hom.app
        (DerivedCategory.Q.obj P) := by
      apply (cancel_mono (cbcFiniteSourceModelMap d sq n P)).1
      exact (eq_of_heq (hz P hP)).symm.trans (eq_of_heq (he P hP))
    apply (cancel_epi ((completedReductionTower U d ⋙
      cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ⋙
      pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (DerivedCategory.Q.map s))).1
    rw [z.hom.naturality, e.hom.naturality, hp]
  · refine ⟨f, hf, ?_⟩
    intro z hz
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (pbcModules U (pbcAdicCompletion U d)) (.up ℤ))
    intro K
    obtain ⟨P, s, hP, hs⟩ := kflat_resolutions d U K
    have : QuasiIso s := hs
    have hmodel := finiteTargetModel_isIso d sq n P hP
    have hp : z.hom.app (DerivedCategory.Q.obj P) = f.hom.app
        (DerivedCategory.Q.obj P) := by
      apply (cancel_mono (cbcFiniteTargetModelMap d sq n P)).1
      exact (eq_of_heq (hz P hP)).symm.trans (eq_of_heq (hf P hP))
    apply (cancel_epi ((completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
      cbcStrictOpen d j' sq.isOpenImmersion' ⋙
      pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (DerivedCategory.Q.map s))).1
    rw [z.hom.naturality, f.hom.naturality, hp]

/-- The canonical finite source identification, with its fixed counit equation.
Source: Stacks 099N (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
@[irreducible] def cbcSourceFiniteComparison (n : ℕ) :=
  (cbcFiniteComparisons_existsUnique d sq n).1.exists.choose

/-- The canonical finite target identification, with the same representative convention.
Source: Stacks 099N (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
@[irreducible] def cbcTargetFiniteComparison (n : ℕ) :=
  (cbcFiniteComparisons_existsUnique d sq n).2.exists.choose

/-- The finite inverse exchange with its completed-ring action, before localization.
Its component is exactly the open-unit adjunct, not an unrelated derived morphism.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteInverse (n : ℕ) : cbcFiniteTarget d sq n ⟶ cbcFiniteSource d sq n :=
  Functor.whiskerRight
    (@singleBetaInv.{u} (cbcFiniteRing d n) _ U' U X' X gU j' j g
      sq.isOpenImmersion sq.isOpenImmersion' sq.w) (cbcFiniteRes d X' n)

/-- The finite inverse is invertible for the chosen cartesian square.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: apply finite open base change to IsPullback.of_iso_pullback for the chosen
square. Scalar restriction preserves the resulting isomorphism. -/
@[instance] theorem cbcFiniteInverse_isIso (n : ℕ) : IsIso (cbcFiniteInverse d sq n) := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  have := singleBetaInv_isIso (cbcFiniteRing d n) gU j' j g sq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
  unfold cbcFiniteInverse
  infer_instance

/-- The canonical finite exchange after restriction of its finite scalar action.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteExchange (n : ℕ) :=
  Functor.mapDerivedCategoryNatIso (asIso (cbcFiniteInverse d sq n)).symm

/-- Strict finite exchange over the completed coefficient rings, on every reduction
K_bullet, with canonical finite components and their specified inverse mates.
Source: blueprint finite-exchange/reduction identification before Rlim;
Stacks 03DI, 03DJ, 04J0, 06XN and 099N
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: steps 1-6 are the construction and strict counit normalization of
cbcStrictExchange_existsUnique. Step 7 identifies the two finite objects by the
normalized constant/completed comparisons and the summand tensor reduction map.
Step 8 checks the inverse: scalar mates preserve the open unit and the cartesian
pullback compositor, so its adjunction transpose is exactly singleBetaInvApp.
The representative equations descend that equality to the displayed finite
square, also identifying the forward map.
Step 9: all maps were simultaneous natural transformations of strict diagrams.
Their naturality commutes with every quotient arrow, including identities and
composites. All component maps are module maps for the completed action through
the finite projection. No inverse limit or completeness hypothesis enters. -/
theorem completedRingStrictFiniteExchange :
    CbcStrictExchangeNormalization d sq (cbcStrictExchange d sq) ∧
      ∀ (K : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) (n : ℕ),
        HEq
          ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map
            ((cbcReductionStrictExchange d sq).hom.app K) ≫
          (cbcTargetFiniteComparison d sq n).hom.app K)
          ((cbcSourceFiniteComparison d sq n).hom.app K ≫
          (cbcFiniteExchange d sq n).hom.app ((cbcFiniteReduction d U n).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
