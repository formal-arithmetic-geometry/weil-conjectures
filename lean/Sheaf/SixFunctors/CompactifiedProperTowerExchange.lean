/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.AlgebraicGeometry.ProperCoincidenceNormalized
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.SixFunctors.CompactSupportProperImageTower
public import Sheaf.Paper.CompleteProetaleStrictTowerRealization
public import Sheaf.Paper.CompletedStrictOpenExchange
public import Sheaf.Paper.CompletedOrdinaryComparisons
public import Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
public import Sheaf.Paper.SfImmersionCompletedPullbackComparison
public import Sheaf.Paper.IntegralCompletedCoefficientTransport
public import Sheaf.Paper.CompactificationCompletedRealization
import Sheaf.Paper.RefinementExchangeCoherence
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.CompletedRlimFunctor
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import WeilConjectures.Compactification.CategoryBaseChange
import Sheaf.Paper.CompactificationCoherence
import Sheaf.Paper.ConstantCompletionEquivalence

/-! # Proper compactification towers and the completed exchange

Source: Bhatt--Scholze, Definition 6.7.6; Stacks 0D6E and 0A07;
blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).

The strict maps are constructed before evaluation and before total derived limit.
The integral statement uses the recorded completed coefficient sheaf and action.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace AlgebraicGeometry.Scheme.CompactifiedProperTower

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The identity-open map is the section-normalized adjunction identification.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def openModuleId (T : Scheme.{u}) : cbcOpenShriek d (𝟙 T) inferInstance ≅ 𝟭 _ :=
  (cbcRealizationOpenAdj d (𝟙 T)).leftAdjointIdIso
    ((proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T))

/-- Degreewise localization of the identity-open identification.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def openId (T : Scheme.{u}) : cbcJ d (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso (openModuleId d T) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- Identity-open identification in the derived category of strict towers.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def openTowerId (T : Scheme.{u}) : cbcRealizationJ d (𝟙 T) ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (openModuleId d T) ≪≫
      Functor.whiskeringRightObjIdIso) ≪≫ Functor.mapDerivedCategoryIdIso _

/-- Proper coincidence before reconstruction: direct image of a_X.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def properId {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :
    (d.push f).obj ((cbcJ d (𝟙 X)).obj K) ≅ (d.push f).obj K :=
  (d.push f).mapIso ((openId d X).app K)

/-- The actual ordinary direct-image strict quotient tower.
Its evaluation uses towerPushReductionEvaluation, including scalar restriction.
Source: Stacks 0D6E, 0A07; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
abbrev ordinaryTower {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :=
  (d.towerPush f).obj ((completedReductionTower X d).obj K)

/-- The identity-open compact-support strict quotient tower, before total limit.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
abbrev supportTower {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :=
  (d.towerPush f).obj
    ((cbcRealizationJ d (𝟙 X)).obj ((completedReductionTower X d).obj K))

/-- Degreewise a_X, pushed forward as one strict derived tower isomorphism.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def strictId {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :
    supportTower d f K ≅ ordinaryTower d f K :=
  (d.towerPush f).mapIso ((openTowerId d X).app ((completedReductionTower X d).obj K))

/-- Ordinary reconstruction is direct image of the completion unit, followed by
its specified direct-image/limit comparison.
Source: Stacks 0A07; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def ordinaryReconstruction {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :
    (d.push f).obj K ⟶ (completedRlim Y (d.completedRing Y)).obj (ordinaryTower d f K) :=
  (d.push f).map (d.completionUnit X K) ≫
    (d.directImageRlimIso f).hom.app ((completedReductionTower X d).obj K)

/-- The compact-support reconstruction retains the normalized strict open reduction.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def supportReconstruction {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :
    (d.push f).obj ((cbcJ d (𝟙 X)).obj K) ⟶
      (completedRlim Y (d.completedRing Y)).obj (supportTower d f K) :=
  ordinaryReconstruction d f ((cbcJ d (𝟙 X)).obj K) ≫
    (completedRlim Y (d.completedRing Y)).map
      ((d.towerPush f).map (cbcRealizationReduction d (𝟙 X) K).hom)


/-- The coefficient coordinates used by the completed exchange datum.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def coefficients : WeilConjectures.PurCompactSupport.Coefficients.{u} where
  ring := d.completedRing
  pull := d.integralRingIso

/-- Strict reconstruction and its projection normalization at identity open.
Source: blueprint prop-functor-package, clause (3); Stacks 0A07 and 0D6E
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: apply the strict open-reduction comparison at the identity. Its unit
normalization identifies it with degreewise a_X. Push forward this equality on
strict towers. Naturality of the completion unit and the specified direct-image
limit comparison gives the reconstruction equation. Derived limit projections
are natural, so the same equation holds after each projection. The evaluation
comparison is the K-injective normalized direct-image/scalar restriction map;
its naturality gives the stated finite proper identification. -/
theorem strictReconstruction {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) :
    supportReconstruction d f K ≫
        (completedRlim Y (d.completedRing Y)).map (strictId d f K).hom =
      (properId d f K).hom ≫ ordinaryReconstruction d f K ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      (pbcTowerTransition Y (d.completedRing Y) m n h).app (supportTower d f K) ≫
          (pbcTowerEvaluation Y (d.completedRing Y) n).map (strictId d f K).hom =
        (pbcTowerEvaluation Y (d.completedRing Y) m).map (strictId d f K).hom ≫
          (pbcTowerTransition Y (d.completedRing Y) m n h).app (ordinaryTower d f K)) ∧
    (∀ n : ℕ,
      supportReconstruction d f K ≫
          (completedRlimProjection Y (d.completedRing Y) n).app (supportTower d f K) ≫
          (pbcTowerEvaluation Y (d.completedRing Y) n).map (strictId d f K).hom ≫
          d.towerPushReductionEvaluation f K n =
        (properId d f K).hom ≫ ordinaryReconstruction d f K ≫
          (completedRlimProjection Y (d.completedRing Y) n).app (ordinaryTower d f K) ≫
          d.towerPushReductionEvaluation f K n) := by
  sorry

/-- Identity-open completed exchange is the specified completed proper mate.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the open restriction mate at identities is the identity on the same sections.
The open-unit normalization identifies the strict open mate with degreewise identity,
including its transitions. The completed strict-tower realization therefore has
only the proper exchange factor. Apply total derived limit, cancel its normalized
source and target realizations, and use naturality of a_X. -/
theorem identityExchange {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    [IsProper f] [IsProper f']
    (sp : ChosenCartesianSquare g' f' f g)
    (sj : OpenImmersionSquare g' (𝟙 X') (𝟙 X) g')
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :
    completedCompactSupportExchange d (Compactification.ofIsProper f)
        (Compactification.ofIsProper f') g' sp sj r a ha K ≫
        (properId d f' ((d.completedPull g').obj K.obj)).hom =
      (d.completedPull g).map (properId d f K.obj).hom ≫ d.completedExchange sp K.obj ∧
    (cbcDatumCompletedExchange d sj r a ha).app K ≫
        (openId d X').hom.app ((d.completedPull g').obj K.obj) =
      (d.completedPull g').map ((openId d X).hom.app K.obj) := by
  sorry


/-- The two recorded open-extension presentations are compared by their specified
adjunctions to exactly the same inverse image.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def openCoordinates {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (WeilConjectures.PurCompactSupport.openExtension (coefficients d) j).mapDerivedCategory ≅
      cbcJ d j :=
  Adjunction.leftAdjointUniq
    (WeilConjectures.PurCompactSupport.openDerivedAdjunction (coefficients d) j)
    (cbcDerivedOpenAdjunction d j)

/-- The canonical comparison of the two proper/open coefficient presentations.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def supportCoordinates {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    WeilConjectures.PurCompactSupport.image (coefficients d) c ≅ cbcSupport d c :=
  Functor.isoWhiskerRight (openCoordinates d c.i) (d.push c.g)

/-- The finite coefficient inverse-image comparison respects the quotient map.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: both maps come from inverse image of the same quotient of the coefficient
ring. Their values on constant sections agree, and sheafification and the
projection-normalized finite coefficient comparison preserve that equality. -/
theorem quotientSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (d.finiteRingIso f (n + 1)).hom ≫ pbcAdicQuotient X d (n + 1) n (Nat.le_succ n) =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n)) ≫
        (d.finiteRingIso f n).hom := by
  sorry

/-- The ordinary finite transition: Rf_{*,n+1} of the quotient map, then
canonical direct-image/scalar restriction, then restriction to the completed ring.
Source: Stacks 0D6E; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def ordinaryFiniteTransition {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X)
    (n : ℕ) :=
  (pbcDerivedRestrict (d.projection Y (n + 1))).map
    ((d.finitePush f (n + 1)).map
      (pbcReductionTransition (d.projection X (n + 1))
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) (d.projection X n)
        (pbcAdicProjection_comp X d (n + 1) n (Nat.le_succ n)) K) ≫
      (proEtaleRingRestrictionDerivedDirectImage f
        (d.finiteRing Y (n + 1)) (d.finiteRing Y n)
        (d.finiteRing X (n + 1)) (d.finiteRing X n)
        (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n))
        (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
        (d.finiteRingIso f (n + 1)) (d.finiteRingIso f n)
        (quotientSquare d f n)).inv.app ((d.reduction X n).obj K)) ≫
    (pbcDerivedRestrictComp (d.projection Y (n + 1))
      (pbcAdicQuotient Y d (n + 1) n (Nat.le_succ n)) (d.projection Y n)
      (pbcAdicProjection_comp Y d (n + 1) n (Nat.le_succ n))).hom.app
        ((d.finitePush f n).obj ((d.reduction X n).obj K))

/-- The actual ordinary strict tower has precisely the prescribed quotient transitions.
Source: blueprint prop-functor-package, clause (3); Stacks 0D6E
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: compute reduction on a K-flat complex: its transition is tensor with the
quotient map. Evaluate a K-injective tower to compute direct image. The normalized
restriction/direct-image comparison is identity on the same sections. Composing
the two scalar restrictions gives exactly ordinaryFiniteTransition. Localization
preserves this equality of strict diagrams. -/
theorem ordinaryTransitions {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X)
    (n : ℕ) :
    (pbcTowerTransition Y (d.completedRing Y) (n + 1) n (Nat.le_succ n)).app
        (ordinaryTower d f K) ≫ d.towerPushReductionEvaluation f K n =
      d.towerPushReductionEvaluation f K (n + 1) ≫ ordinaryFiniteTransition d f K n := by
  sorry

/-- The identity-open beta normalization holds before evaluation on strict towers.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the strict inverse exchange is the open-unit transpose. Under the
degreewise identity-open isomorphism that unit is the identity. The triangle
identity therefore identifies beta with the displayed identity comparison in
every degree and tower index, compatibly with every transition. Localize this
strict equation; no faithfulness of separate evaluations is needed. -/
theorem identityStrictOpen {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (sj : OpenImmersionSquare g' (𝟙 X') (𝟙 X) g')
    (M : DerivedCategory (d.towers X)) :
    (cbcStrictExchange d sj).hom.app M ≫
        (openTowerId d X').hom.app ((completedTowerPullback g' d).obj M) =
      (completedTowerPullback g' d).map ((openTowerId d X).hom.app M) := by
  sorry

/-- Finite proper coincidence is compatible with every refinement comparison.
Source: blueprint prop-functor-package, clause (3), finite refinement normalization
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: finite proper coincidence at the identity-open compactification is
Rf_*(a_X). Finite compactification coherence identifies its comparison through
any common refinement with the specified canonical comparison. Composing with
this fixed identity-open map gives the displayed finite proper coincidence.
The argument uses the witnessed bounded-below finite domain only. -/
theorem finiteRefinement (B : Type (u + 1)) [CommRing B] [Finite B]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c e : Compactification f) (r : e.Refinement c)
    (s : e.Refinement (Compactification.ofIsProper f)) :
    Etale.properCoincidenceCandidatePlus B f c =
      Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso B r ≪≫
        (Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso B s).symm ≪≫
          Etale.properCoincidenceIdentityOpenPlus B f := by
  sorry

/-- The finite proper map in reduction coordinates is Rf_{*,n} of a_X.
The normalized open tensor comparison identifies its source with (1_X)_!K_n.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def finiteProper {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) (n : ℕ) :=
  (d.finitePush f n).mapIso ((d.reduction X n).mapIso ((openId d X).app K))

/-- The source finite projection includes the inverse strict open-reduction map.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def sourceEvaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) (n : ℕ) :=
  (pbcTowerEvaluation Y (d.completedRing Y) n).map
      ((d.towerPush f).map (cbcRealizationReduction d (𝟙 X) K).inv) ≫
    d.towerPushReductionEvaluation f ((cbcJ d (𝟙 X)).obj K) n

/-- Evaluation is the finite proper coincidence, with the actual source and target maps.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the identity-open tensor comparison is the transpose of its ordinary unit.
The triangle identities identify it with reduction of a_X. Apply proper image to
that strict identity, then its normalized evaluation comparison. Naturality of
finite pushforward/scalar restriction yields the displayed finite map. -/
theorem finiteNormalization {X Y : Scheme.{u}} (f : X ⟶ Y) (K : d.derived X) (n : ℕ) :
    (pbcTowerEvaluation Y (d.completedRing Y) n).map (strictId d f K).hom ≫
        d.towerPushReductionEvaluation f K n =
      sourceEvaluation d f K n ≫
        (reductionDerivedRestrict Y (d.projection Y n)).map (finiteProper d f K n).hom := by
  sorry

/-- Canonical refinement-defined proper coincidences are independent of all choices.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: finite proper coincidence is normalized by Rf_*(a_X), and common-refinement
coherence identifies every finite comparison with it on the retained origin domain.
For integral coefficients, realize the refinement/open/proper words on actual strict
constant-R towers. The refinement-exchange theorem applies to their compatible
finite étale origins. Apply total limit, conjugate by the normalized realizations,
and descend through the fully faithful equivalence on complete coefficients.
Common domination and arrow equalization give independence, and cancellation of
the intermediate invertible factors gives the cocycle. No Tor interval is imposed. -/
theorem refinementIndependence {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj)
    (c c₁ c₂ : Compactification f)
    (u₁ : c₁.Refinement c) (v₁ : c₁.Refinement (Compactification.ofIsProper f))
    (u₂ : c₂.Refinement c) (v₂ : c₂.Refinement (Compactification.ofIsProper f)) :
    cbcCompactificationComparison d u₁ v₁ r a ha K origins ≪≫ properId d f K.obj =
      cbcCompactificationComparison d u₂ v₂ r a ha K origins ≪≫ properId d f K.obj := by
  sorry

/-- Completed pullback preserves the complete witnessed domain needed for refinement.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: completed pullback is the total limit of pullback of the strict reduction
tower. Its finite quotient comparison identifies each reduction with finite
pullback. Pulling the retained etale origins gives compatible etale origins,
and Koszul reconstruction shows intrinsic completeness of this total limit. -/
theorem pulledDomain {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (_origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    cbcCompleteProperty d X' r a ha ((d.completedPull g').obj K.obj) ∧
      PbcHasCompatibleEtaleOrigins X' d ((d.completedPull g').obj K.obj) := by
  sorry

/-- The base-changed complete object, using only the derived completeness conclusion.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def pulledObject {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    (cbcCompleteProperty d X' r a ha).FullSubcategory :=
  ⟨(d.completedPull g').obj K.obj, (pulledDomain d g' r a ha K origins).1⟩

/-- Every compactification gives the same proper exchange under its refinement-defined
proper coincidence, with no restriction on the chosen common refinements.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: strict refinement-exchange coherence identifies the exchange for c with
that for the identity-open compactification through any common refinement.
The compatible finite origins are exactly the theorem's refinement domain.
Apply total limit and the compactified-word realization. The constant-completion
equivalence descends the resulting equation uniquely to completed-ring modules.
Insert identityExchange and cancel the intermediate common-refinement factors.
Independence and the cocycle imply that the displayed equality holds for every
choice of the four refinement arrows. -/
theorem refinementExchange {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsProper f] [IsProper f'] (sp : ChosenCartesianSquare g' f' f g)
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (spp : ChosenCartesianSquare gb c'.g c.g g)
    (sjj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj)
    (e : Compactification f) (e' : Compactification f')
    (u : e.Refinement c) (v : e.Refinement (Compactification.ofIsProper f))
    (u' : e'.Refinement c') (v' : e'.Refinement (Compactification.ofIsProper f')) :
    completedCompactSupportExchange d c c' gb spp sjj r a ha K ≫
        (cbcCompactificationComparison d u' v' r a ha
          (pulledObject d g' r a ha K origins)
          (pulledDomain d g' r a ha K origins).2).hom ≫
        (properId d f' ((d.completedPull g').obj K.obj)).hom =
      (d.completedPull g).map
          ((cbcCompactificationComparison d u v r a ha K origins).hom ≫
            (properId d f K.obj).hom) ≫ d.completedExchange sp K.obj := by
  sorry

section Integral
open WeilConjectures WeilConjectures.PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The completed coefficient comparison respects geometric inverse image.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: compose both maps with each positive quotient projection. The defining
normalization of completedRingIso and the coefficient inverse-image comparison
identify both composites with the same finite constant-section map. Limit
uniqueness gives the equality, including identity and empty schemes. -/
theorem coefficientSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((pbcIntegralDatum l E).integralRingIso f).hom ≫
        (ImmersionCompletedPullback.completedRingIso l E X).hom =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (ImmersionCompletedPullback.completedRingIso l E Y).hom ≫
        ((completed l E).pull f).hom := by
  sorry

/-- The actual canonical completed coefficient change, retaining every finite projection.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def coefficientChange : Change (coefficients (pbcIntegralDatum l E)) (completed l E) where
  map := fun T ↦ (ImmersionCompletedPullback.completedRingIso l E T).hom
  square := coefficientSquare l E

/-- Restriction from the published integral coordinates to the completed-exchange
coordinates, along the specified ring isomorphism rather than an arbitrary equivalence.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
abbrev restrict (T : Scheme.{u}) :=
  pbcDerivedRestrict ((coefficientChange l E).map T)

/-- Direct-image comparison for this coefficient change, with its specified
K-injective normalization.
Source: Stacks 0D6E; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def pushComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    restrict l E X ⋙ (pbcIntegralDatum l E).push f ≅
      push (completed l E) f ⋙ restrict l E Y :=
  (proEtaleRingRestrictionDerivedDirectImage f
    ((pbcIntegralDatum l E).completedRing Y) ((completed l E).ring Y)
    ((pbcIntegralDatum l E).completedRing X) ((completed l E).ring X)
    ((coefficientChange l E).map Y) ((coefficientChange l E).map X)
    ((pbcIntegralDatum l E).integralRingIso f) ((completed l E).pull f)
    (coefficientSquare l E f)).symm

/-- The uncompleted proper identification is uniquely specified by direct image of
identity-open a_X in the completed-exchange coordinates.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the coefficient map is an isomorphism, so its derived scalar restriction
is fully faithful. Conjugate properId by the specified compact-support and
proper-image scalar comparisons. Full faithfulness gives its unique lift and
reflects invertibility. The adjunction-unit normalization makes it precisely
proper image of the degreewise identity-open map. -/
theorem ambientProper_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    ∃! α : (image (completed l E) (Compactification.ofIsProper f)).obj K ≅
        (push (completed l E) f).obj K,
      (restrict l E Y).mapIso α =
        ((restriction (coefficientChange l E) (Compactification.ofIsProper f)).app K).symm ≪≫
          (supportCoordinates (pbcIntegralDatum l E) (Compactification.ofIsProper f)).app
            ((restrict l E X).obj K) ≪≫
          properId (pbcIntegralDatum l E) f ((restrict l E X).obj K) ≪≫
            (pushComparison l E f).app K := by
  sorry

/-- The ambient proper coincidence, fixed by a unique normalization.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def ambientProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X)) :
    (image (completed l E) (Compactification.ofIsProper f)).obj K ≅
      (push (completed l E) f).obj K :=
  (ambientProper_existsUnique l E f K).exists.choose

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsProper f]

/-- The canonical integral proper coincidence uses the recorded compact-support
realization, with the same coefficient map as the completed exchange.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def integralProper (K : sfIntegralConstructibleCategory l E X) :
    ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
        (Compactification.ofIsProper f) E).obj K).obj ≅
      (push (completed l E) f).obj K.obj :=
  ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl)
    (Compactification.ofIsProper f)).app K).symm ≪≫ ambientProper l E f K.obj

end Integral
/-- The compactified proper-tower exchange package.
Source: Bhatt--Scholze Definition 6.7.6 and Stacks Tags 0D6E, 0A07;
blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).

Proof: use the section-normalized identity-open adjunction and the strict
proper-image tower. The quotient maps are the canonical derived scalar-reduction
maps, and their direct-image transitions are the normalized coefficient
restriction maps. The strict identity comparison is natural in every transition.
The direct-image/Rlim comparison and its completion unit give the reconstruction
and projection equations. The normalized open beta map is the identity at both
identity opens, so the strict completed exchange reduces to the proper mate.
Finite evaluation gives the prescribed finite proper comparison. Finally apply
common-refinement exchange coherence and the constant-completion equivalence;
the intermediate word realizations cancel, yielding independence and the cocycle.
No comparison for discrete non-torsion etale coefficients is used. -/
theorem properTowerExchange {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {g' : X' ⟶ X}
    [IsProper f] [IsProper f'] (sp : ChosenCartesianSquare g' f' f g)
    (sj : OpenImmersionSquare g' (𝟙 X') (𝟙 X) g')
    {r : ℕ} {a : Fin r → A} {ha : Ideal.span (Set.range a) = d.ideal}
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (origins : PbcHasCompatibleEtaleOrigins X d K.obj) :
    supportReconstruction d f K.obj ≫
        (completedRlim Y (d.completedRing Y)).map (strictId d f K.obj).hom =
      (properId d f K.obj).hom ≫ ordinaryReconstruction d f K.obj ∧
    (∀ n : ℕ,
      (pbcTowerEvaluation Y (d.completedRing Y) n).map (strictId d f K.obj).hom ≫
          d.towerPushReductionEvaluation f K.obj n =
        sourceEvaluation d f K.obj n ≫
          (reductionDerivedRestrict Y (d.projection Y n)).map
            (finiteProper d f K.obj n).hom) ∧
    (completedCompactSupportExchange d (Compactification.ofIsProper f)
        (Compactification.ofIsProper f') g' sp sj r a ha K ≫
        (properId d f' ((d.completedPull g').obj K.obj)).hom =
      (d.completedPull g).map (properId d f K.obj).hom ≫ d.completedExchange sp K.obj) ∧
    (∀ (c c₁ c₂ : Compactification f)
      (u₁ : c₁.Refinement c) (v₁ : c₁.Refinement (Compactification.ofIsProper f))
      (u₂ : c₂.Refinement c) (v₂ : c₂.Refinement (Compactification.ofIsProper f)),
      cbcCompactificationComparison d u₁ v₁ r a ha K origins ≪≫ properId d f K.obj =
        cbcCompactificationComparison d u₂ v₂ r a ha K origins ≪≫ properId d f K.obj) := by
  sorry


section IntegralNormalization
open WeilConjectures WeilConjectures.PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}} (f : X ⟶ Y)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsProper f]

/-- The actual strict coefficient restriction, applied before localization.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
abbrev towerRestriction (T : Scheme.{u}) :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
    (proEtaleRingRestrictScalars ((coefficientChange l E).map T))).mapDerivedCategory

/-- Evaluation commutes with exact coefficient restriction before localization.
Source: Stacks 0941; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def towerRestrictionEvaluation (T : Scheme.{u}) (n : ℕ) :
    towerRestriction l E T ⋙
        pbcTowerEvaluation T ((pbcIntegralDatum l E).completedRing T) n ≅
      coefficientConstantTowerEvaluation l E T n ⋙ restrict l E T :=
  (Functor.mapDerivedCategoryCompIso
    ((Functor.whiskeringRight ℕᵒᵖ _ _).obj
      (proEtaleRingRestrictScalars ((coefficientChange l E).map T)))
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj (Opposite.op n))).symm ≪≫
  Functor.mapDerivedCategoryCompIso
    ((CategoryTheory.evaluation ℕᵒᵖ _).obj (Opposite.op n))
    (proEtaleRingRestrictScalars ((coefficientChange l E).map T))

/-- The chosen uniformizer generates the coefficient ideal.
Source: blueprint prop-functor-package, coefficient convention
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the coefficient ideal is defined as the span of the singleton uniformizer;
the range of the constant function on Fin 1 is that same singleton. -/
theorem uniformizerGenerators :
    Ideal.span (Set.range (fun _ : Fin 1 ↦ pbcUniformizer l E)) =
      (pbcIntegralDatum l E).ideal := by
  sorry

/-- The recorded integral constructible object is complete in the canonical
completed-exchange coordinates; this is a conclusion, not an extra hypothesis.
Source: Bhatt--Scholze 6.5.1; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: sfIntegralConstructible includes its normalized reduction Roos triangle.
The projection-normalized coefficient isomorphism identifies this strict quotient
tower and its augmentation with those of pbcIntegralDatum. The DVR Koszul
reconstruction criterion identifies its invertible augmentation with intrinsic
completeness for the singleton uniformizer tuple. -/
theorem integralCompleteness (K : sfIntegralConstructibleCategory l E X) :
    cbcCompleteProperty (pbcIntegralDatum l E) X 1
      (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)
      ((restrict l E X).obj K.obj) := by
  sorry

/-- The same object in the complete subcategory, with its proved completeness only.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def completeObject (K : sfIntegralConstructibleCategory l E X) :
    (cbcCompleteProperty (pbcIntegralDatum l E) X 1
      (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)).FullSubcategory :=
  ⟨(restrict l E X).obj K.obj, integralCompleteness l E K⟩

/-- The identity-open slice object has the same structure map as its ambient object.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the commutativity condition of a is a.left followed by the identity equals
V.hom; the slice functor retains a.left. -/
theorem identitySliceCondition (T : Scheme.{u}) (V : T.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject (𝟙 T)) :
    (𝟙 V.left) ≫
        ((IntegralOpenReduction.sliceSite (𝟙 T)).obj (Over.mk a)).hom = V.hom := by
  sorry

/-- The literal identity arrow from the slice presentation back to V.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def identitySliceArrow (T : Scheme.{u}) (V : T.ProEt)
    (a : V ⟶ IntegralOpenReduction.openObject (𝟙 T)) :
    V ⟶ (IntegralOpenReduction.sliceSite (𝟙 T)).obj (Over.mk a) :=
  MorphismProperty.Over.homMk (𝟙 V.left) (identitySliceCondition T V a)

/-- The identity-open map on the supplied ordinary presentation is fixed on every
extension summand, so this existence theorem determines its data uniquely.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: identity-open localization has one extension summand. Send that summand to
the same section, using identitySliceArrow to identify its site object. These
maps and their inverse preserve restrictions and scalar actions; sheafification
extends them uniquely. The extension generators determine uniqueness. -/
theorem suppliedOpenId_existsUnique (T : Scheme.{u})
    (o : IntegralOpenReduction.Operations l E (𝟙 T)) :
    ∃! aX : IntegralOpenReduction.extension l E (𝟙 T) o ≅ 𝟭 _,
      ∀ (M : scalarReductionSource l E T) (V : T.ProEt)
        (a : V ⟶ IntegralOpenReduction.openObject (𝟙 T))
        (x : M.val.obj (Opposite.op
          ((IntegralOpenReduction.sliceSite (𝟙 T)).obj (Over.mk a)))),
        (aX.hom.app M).val.app (Opposite.op V)
            (IntegralOpenReduction.extensionSection l E (𝟙 T) o M V a x) =
          M.val.map (identitySliceArrow T V a).op x := by
  sorry

/-- The specified degreewise a_X, localized to the supplied open presentation.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def suppliedOpenId (T : Scheme.{u})
    (o : IntegralOpenReduction.Operations l E (𝟙 T)) :
    IntegralOpenReduction.shriek l E (𝟙 T) o ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    (suppliedOpenId_existsUnique l E T o).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The finite identity-open map is fixed on all extension generators.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the identity open has exactly its identity lift on each test object. Send
each extension generator to the same section. Sheafification extends this map;
the inverse inserts that generator. Generators also prove uniqueness. -/
theorem suppliedFiniteOpenId_existsUnique (T : Scheme.{u})
    (o : IntegralOpenReduction.Operations l E (𝟙 T)) (n : ℕ) :
    ∃! aX : IntegralOpenReduction.finiteExtension l E (𝟙 T) o n ≅ 𝟭 _,
      ∀ (M : normalizedDVRModules l E T n) (V : T.ProEt)
        (a : V ⟶ IntegralOpenReduction.openObject (𝟙 T))
        (x : M.val.obj (Opposite.op
          ((IntegralOpenReduction.sliceSite (𝟙 T)).obj (Over.mk a)))),
        (aX.hom.app M).val.app (Opposite.op V)
            (IntegralOpenReduction.finiteExtensionSection l E (𝟙 T) o n M V a x) =
          M.val.map (identitySliceArrow T V a).op x := by
  sorry

/-- The same degreewise a_X at the finite coefficient level.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def suppliedFiniteOpenId (T : Scheme.{u})
    (o : IntegralOpenReduction.Operations l E (𝟙 T)) (n : ℕ) :
    compactSupportCanonicalJLevel l E (𝟙 T) o n ≅ 𝟭 _ :=
  Functor.mapDerivedCategoryNatIso
    (suppliedFiniteOpenId_existsUnique l E T o n).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The finite restriction square uses the projection-normalized coefficient maps.
Source: Bhatt--Scholze 6.5.1; Stacks 03DA
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def finiteRestrictionSquare (T : Scheme.{u}) (n : ℕ) :
    pbcDerivedRestrict (ImmersionCompletedPullback.finiteRingIso l E T n).hom ⋙
        pbcDerivedRestrict ((pbcIntegralDatum l E).projection T n) ≅
      coefficientFiniteDerivedRestriction l E T n ⋙ restrict l E T :=
  pbcDerivedRestrictComp ((pbcIntegralDatum l E).projection T n)
      (ImmersionCompletedPullback.finiteRingIso l E T n).hom
      (((coefficientChange l E).map T) ≫
        completedIntegralCommRingProjectionUnrestricted l E T n)
      ((ImmersionCompletedPullback.completedRingIso_exists l E T).exists.choose_spec n).symm ≪≫
    (pbcDerivedRestrictComp ((coefficientChange l E).map T)
      (completedIntegralCommRingProjectionUnrestricted l E T n)
      (((coefficientChange l E).map T) ≫
        completedIntegralCommRingProjectionUnrestricted l E T n) rfl).symm

/-- The finite reduction coordinate change is fixed by the actual tensor units.
Source: Stacks 06YY; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: take the adjoint mate of finiteRestrictionSquare. Both coefficient maps
are isomorphisms, so restriction along them is an equivalence. The mate is an
isomorphism, and the adjunction Hom bijection fixes it uniquely by this unit equation. -/
theorem reductionCoordinates_existsUnique (T : Scheme.{u}) (n : ℕ) :
    ∃! e : restrict l E T ⋙ (pbcIntegralDatum l E).reduction T n ≅
        coefficientFiniteDerivedExtension l E T n ⋙
          pbcDerivedRestrict (ImmersionCompletedPullback.finiteRingIso l E T n).hom,
      ∀ K : DerivedCategory (scalarReductionSource l E T),
        (pbcDerivedScalarAdjunction ((pbcIntegralDatum l E).projection T n)).unit.app
            ((restrict l E T).obj K) ≫
          (pbcDerivedRestrict ((pbcIntegralDatum l E).projection T n)).map (e.hom.app K) ≫
          (finiteRestrictionSquare l E T n).hom.app
            ((coefficientFiniteDerivedExtension l E T n).obj K) =
        (restrict l E T).map ((coefficientFiniteAdjunction l E T n).unit.app K) := by
  sorry

/-- The unique quotient-adjunction coordinate change.
Source: Stacks 06YY; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def reductionCoordinates (T : Scheme.{u}) (n : ℕ) :=
  (reductionCoordinates_existsUnique l E T n).exists.choose

/-- The finite coefficient square is fixed by inverse image of constant sections.
Source: Stacks 03D1; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the coefficient maps agree on constant quotient representatives. Their
sheafifications therefore agree, giving precisely the displayed square. -/
theorem finiteCoefficientSquare (n : ℕ) :
    ((pbcIntegralDatum l E).finiteRingIso f n).hom ≫
        (ImmersionCompletedPullback.finiteRingIso l E X n).hom =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (ImmersionCompletedPullback.finiteRingIso l E Y n).hom ≫
        (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (n+1))).hom := by
  sorry

/-- The supplied finite pushforward is the same sectionwise module direct image.
Source: Stacks 03D1, 0D6E; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: the ring direct-image map is the transpose of the constant-section
inverse-image map. The adjunction triangle identifies this transpose with the
constant-section direct-image map used by compactSupportLevelDirectImage.
Substitution in SheafOfModules.pushforward gives equality. -/
theorem suppliedFinitePush_eq (n : ℕ) :
    proEtaleRingModuleDirectImage f
        (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n+1)))
        (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n+1)))
        (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (n+1))) =
      compactSupportLevelDirectImage l E f n := by
  sorry

/-- Ordinary finite direct image, in the two fixed coefficient presentations.
Source: Stacks 0D6E; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def ordinaryLevelCoordinates [di : CompactSupportProperImageTower.DirectData l E f]
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (reductionDerivedRestrict Y ((pbcIntegralDatum l E).projection Y n)).obj
        (((pbcIntegralDatum l E).finitePush f n).obj
          (((pbcIntegralDatum l E).reduction X n).obj ((restrict l E X).obj K))) ≅
      (restrict l E Y).obj ((coefficientFiniteDerivedRestriction l E Y n).obj
        ((compactSupportLevelDirectImage l E f n).rightDerivedFunctor.obj
          ((coefficientFiniteDerivedExtension l E X n).obj K))) := by
  letI : (proEtaleRingModuleDirectImage f
      (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n+1)))
      (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n+1)))
      (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (n+1)))).Additive :=
    (suppliedFinitePush_eq l E f n).symm ▸
      inferInstanceAs (compactSupportLevelDirectImage l E f n).Additive
  exact
    (pbcDerivedRestrict ((pbcIntegralDatum l E).projection Y n)).mapIso
      (((pbcIntegralDatum l E).finitePush f n).mapIso
        ((reductionCoordinates l E X n).app K) ≪≫
        (proEtaleRingRestrictionDerivedDirectImage f
          ((pbcIntegralDatum l E).finiteRing Y n)
          (proEtaleConstantRing Y (Padic.coefficientExtensionRing l E (n+1)))
          ((pbcIntegralDatum l E).finiteRing X n)
          (proEtaleConstantRing X (Padic.coefficientExtensionRing l E (n+1)))
          (ImmersionCompletedPullback.finiteRingIso l E Y n).hom
          (ImmersionCompletedPullback.finiteRingIso l E X n).hom
          ((pbcIntegralDatum l E).finiteRingIso f n)
          (proEtaleConstantRingComparison f (Padic.coefficientExtensionRing l E (n+1)))
          (finiteCoefficientSquare l E f n)).symm.app
            ((coefficientFiniteDerivedExtension l E X n).obj K)) ≪≫
    (pbcDerivedRestrict ((pbcIntegralDatum l E).projection Y n)).mapIso
      ((pbcDerivedRestrict (ImmersionCompletedPullback.finiteRingIso l E Y n).hom).mapIso
        ((Functor.rightDerivedFunctorNatIso
          (G := compactSupportLevelDirectImage l E f n)
          (eqToIso (suppliedFinitePush_eq l E f n))).app
            ((coefficientFiniteDerivedExtension l E X n).obj K))) ≪≫
    (finiteRestrictionSquare l E Y n).app
      ((compactSupportLevelDirectImage l E f n).rightDerivedFunctor.obj
        ((coefficientFiniteDerivedExtension l E X n).obj K))

/-- The recorded integral domain supplies completeness for the cited open comparison.
Source: Bhatt--Scholze 3.5.2, 6.5.1
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: both predicates use the same scalar-reduction units and quotient Roos
triangle. Reindex their positive exponents by n+1. -/
theorem suppliedCompleteness (K : sfIntegralConstructibleCategory l E X) :
    IntegralOpenReduction.complete l E X K.obj := by
  sorry

/-- The original finite identity-open identification in the recorded support coordinates.
Source: Stacks 03DI; blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange). -/
def recordedFiniteProper [di : CompactSupportProperImageTower.DirectData l E f] (n : ℕ) :
    sfIntrinsicCompactSupport (Compactification.ofIsProper f)
        (Padic.coefficientExtensionRing l E (n+1)) ≅
      (compactSupportLevelDirectImage l E f n).rightDerivedFunctor :=
  Functor.isoWhiskerRight
    (Functor.mapDerivedCategoryNatIso
        (sfIntrinsicOpenId (Padic.coefficientExtensionRing l E (n+1)) X) ≪≫
      Functor.mapDerivedCategoryIdIso _) _ ≪≫ Functor.leftUnitor _

/-- The recorded integral action reconstructs the ordinary direct image from the
actual strict tower and all its projections, with the degreewise proper normalization.
Source: blueprint prop-functor-package, clause (3); Stacks 0A07, 0D6E
(blueprint: lem-sf-compactified-proper-tower-exchange).

Proof: the coefficient isomorphism identifies the published completed module
categories and their finite reductions. The uniform interval and constructibility
in sfIntegralConstructible imply completeness; it is preserved by this equivalence.
At identity open, apply compactSupportProperImageTower and the normalized
compactification realization to the actual quotient tower. Under a_X its strict
transitions are ordinary direct image of the quotient maps followed by the
canonical scalar restriction comparison. Thus there is one isomorphism in the
derived category of strict towers, not merely isomorphisms of evaluations.
Apply total limit and the direct-image reconstruction, whose augmentation is
Rf_* of the completion unit. Its finite projections are the specified finite
proper maps. The realization equation identifies the resulting integral map
with integralProper. Naturality of derived projections gives every displayed
projection identity. This argument includes K=0, n=0 (exponent one), f=id and
the empty scheme; no common Tor bound is added. -/
def IntegralNormalizationSpec (K : sfIntegralConstructibleCategory l E X)
    (_origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum l E)
      ((restrict l E X).obj K.obj)) : Prop :=
    IsIso (ordinaryReconstruction (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)) ∧
    ∃ (o : IntegralOpenReduction.Operations l E (𝟙 X))
      (SX : CoefficientDerivedSystemCalculus l E X)
      (SV : CoefficientDerivedSystemCalculus l E X)
      (tensor : IntegralOpenReduction.TensorComparison l E (𝟙 X) o)
      (r : IntegralOpenReduction.Comparison l E (𝟙 X) o SV SX tensor)
      (di : CompactSupportProperImageTower.DirectData l E f)
      (δ : ((sfCompactSupportFiniteIntegralFunctor l D.k
          (coefficientPrimeUnit l D hl) (Compactification.ofIsProper f) E).obj K).obj ≅
        (coefficientConstantTowerLimit l E Y).obj
          ((CompactificationCompletedRealization.supportTower l E
            (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj))
      (θ : (towerRestriction l E Y).obj
        ((CompactificationCompletedRealization.supportTower l E
          (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj) ≅
        supportTower (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj))
      (γ : (towerRestriction l E Y).obj
        ((CompactificationCompletedRealization.supportTower l E
          (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj) ≅
        ordinaryTower (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)),
      γ = θ ≪≫ strictId (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) ∧
      (∀ n : ℕ,
        (pbcTowerEvaluation Y ((pbcIntegralDatum l E).completedRing Y) n).map θ.hom ≫
            sourceEvaluation (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n ≫
            (reductionDerivedRestrict Y ((pbcIntegralDatum l E).projection Y n)).map
              (finiteProper (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n).hom ≫
            (ordinaryLevelCoordinates l E f (di := di) K.obj n).hom =
          (towerRestrictionEvaluation l E Y n).hom.app
              ((CompactificationCompletedRealization.supportTower l E
                (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj
                  K.obj) ≫
          (restrict l E Y).map
            ((CompactificationCompletedRealization.supportEvaluation l E
                (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl) n).hom.app
                  K.obj ≫
              (coefficientFiniteDerivedRestriction l E Y n).map
                ((recordedFiniteProper l E f (di := di) n).hom.app
                    ((coefficientFiniteDerivedExtension l E X n).obj K.obj) ≫
                  (compactSupportLevelDirectImage l E f n).rightDerivedFunctor.map
                    ((suppliedFiniteOpenId l E X o n).inv.app
                      ((coefficientFiniteDerivedExtension l E X n).obj K.obj))) ≫
              (CompactSupportProperImageTower.beta l E (𝟙 X) f o
                (d := di) SV SX tensor r ⟨K.obj, suppliedCompleteness l E K⟩ n).inv ≫
              (coefficientFiniteDerivedRestriction l E Y n).map
                ((compactSupportLevelDirectImage l E f n).rightDerivedFunctor.map
                  ((coefficientFiniteDerivedExtension l E X n).map
                    ((suppliedOpenId l E X o).hom.app K.obj))))) ∧
      (restrict l E Y).map (integralProper l E D hl f K).hom ≫
          (pushComparison l E f).inv.app K.obj ≫
          ordinaryReconstruction (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) =
        (restrict l E Y).map δ.hom ≫
          (cbcRealizationLimitMap
            (proEtaleRingRestrictScalars ((coefficientChange l E).map Y))).app
              ((CompactificationCompletedRealization.supportTower l E
                (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj) ≫
          (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map γ.hom ∧
      (∀ n : ℕ,
        (restrict l E Y).map (integralProper l E D hl f K).hom ≫
            (pushComparison l E f).inv.app K.obj ≫
            ordinaryReconstruction (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) ≫
            (completedRlimProjection Y ((pbcIntegralDatum l E).completedRing Y) n).app
              (ordinaryTower (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)) ≫
            (pbcIntegralDatum l E).towerPushReductionEvaluation f
              ((restrict l E X).obj K.obj) n =
          (restrict l E Y).map δ.hom ≫
            (cbcRealizationLimitMap
              (proEtaleRingRestrictScalars ((coefficientChange l E).map Y))).app
                ((CompactificationCompletedRealization.supportTower l E
                  (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj
                    K.obj) ≫
            (completedRlimProjection Y ((pbcIntegralDatum l E).completedRing Y) n).app
              ((towerRestriction l E Y).obj
                ((CompactificationCompletedRealization.supportTower l E
                  (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj
                    K.obj)) ≫
            (pbcTowerEvaluation Y ((pbcIntegralDatum l E).completedRing Y) n).map θ.hom ≫
            sourceEvaluation (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n ≫
            (reductionDerivedRestrict Y ((pbcIntegralDatum l E).projection Y n)).map
              (finiteProper (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n).hom) ∧
      (∀ n : ℕ,
        δ.hom ≫ (coefficientConstantTowerProjection l E Y n).app
            ((CompactificationCompletedRealization.supportTower l E
              (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj) ≫
            (CompactificationCompletedRealization.supportEvaluation l E
              (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl) n).hom.app
                K.obj =
          (coefficientFiniteAdjunction l E Y n).unit.app
              ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
                (Compactification.ofIsProper f) E).obj K).obj ≫
            (scalarReductionDerivedRestriction l E Y n).map
              (sfCompactSupportFiniteReductionIso l D.k (coefficientPrimeUnit l D hl)
                (Compactification.ofIsProper f) E K n).hom) ∧
      (∀ (m n : ℕ) (h : n ≤ m),
        (pbcTowerTransition Y ((pbcIntegralDatum l E).completedRing Y) m n h).app
            ((towerRestriction l E Y).obj
              ((CompactificationCompletedRealization.supportTower l E
                (Compactification.ofIsProper f) D.k (coefficientPrimeUnit l D hl)).obj K.obj)) ≫
            (pbcTowerEvaluation Y ((pbcIntegralDatum l E).completedRing Y) n).map γ.hom =
          (pbcTowerEvaluation Y ((pbcIntegralDatum l E).completedRing Y) m).map γ.hom ≫
            (pbcTowerTransition Y ((pbcIntegralDatum l E).completedRing Y) m n h).app
              (ordinaryTower (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)))

/-- The recorded integral tower satisfies the strict reconstruction specification.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: identify coefficient presentations by their finite projections; use the
strict open-reduction comparison at identity, then proper image and its canonical
limit comparison. The normalized compactification realization gives delta and
theta; gamma is theta followed by degreewise a_X. Naturality gives its transitions
and all finite projections. The completion unit is invertible since K is complete. -/
theorem integralNormalization (K : sfIntegralConstructibleCategory l E X)
    (origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum l E)
      ((restrict l E X).obj K.obj)) :
    IntegralNormalizationSpec l E D hl f K origins := by
  sorry

/-- Proper compact support, including its actual quotient tower, agrees with
ordinary direct image and its completed proper-base-change mate.
Source: blueprint prop-functor-package, clause (3)
(blueprint: lem-sf-compactified-proper-tower-exchange).
Proof: integralNormalization gives the strict identity-open realization and its
ordinary reconstruction. Strict reconstruction and finite normalization identify
every finite projection with Rf_{*,n}(a_X). IdentityExchange gives the completed
proper mate, since the open comparison is the identity on strict transitions.
RefinementIndependence identifies every common-refinement proper coincidence;
its finite normalization is the finite proper-coincidence coherence, and its
integral normalization follows by applying total limit and descending through
the constant-completion equivalence. This gives the assertion without discrete
non-torsion etale comparison and without any extra Tor assumption. -/
theorem compactifiedProperTowerExchange
    {X' Y' : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    [IsProper f'] (sp : ChosenCartesianSquare g' f' f g)
    (sj : OpenImmersionSquare g' (𝟙 X') (𝟙 X) g')
    (K : sfIntegralConstructibleCategory l E X)
    (origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum l E)
      ((restrict l E X).obj K.obj)) :
    IntegralNormalizationSpec l E D hl f K origins ∧
    (∀ n : ℕ,
      (pbcTowerTransition Y ((pbcIntegralDatum l E).completedRing Y)
          (n+1) n (Nat.le_succ n)).app
          (ordinaryTower (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)) ≫
          (pbcIntegralDatum l E).towerPushReductionEvaluation f
            ((restrict l E X).obj K.obj) n =
        (pbcIntegralDatum l E).towerPushReductionEvaluation f
            ((restrict l E X).obj K.obj) (n+1) ≫
          ordinaryFiniteTransition (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n) ∧
    (∀ n : ℕ,
      (pbcTowerEvaluation Y ((pbcIntegralDatum l E).completedRing Y) n).map
          (strictId (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)).hom ≫
          (pbcIntegralDatum l E).towerPushReductionEvaluation f
            ((restrict l E X).obj K.obj) n =
        sourceEvaluation (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n ≫
          (reductionDerivedRestrict Y ((pbcIntegralDatum l E).projection Y n)).map
            (finiteProper (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) n).hom) ∧
    ((cbcDatumCompletedExchange (pbcIntegralDatum l E) sj
          1 (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)).app
            (completeObject l E K) ≫
        (openId (pbcIntegralDatum l E) X').hom.app
          (((pbcIntegralDatum l E).completedPull g').obj ((restrict l E X).obj K.obj)) =
      ((pbcIntegralDatum l E).completedPull g').map
        ((openId (pbcIntegralDatum l E) X).hom.app ((restrict l E X).obj K.obj))) ∧
    ((cbcStrictExchange (pbcIntegralDatum l E) sj).hom.app
          ((completedReductionTower X (pbcIntegralDatum l E)).obj
            ((restrict l E X).obj K.obj)) ≫
        (openTowerId (pbcIntegralDatum l E) X').hom.app
          ((completedTowerPullback g' (pbcIntegralDatum l E)).obj
            ((completedReductionTower X (pbcIntegralDatum l E)).obj
              ((restrict l E X).obj K.obj))) =
      (completedTowerPullback g' (pbcIntegralDatum l E)).map
        ((openTowerId (pbcIntegralDatum l E) X).hom.app
          ((completedReductionTower X (pbcIntegralDatum l E)).obj
            ((restrict l E X).obj K.obj)))) ∧
    (completedCompactSupportExchange (pbcIntegralDatum l E)
        (Compactification.ofIsProper f) (Compactification.ofIsProper f') g' sp sj
        1 (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)
        (completeObject l E K) ≫
        (properId (pbcIntegralDatum l E) f'
          (((pbcIntegralDatum l E).completedPull g').obj ((restrict l E X).obj K.obj))).hom =
      ((pbcIntegralDatum l E).completedPull g).map
          (properId (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)).hom ≫
        (pbcIntegralDatum l E).completedExchange sp ((restrict l E X).obj K.obj)) ∧
    (∀ (c c₁ c₂ : Compactification f)
      (u₁ : c₁.Refinement c) (v₁ : c₁.Refinement (Compactification.ofIsProper f))
      (u₂ : c₂.Refinement c) (v₂ : c₂.Refinement (Compactification.ofIsProper f)),
      cbcCompactificationComparison (pbcIntegralDatum l E) u₁ v₁
          1 (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)
          (completeObject l E K) origins ≪≫
          properId (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj) =
        cbcCompactificationComparison (pbcIntegralDatum l E) u₂ v₂
          1 (fun _ : Fin 1 ↦ pbcUniformizer l E) (uniformizerGenerators l E)
          (completeObject l E K) origins ≪≫
          properId (pbcIntegralDatum l E) f ((restrict l E X).obj K.obj)) := by
  sorry

end IntegralNormalization
end AlgebraicGeometry.Scheme.CompactifiedProperTower
