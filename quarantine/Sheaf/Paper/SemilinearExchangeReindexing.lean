module

public import Sheaf.Paper.SemilinearExchangeDescentData
import Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent
import Sheaf.Paper.PurCompletedReductionReindexingLifted

/-! # Semilinear compact-support exchange is site reindexing

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility;
the extracted five-step DAG assembly
(blueprint: lem-pur-weil-semilinear-exchange-reindexing).

The finite and integral clauses use the specified proper mate followed by the
open comparison. Integral equations are retained before the derived inverse limit.
All isomorphisms below are isomorphisms of underlying schemes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
open WeilConjectures WeilConjectures.PurityFiniteSetting

namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard
  PurIntegralStrictMapNormalization PurIntegralStrictHorizontal PurIntegralStrictVertical
  PurIntegralStrictReduction PurIntegralCompletedCoherence
  FiniteExchangeCoherence.composition etaleOriginRealization
  Functor.mapDerivedCategory completedCompactSupportExchange
  PurCompletedReindexingAt PurCompletedReindexingSquare
  PurStrictIntegralGeometricNormalization PurIntegralSupportNormalization
  PurIntegralProperNormalization
  completedAdicChangeData
  CategoryTheory.Limits.limit AdicCoefficients.ringSystem
  cbcDerivedOpenShriek cbcDatumCompletedExchange cbcDatumOrdinaryExchange cbcBeta
  pbcIntegralDatum
  proEtaleRingModulePullback proEtaleRingModuleDirectImage Functor.rightDerivedFunctor

attribute [local instance 2000] reductionModulesHasDerivedCategory
  reductionTowerHasDerivedCategory

/-- Completed inverse image is the exact sectionwise reindexing equivalence,
with its quotient-projection unit and actual strict reduction tensor comparison.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearCompletedReindexing (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  ∀ (T' T : Scheme.{u}) [T.Over (Spec (.of P.field.k))]
      [IsSeparated (T ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
      [QuasiCompact (T ↘ Spec (.of P.field.k))] (g : T' ⟶ T) [IsIso g],
    PurReindexing.PurCompletedReindexingAt d g

/-- The finite coherence arrows are the actual supplied-domain exchanges,
with the canonical pullback square and the specified open comparison.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearFiniteAgreement (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}} [ X.Over (Spec (.of P.field.k))]
  [ Y.Over (Spec (.of P.field.k))]
  [ LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [ QuasiCompact (X ↘ Spec (.of P.field.k))]
  [ IsSeparated (X ↘ Spec (.of P.field.k))]
  [ LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [ QuasiCompact (Y ↘ Spec (.of P.field.k))]
  [ IsSeparated (Y ↘ Spec (.of P.field.k))]
{f : X ⟶ Y} [ f.IsOver (Spec (.of P.field.k))]
  [ IsSeparated f] [ LocallyOfFiniteType f] [ QuasiCompact f]
    {X' Y' : Scheme.{u}} {f' : X' ⟶ Y'}
    [X'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X' ↘ Spec (.of P.field.k))]
    [QuasiCompact (X' ↘ Spec (.of P.field.k))]
    [IsSeparated (X' ↘ Spec (.of P.field.k))]
    [Y'.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y' ↘ Spec (.of P.field.k))]
    [IsSeparated (Y' ↘ Spec (.of P.field.k))]
    (c : Compactification f) (c' : Compactification f')
    (g : Y' ⟶ Y) (x : X' ⟶ X) (z : c'.Z ⟶ c.Z) [IsIso g]
    (sp : IsPullback z c'.g c.g g) (sj : IsPullback x c'.i c.i z),
        ordinaryH P.Coefficient c c' g x z sp sj =
      finiteChosenExchange P.Coefficient c c' g x z sp sj

/-- The proper mate is the actual sectionwise reindexing comparison,
and the completed compact-support map itself is invertible on the supplied domain.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
@[irreducible] def PurSemilinearIntegralIsomorphism (P : PurityFiniteSetting.{u}) : Prop :=
  let d := pbcIntegralDatum P.coefficients.l P.extension
  ∀ {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
      [IsIso g] [IsIso g']
      (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z) [IsIso gb]
      (sp : ChosenCartesianSquare gb c'.g c.g g)
      (sj : OpenImmersionSquare g' c'.i c.i gb),
    PurReindexing.PurCompletedReindexingSquare d sp ∧
    ∀ (r : ℕ) (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
      (ha : Ideal.span (Set.range a) = d.ideal)
      (K : (cbcCompleteProperty d
        X r a ha).FullSubcategory),
      IsIso (completedCompactSupportExchange d
        c c' gb sp sj r a ha K)

/-- Cancellation of completion units transports invertibility of the ordinary
proper/open exchange to its normalized completed exchange. -/
private theorem completedExchange_isIso_of_normalization
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gb : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gb c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gb)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory)
    (hn : PurIntegralSupportNormalization d c c' gb sp sj r a ha K)
    (hm : IsIso (purReindexingDerivedMate d sp)) :
    IsIso (completedCompactSupportExchange d c c' gb sp sj r a ha K) := by
  unfold PurIntegralSupportNormalization at hn
  rcases hn with ⟨hproper, hunit, _, _, htotal⟩
  unfold PurIntegralProperNormalization at hproper
  let hu : IsIso (d.ordinaryToCompleted g ((cbcSupport d c).obj K.obj)) :=
    hproper.2.2.1
  have hordinaryTransformation :
      IsIso (AlgebraicGeometry.Scheme.purIntegralReindexingExchange d c c' gb sp sj) := by
    unfold AlgebraicGeometry.Scheme.purIntegralReindexingExchange
    refine IsIso.comp_isIso' ?_ ?_
    · exact @Functor.isIso_whiskerLeft _ _ _ _ _ _ (cbcJ d c.i) _ _
        (purReindexingDerivedMate d sp) hm
    · exact Functor.isIso_whiskerRight _ _
  have hordinary : IsIso ((AlgebraicGeometry.Scheme.purIntegralReindexingExchange
      d c c' gb sp sj).app K.obj) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ hordinaryTransformation K.obj
  have htarget := @Functor.map_isIso _ _ _ _ _ _ (cbcSupport d c')
    (d.ordinaryToCompleted g' K.obj) hunit
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ hu
    (IsIso.comp_isIso' hordinary htarget) htotal

/-- Semilinear compact-support exchange is precisely site reindexing, including
finite and strict integral coherence, coefficient transport and compactification descent.

Proof plan (the five DAG assembly steps):
1. Apply lem-pur-isomorphism-finite-mate-normalization over S = Y. Its proper
   counit equation identifies the first factor with the sectionwise reindexing
   mate; its open-unit transpose identifies beta. Substitute in Ex! = Rp!(beta) r.
2. Apply lem-pur-isomorphism-finite-exchange-coherence for identity, horizontal
   and vertical pasting, with canonical compositors and finite-Tor quotient inputs.
3. Apply lem-pur-isomorphism-completed-reduction-reindexing to g, g prime and
   g bar. Quotient projections identify completed pullback, actual strict tensor
   reduction, its transitions and both direct-image mates with exact reindexing.
4. Apply lem-pur-isomorphism-strict-integral-exchange-normalization to j! K.
   The equality v = r holds before Rlim; the specified H, H prime and
   direct-image/limit comparison reconstruct the ordered proper/open identity.
   Its strict identity, pasting and reduction equations give the integral laws.
5. Apply lem-pur-isomorphism-exchange-scalar-refinement-descent to these
   equations. Scalar localization carries each ordered integral path to its
   rational path. The canonical scalar comparisons and their cocycles give
   the same common-stage class at every overfield, including equal fields.
   Refinement intertwines the actual exchanges, so substitute their already
   proved reindexing identities and pass through a common refinement.
   Do the same for a compatible composition tower. All steps use underlying
   scheme isomorphisms, and impose no extra k-linearity on them.
Source: constituent-compatibility assembly of
prop-pur-weil-equivariance-compatibilities.proof.md
(blueprint: lem-pur-weil-semilinear-exchange-reindexing). -/
theorem semilinearExchangeReindexing (P : PurityFiniteSetting.{u}) :
    PurSemilinearFiniteNormalization P ∧
    PurSemilinearFiniteAgreement P ∧
    PurSemilinearFiniteIdentity P ∧
    PurSemilinearFiniteHorizontal P ∧
    PurSemilinearFiniteVertical P ∧
    PurSemilinearFiniteCompositionIsIso P ∧
    PurSemilinearFiniteCoefficient P ∧
    PurReindexing.PurStrictIntegralGeometricNormalization P ∧
    PurReindexing.PurIntegralStrictMapNormalization (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurReindexing.PurIntegralStrictHorizontal (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurReindexing.PurIntegralStrictVertical (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurReindexing.PurIntegralStrictReduction (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurReindexing.PurIntegralCompletedCoherence (pbcIntegralDatum P.coefficients.l P.extension)
      (Spec (.of P.field.k)) ∧
    PurSemilinearCompletedReindexing P ∧
    PurSemilinearIntegralIsomorphism P ∧
    PurSemilinearScalar P ∧
    PurSemilinearRefinement P ∧
    PurSemilinearFiniteCompactComparison P ∧
    PurSemilinearRational P ∧
    PurSemilinearRationalCoherence P ∧
    PurSemilinearCommonStage P := by
  have hfinite : PurSemilinearFiniteNormalization P := by
    unfold PurSemilinearFiniteNormalization
    exact isomorphismFiniteMateNormalization P
  have hagreement : PurSemilinearFiniteAgreement P := by
    unfold PurSemilinearFiniteAgreement
    exact FiniteExchangeCoherence.canonicalAgreement P
  have hid : PurSemilinearFiniteIdentity P := by
    unfold PurSemilinearFiniteIdentity
    exact FiniteExchangeCoherence.identity P
  have hhorizontal : PurSemilinearFiniteHorizontal P := by
    unfold PurSemilinearFiniteHorizontal
    exact FiniteExchangeCoherence.horizontal P
  have hvertical : PurSemilinearFiniteVertical P := by
    unfold PurSemilinearFiniteVertical
    exact FiniteExchangeCoherence.vertical P
  have hcomposition : PurSemilinearFiniteCompositionIsIso P := by
    unfold PurSemilinearFiniteCompositionIsIso
    exact ⟨@FiniteExchangeCoherence.compositionIsIso.{u} P⟩
  have hcoefficient : PurSemilinearFiniteCoefficient P := by
    unfold PurSemilinearFiniteCoefficient
    intro m hm h X X' Y Y' f f' _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _ c c' g x z _ sp sj K hK
    exact FiniteExchangeCoherence.coefficient P m hm h c c' g x z sp sj K hK
  have hnormalization := purStrictIntegralExchangeNormalization P
  have hintegral := hnormalization.1
  have hstrict := hnormalization.2.1
  have hstrictHorizontal := hnormalization.2.2.1
  have hstrictVertical := hnormalization.2.2.2.1
  have hstrictReduction := hnormalization.2.2.2.2.1
  have hcompletedCoherence := hnormalization.2.2.2.2.2
  have hred := purCompletedReductionReindexingLifted.{u} P.coefficients.l
    (P.extension : Type u)
  have hreindex := hred.1
  have hsquare := hred.2
  have hcompleted : PurSemilinearCompletedReindexing P := by
    unfold PurSemilinearCompletedReindexing
    dsimp only
    intro T' T _ _ _ _ g _
    exact hreindex T' T g (P.coefficientPrime_isUnit_stalk T (T ↘ Spec (.of P.field.k)))
  have hisomorphism : PurSemilinearIntegralIsomorphism P := by
    unfold PurSemilinearIntegralIsomorphism
    dsimp only
    intro X' X Y' Y f f' g g' _ _ _ _ _ _ _ _ _ _ _ _ _ _ c c' gb _ sp sj
    have hs := hsquare c'.Z c.Z Y' Y gb c'.g c.g g
      (P.coefficientPrime_isUnit_stalk Y (Y ↘ Spec (.of P.field.k))) sp
    refine ⟨hs, ?_⟩
    intro r a ha K
    have hn := (show PurStrictIntegralGeometricNormalization P from hintegral)
    unfold PurReindexing.PurStrictIntegralGeometricNormalization
      AlgebraicGeometry.Scheme.PurStrictIntegralGeometricNormalization at hn
    have hnK := hn c c' gb sp sj r a ha K
    unfold PurReindexing.PurCompletedReindexingSquare
      AlgebraicGeometry.Scheme.PurCompletedReindexingSquare at hs
    exact completedExchange_isIso_of_normalization
      (pbcIntegralDatum P.coefficients.l P.extension) c c' gb sp sj r a ha K hnK hs.2.2.1
  have hdescent := isomorphismExchangeScalarRefinementDescent P hfinite hid hhorizontal
    hvertical hcoefficient hintegral hstrict hstrictHorizontal hstrictVertical
    hstrictReduction hcompletedCoherence
  have hrational := hdescent.1
  have hscalar := hdescent.2.1
  have hcommon := hdescent.2.2.1
  have hrationalCoherence := hdescent.2.2.2.1
  have hrefinement := hdescent.2.2.2.2.1
  have hcompact := hdescent.2.2.2.2.2
  exact ⟨hfinite, hagreement, hid, hhorizontal, hvertical, hcomposition, hcoefficient,
    hintegral, hstrict, hstrictHorizontal, hstrictVertical, hstrictReduction,
    hcompletedCoherence, hcompleted, hisomorphism, hscalar, hrefinement, hcompact,
    hrational, hrationalCoherence, hcommon⟩

end WeilConjectures
