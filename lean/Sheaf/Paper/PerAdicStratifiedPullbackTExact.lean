/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.ContinuousRationalDerivedRealization
public import Sheaf.Paper.PerAdicCommonStageTruncations
public import Sheaf.Paper.ContinuousCoefficientSliceNormalization
public import Sheaf.CategoryTheory.Triangulated.CoefficientStageDescent
import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntegralUniformCoefficient
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.Paper.PbcRationalCategory
import Sheaf.Paper.LocalizedTStructure
public import Sheaf.Paper.IntrinsicQbarCategory
import Sheaf.Paper.PbcScalarExtension
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.Paper.PbcQbarStandardCohomology
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.Paper.RationalRealizationPullbackComparison
import Sheaf.Paper.CompletedPullbackTriangles
import Sheaf.Paper.IntegralStratumChartRestrictions
import Sheaf.Paper.CompletedPerfectScalarPullback
import Sheaf.AlgebraicGeometry.NoetherianStratumDetection
import Sheaf.Paper.IntegralTStructure
import Sheaf.CategoryTheory.SemilinearScalarLocalization
import Sheaf.Paper.PbcVerdierAxioms
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons

/-! # Stratified finite-free calculation for completed rational pullback

Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.6 and 6.8.8,
Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-per-adic-stratified-pullback-texact).

The assertions use the published strict completed pullback, raw rational stages,
continuous rational realization and pair category. The local calculation uses the
ambient module categories even on charts which are not Noetherian.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
attribute [-instance] CategoryTheory.StageSystem.PairCategory.preadditive

namespace AlgebraicGeometry.Scheme
namespace StratifiedAdicPullback

/-- Bundle the existing geometric hypotheses for the realization interface.
Source: BS 6.8.14 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def base (l : ℕ) (X : Scheme.{u}) [IsNoetherian X]
    [hd : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
    [hi : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))] : ContinuousRational.Base l :=
  { scheme := X, dimension := hd.out, prime_unit := hi.out }

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The canonical map of continuous rational coefficients on an arbitrary scheme morphism.
This is the existing continuous-function pullback, with the finite extension's norm.
Source: BS 6.8.1 and 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
def coefficient {X Y : Scheme.{u}} (g : Y ⟶ X) :
    (adicTowerInverseImage g).obj (rationalCoefficientSheaf l X E) ⟶
      rationalCoefficientSheaf l Y E :=
  letI := coefficientExtensionNormedField l E
  continuousCoefficientPullback (ULift.{u + 1} E) g

/-- The existing finite free continuous module, including rank zero.
Source: BS 6.8.3 (blueprint: lem-per-adic-stratified-pullback-texact). -/
abbrev free (X : Scheme.{u}) (r : ℕ) :=
  SheafOfModules.free (R := (adicLisseForget X).obj (rationalCoefficientSheaf l X E))
    (ULift.{u + 1} (Fin r))

/-- The balanced-tensor calculation on a trivializing chart. The ordinary isomorphism
is fixed on every scalar multiple of every basis section, and the derived identification
is its degree-zero image after the normalized universal computation counit.
Source: BS 6.8.15 (blueprint: lem-per-adic-stratified-pullback-texact). -/
structure FreeCalculation {X Y : Scheme.{u}} (g : Y ⟶ X) (r : ℕ) where
  [additive : (ContinuousRational.modulePull g (coefficient l E g)).Additive]
  ordinary : (ContinuousRational.modulePull g (coefficient l E g)).obj (free l E X r) ≅
    free l E Y r
  basis : ∀ (U : X.ProEt) (j : ULift.{u + 1} (Fin r))
    (a : (rationalCoefficientSheaf l Y E).obj.obj
      (op ((proEtaleBaseChange g).obj U))),
    ordinary.hom.val.app (op ((proEtaleBaseChange g).obj U))
      (a • ContinuousRational.moduleUnit g (coefficient l E g) (free l E X r) U
        ((SheafOfModules.freeSection (R := (adicLisseForget X).obj
          (rationalCoefficientSheaf l X E)) j).val (op U))) =
      a • @id ((free l E Y r).val.obj (op ((proEtaleBaseChange g).obj U)))
        ((SheafOfModules.freeSection (R := (adicLisseForget Y).obj
          (rationalCoefficientSheaf l Y E)) j).val (op ((proEtaleBaseChange g).obj U)))
  counit : DerivedCategory.Q ⋙ ContinuousRational.derivedPull g (coefficient l E g) ⟶
    (ContinuousRational.modulePull g (coefficient l E g)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q
  normalized : ContinuousRational.IsNormalizedPullCounit g (coefficient l E g) counit
  universal : (ContinuousRational.derivedPull g (coefficient l E g)).IsLeftDerivedFunctor
    counit (HomologicalComplex.quasiIso _ (.up ℤ))
  computes : IsIso (counit.app ((CochainComplex.singleFunctor _ 0).obj (free l E X r)))
  derived : (ContinuousRational.derivedPull g (coefficient l E g)).obj
      ((DerivedCategory.singleFunctor _ 0).obj (free l E X r)) ≅
    (DerivedCategory.singleFunctor _ 0).obj (free l E Y r)
  derived_formula : derived.hom =
    counit.app ((CochainComplex.singleFunctor _ 0).obj (free l E X r)) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (ContinuousRational.modulePull g (coefficient l E g)) (.up ℤ) 0).hom.app
            (free l E X r)) ≫
      (DerivedCategory.singleFunctor _ 0).map ordinary.hom

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]

set_option maxHeartbeats 800000 in
-- Nested inverse-image and completed coefficient transports need extra elaboration steps.
/-- The stratum and chart clauses, using J(K)=F[0] in place of choosing an inverse
object of an equivalence. Thus every permitted realization and every inverse representative
are included. The immersion and its fibre product may be empty; r may be zero.
Source: BS 6.8.2, 6.8.6, 6.8.8 and 6.8.15
(blueprint: lem-per-adic-stratified-pullback-texact). -/
def LocalCalculation (R : ContinuousRational.Family.{u} l) (g : Y ⟶ X) : Prop :=
  ∀ (F : pbcModules X (rationalCoefficientSheaf l X E))
    (K : PbcRationalCategory X (pbcIntegralDatum l E) (pbcUniformizer l E)),
    ContinuousRational.IsConstructible l E X (R.realization E (base l X)).encoding F →
    Nonempty ((R.realization E (base l X)).J.obj K ≅
      (DerivedCategory.singleFunctor _ 0).obj F) →
    ∀ (S : Scheme.{u}) (i : S ⟶ X) (_hi : IsImmersion i),
      ((ContinuousRational.modulePull i (coefficient l E i)).obj F).IsFiniteLocallyFree →
      ((ContinuousRational.derivedPull (pullback.fst g i)
          (coefficient l E (pullback.fst g i))).obj
        ((R.realization E (base l Y)).J.obj
          ((R.along E (X := base l Y) (Y := base l X) g).raw l E |>.obj K))).IsLE 0 ∧
      ((ContinuousRational.derivedPull (pullback.fst g i)
          (coefficient l E (pullback.fst g i))).obj
        ((R.realization E (base l Y)).J.obj
          ((R.along E (X := base l Y) (Y := base l X) g).raw l E |>.obj K))).IsGE 0 ∧
      ∀ (U : S.ProEt) (r : ℕ),
        Nonempty ((ContinuousRational.modulePull U.hom (coefficient l E U.hom)).obj
          ((ContinuousRational.modulePull i (coefficient l E i)).obj F) ≅ free l E U.left r) →
        Nonempty (FreeCalculation l E (pullback.fst U.hom (pullback.snd g i)) r) ∧
        Nonempty ((ContinuousRational.derivedPull
            (pullback.snd U.hom (pullback.snd g i) ≫ pullback.fst g i)
            (coefficient l E (pullback.snd U.hom (pullback.snd g i) ≫ pullback.fst g i))).obj
          ((R.realization E (base l Y)).J.obj
            ((R.along E (X := base l Y) (Y := base l X) g).raw l E |>.obj K)) ≅
          (DerivedCategory.singleFunctor _ 0).obj
            (free l E (pullback U.hom (pullback.snd g i)) r))


variable (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 800000 in
-- Checking compatibility of the stage and ambient presentations unfolds their transports.
/-- The global conclusions on the actual completed pullback and its stage family.
`Comparisons` includes t-exactness at every cutoff, exactness on the heart, the two
uniquely unit/counit-normalized truncation comparisons, and their cohomology composite.
The integral shift is the ambient completed-pullback shift. `FractionExtension.factor_shift`
pins each rational shift to its localization, and `common_shift` pins the common shift to
those stage shifts. The scalar square includes equal finite fields.
Source: BS 6.8.14--6.8.15 and BBD 1.3.3, 1.3.6, 1.3.17
(blueprint: lem-per-adic-stratified-pullback-texact). -/
structure GlobalCalculation
    (tX : (pbcScalarSystem l Ω X (Fact.out) (Fact.out)).AdicCommonStageTruncations)
    (tY : (pbcScalarSystem l Ω Y (Fact.out) (Fact.out)).AdicCommonStageTruncations)
    (g : Y ⟶ X) where
  standardX : ∀ (A : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
    (K : pbcStageCategory l Ω X A),
    ((tX.finite A).le n K ↔ ∃ M : pbcIntegralStage l Ω X A,
      (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω A)).le n M ∧
        Nonempty (K ≅ (pbcStageLocalization l Ω X A).obj M)) ∧
    ((tX.finite A).ge n K ↔ ∃ M : pbcIntegralStage l Ω X A,
      (pbcIntegralTStructure X l (pbcFiniteField.{u} l Ω A)).ge n M ∧
        Nonempty (K ≅ (pbcStageLocalization l Ω X A).obj M))
  standardY : ∀ (A : Padic.FiniteCoefficientFields l Ω) (n : ℤ)
    (K : pbcStageCategory l Ω Y A),
    ((tY.finite A).le n K ↔ ∃ M : pbcIntegralStage l Ω Y A,
      (pbcIntegralTStructure Y l (pbcFiniteField.{u} l Ω A)).le n M ∧
        Nonempty (K ≅ (pbcStageLocalization l Ω Y A).obj M)) ∧
    ((tY.finite A).ge n K ↔ ∃ M : pbcIntegralStage l Ω Y A,
      (pbcIntegralTStructure Y l (pbcFiniteField.{u} l Ω A)).ge n M ∧
        Nonempty (K ≅ (pbcStageLocalization l Ω Y A).obj M))
  integral : ∀ (A : Type u) [Field A] [Algebra ℚ_[l] A] [FiniteDimensional ℚ_[l] A]
    (K : PbcBoundedConstructibleComplete X (pbcIntegralDatum l A)),
    PbcIsBoundedConstructibleComplete Y (pbcIntegralDatum l A)
      ((pbcActualCompletedPull g (pbcIntegralDatum l A)).obj K.obj)
  [integralShift : ∀ A : Padic.FiniteCoefficientFields l Ω,
    (pbcConditionalIntegral (pbcStageDatum.{u} l Ω A)
      (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω A))
      (pbcQbarIntegralPull_mem l Ω g A)).CommShift ℤ]
  integral_shift : ∀ (A : Padic.FiniteCoefficientFields l Ω)
    (K : pbcIntegralStage l Ω X A) (n : ℤ),
    HEq ((ObjectProperty.ι (PbcIsBoundedConstructibleComplete Y
        (pbcStageDatum.{u} l Ω A))).map
      (((pbcConditionalIntegral (pbcStageDatum.{u} l Ω A)
        (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω A))
        (pbcQbarIntegralPull_mem l Ω g A)).commShiftIso n).hom.app K))
      (((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω A)).commShiftIso n).hom.app K.obj)
  [finiteShift : ∀ A : Padic.FiniteCoefficientFields l Ω,
    ((pbcQbarPullFamily l Ω g).Φ A).CommShift ℤ]
  [commonShift : (pbcQbarCompletedPull l Ω g).CommShift ℤ]
  finite_fraction : ∀ A : Padic.FiniteCoefficientFields l Ω,
    CoefficientStageDescent.FractionExtension
      (pbcConditionalIntegral (pbcStageDatum.{u} l Ω A)
        (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω A))
        (pbcQbarIntegralPull_mem l Ω g A))
      ((pbcQbarPullFamily l Ω g).Φ A)
  common_shift : ∀ (A : Padic.FiniteCoefficientFields l Ω)
    (K : pbcStageCategory l Ω X A) (n : ℤ),
    HEq (((pbcQbarCompletedPull l Ω g).commShiftIso n).hom.app
      (((pbcScalarSystem l Ω X (Fact.out) (Fact.out)).ι A).obj K))
      (((pbcScalarSystem l Ω Y (Fact.out) (Fact.out)).ι A).map
        ((((pbcQbarPullFamily l Ω g).Φ A).commShiftIso n).hom.app K))
  finite : ∀ A : Padic.FiniteCoefficientFields l Ω,
    CoefficientStageDescent.Comparisons
      (tX.finite A)
      (tY.finite A)
      ((pbcQbarPullFamily l Ω g).Φ A)
  common : CoefficientStageDescent.Comparisons
    tX.common tY.common (pbcQbarCompletedPull l Ω g)
  scalarX : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    CoefficientStageDescent.Comparisons
      (tX.finite A)
      (tX.finite B)
      ((pbcScalarSystem l Ω X (Fact.out) (Fact.out)).T h)
  scalarY : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    CoefficientStageDescent.Comparisons
      (tY.finite A)
      (tY.finite B)
      ((pbcScalarSystem l Ω Y (Fact.out) (Fact.out)).T h)
  scalar_square : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    CoefficientStageDescent.SquareCompatible (finite A) (finite B)
      (scalarX A B h) (scalarY A B h) ((pbcQbarPullFamily l Ω g).β h)
  scalar_shift : ∀ (A B : Padic.FiniteCoefficientFields l Ω) (h : A ≤ B),
    NatTrans.CommShift ((pbcQbarPullFamily l Ω g).β h).hom ℤ
  scalar_unit : ∀ (A : Padic.FiniteCoefficientFields l Ω) (K : pbcStageCategory l Ω X A),
    HEq (((pbcQbarPullFamily l Ω g).β (le_refl A)).hom.app K)
      (𝟙 (((pbcQbarPullFamily l Ω g).Φ A).obj K))
  finite_interval : ∀ (A : Padic.FiniteCoefficientFields l Ω) (a b : ℤ)
    (K : pbcStageCategory l Ω X A),
    (tX.finite A).ge a K →
    (tX.finite A).le b K →
    (tY.finite A).ge a
      (((pbcQbarPullFamily l Ω g).Φ A).obj K) ∧
    (tY.finite A).le b
      (((pbcQbarPullFamily l Ω g).Φ A).obj K)
  common_interval : ∀ (a b : ℤ) (K : pbcQbarCategory l Ω X),
    tX.common.ge a K → tX.common.le b K →
    tY.common.ge a ((pbcQbarCompletedPull l Ω g).obj K) ∧
      tY.common.le b ((pbcQbarCompletedPull l Ω g).obj K)

end StratifiedAdicPullback

/-- Completed rational pullback is stratified finite free and standard t-exact.

Source: Bhatt--Scholze, Lemma 6.8.2, Definitions 6.8.6 and 6.8.8,
Proposition 6.8.14 and Remark 6.8.15
(blueprint: lem-per-adic-stratified-pullback-texact).

Proof (the nine steps of the node):

1. Both $X$ and $Y$ satisfy the noetherian and finite-dimensional hypotheses of the cited adic
results. Apply the finite-type noetherian theorem to their structure maps to
$\operatorname{Spec}k$ (a field is noetherian). Apply the finite-type fibre dimension bound to
the same maps: their unique fibres are $X$ and $Y$. The base is quasi-compact. Invertibility of
$\ell$ is inherited from $k$. No smoothness, flatness or assumption that $k$ is algebraically
closed is used.
Uses: lem-weil-pbc-finite-type-over-noetherian, lem-fin-finite-type-fibre-dimension-bound.

2. Write $\mathcal C_W=D^b_c(W,A_E)$ with exactly the compatible etale-origin witnesses in the
statement. The integral stratified-perfect characterization identifies this category with the
detailed integral category used by the chart lemmas, with the same completed ring and reduction
functors. The rational-realization pullback comparison states that ordinary ringed pullback
$P_g$ preserves $\mathcal C$ and that the specified quotient-tower unit
$\gamma_g:P_gK\to\widehat P_gK$ is invertible; it also retains the compatible etale witnesses.
Thus the actual completed pullback restricts to $\mathcal C_X\to\mathcal C_Y$. The completed-
pullback triangle theorem supplies its shift comparison and preservation of distinguished
triangles. These are inherited ambient triangles, not newly chosen triangles. The functor is
$A_E$-linear by the chart-restriction lemma (equivalently its scalar action on all quotient-
tower maps).
Uses: lem-weil-pbc-integral-stratified-perfect-characterization, lem-per-rational-realization-
pullback-comparison, lem-cbc-completed-pullback-triangles, lem-a1-integral-stratum-chart-
restrictions.

3. Fix integral $K$ with ambient cohomology supported in a finite interval $[a,b]$. The chart-
restriction lemma supplies a finite locally closed stratification $S_\alpha$ and pro-etale
covers $V_{\alpha t}\to S_\alpha$ on which $K$ is
$C_V(P)=B_{E,V}\otimes_{\underline{A_E}}\underline{P^\bullet}$ for bounded finite-projective
$A_E$-complexes $P^\bullet$. Its exact restriction assertion puts each such model in $[a,b]$.
Set $S'_\alpha=Y\times_XS_\alpha$, $V'_{\alpha t}=Y\times_XV_{\alpha t}$ and $g_{\alpha
t}:V'_{\alpha t}\to V_{\alpha t}$. The same lemma states that the nonempty $S'_\alpha$ stratify
$Y$, the $V'_{\alpha t}$ cover them pro-etale, and the restriction of $\widehat P_gK$ is the
specified completed pullback of this model along $g_{\alpha t}$. In particular we take fibre-
product strata, not a factorization deduced merely from inclusion of images.
Uses: lem-a1-integral-stratum-chart-restrictions.

4. Apply the completed perfect scalar-pullback calculation on every $g_{\alpha t}$. It gives
$Lg_{\alpha t}^*C_V(P)\cong C_{V'}(P)$, with the actual finite quotient projections and
transitions. Its cohomology and balanced-tensor assertions give $\mathcal H^jC_{V'}(P)\cong
g_{\alpha t}^*\mathcal H^jC_V(P)$ and therefore zero for $j\notin[a,b]$. The exact restrictions
in the previous step identify these sheaves with the restrictions of $\mathcal H^j(\widehat
P_gK)$. Apply noetherian stratum detection on $Y$ to each such abelian sheaf to obtain global
vanishing. Empty strata contribute nothing; if $K=0$ the additive functor sends it to zero,
covering an empty interval. Finally the integral standard t-structure is bounded and its halves
are defined by ambient vanishing: for an integral nonpositive object choose a bound $[a,0]$, and
for a nonnegative one choose $[0,b]$. The same argument proves preservation of both integral
halves. This checks the crucial hypothesis of coefficient-stage descent, without assuming
flatness of $g^{-1}B_{E,X}\to B_{E,Y}$.
Uses: lem-a1-completed-perfect-scalar-pullback, lem-weil-pbc-noetherian-stratum-detection,
lem-a1-integral-stratum-chart-restrictions, prop-weil-pbc-integral-tstructure.

5. Rationalize the $A_E$-linear exact functor using semilinear scalar localization with
$R=S=A_E$ and $t=u=\varpi_E$: on a fraction it is $f/\varpi_E^n\mapsto\widehat
P_g(f)/\varpi_E^n$. The localized t-structure has exactly the image halves required by descent.
The scalar-extension package gives the completed integral comparison $C_{L/E,Y}\widehat
P_{g,E}\cong\widehat P_{g,L}C_{L/E,X}$ and its identity, composition, coefficient-tower and
shift equations. Since Step 2 proved constructible preservation, these comparisons restrict
here, and semilinear localization preserves their equations. Thus they are the exact rational-
stage comparisons $\beta_{L/E}:T_{L/E,Y}F_E\cong F_LT_{L/E,X}$, with their stated unit and
associator normalizations.
Uses: lem-pur-semilinear-scalar-localization, prop-weil-localized-tstructure, prop-weil-pbc-
scalar-extension.

6. Apply coefficient-stage descent with integral categories $\mathcal C_X,\mathcal C_Y$ and
integral functors $\widehat P_{g,E}$ for every finite field $E$. Step 2 gives linear exactness,
Step 4 gives preservation of integral halves, and Step 5 gives the exact scalar comparisons. The
common-stage truncation theorem supplies t-exact transitions and the bounded common-stage
t-structures with finite-stage truncations; the scalar-extension package supplies exact
transition functors with literal identities and associators; the pair-category definition
supplies the same common-stage morphisms and cone triangles (a triangle is distinguished iff
isomorphic to the image of one finite-stage triangle), and the Verdier-axioms theorem proves
that these data form a triangulated category. These are precisely the remaining hypotheses of
descent. Consequently each rational $F_E$ and the functor $F_{\overline{\mathbf Q}_\ell}$ are
exact and t-exact. Explicitly the latter sends $(E,K)$ to $(E,F_EK)$ and sends a common-stage
arrow $u$ over $L$ to $\beta_{\mathrm{target}}^{-1}F_L(u)\beta_{\mathrm{source}}$. The unit and
tower equations proved in Step 5 make this independent of further enlargement, as asserted by
descent. This constructs the requested common-stage pullback, with its actual arrow action.
Uses: lem-a1-texact-coefficient-stage-descent, lem-per-adic-common-stage-truncations, def-weil-
pbc-qbar-category, prop-weil-pbc-scalar-extension, thm-weil-pbc-verdier-axioms.

7. For the additional finite-stage local formula, use $J$ to write the realized pullback of a
constructible module sheaf $F$ as $G_gF=E_Y\otimes^L_{g^{-1}E_X}g^{-1}F$. Let
$i:S\hookrightarrow X$ be the chosen stratum and $i':S'=Y\times_XS\hookrightarrow Y$. Their
coefficient maps are isomorphisms and their pullbacks are exact restrictions, by continuous
rational realization. Composition for ambient ringed derived pullbacks identifies $i'^*G_gF$
with $G_{g_S}i^*F$, since $g i'=i g_S$; the structural coefficient maps agree by the finite
quotient normalization. On a pro-etale chart $v:U\to S$, put $U'=S'\times_SU$. Slice
normalization identifies its restriction with $G_{g_U}(F|_U)$, where $g_U:U'\to U$. This uses
restriction for a site object, so imposes no noetherian hypothesis on $U$ or $U'$.
Uses: lem-per-continuous-rational-derived-realization, lem-sfb-ringed-derived-monoidal-
comparisons, lem-per-continuous-coefficient-slice-normalization.

8. On a chart trivializing $F|_S$ as $E_U^r$, the derived pullback unit $G_{g_U}(E_U)\cong
E_{U'}$ and additivity give $G_{g_U}(E_U^r)\cong E_{U'}^r[0]$. The balanced-tensor map is
$e'\otimes(e_1,\ldots,e_r)\mapsto(e'g_U^\sharp(e_1),\ldots,e'g_U^\sharp(e_r))$; its inverse
sends the $j$-th basis vector with coefficient $a$ to $a\otimes e_j$. These are inverse by the
balancing relation. For $r=0$ both sides are zero. Since pro-etale restriction is exact, all
nonzero-degree cohomology sheaves restrict to zero on this cover and hence are zero;
alternatively apply stratum detection to the one-stratum scheme $S'$ with these charts. Thus the
restriction to $S'$ is concentrated in degree zero, with exactly the asserted continuous finite
free chart model. For empty $S'$ this assertion is vacuous. The calculation uses only the
derived pullback unit, not flatness of its coefficient map.
Uses: lem-sfb-ringed-derived-monoidal-comparisons, lem-per-continuous-coefficient-slice-
normalization, lem-weil-pbc-noetherian-stratum-detection.

9. The descent theorem gives exactness on both hearts and the canonical truncation comparisons
$\alpha^-:F\tau^{\le m}\cong\tau^{\le m}F$ and $\alpha^+:F\tau^{\ge m}\cong\tau^{\ge m}F$,
characterized by their counit and unit equations. It also gives $F\mathcal H^j\cong\mathcal
H^jF$ and compatibility with every $\beta_{L/E}$. On a heart object define
$g^*=F|_{\mathrm{heart}}$; invert this cohomology comparison to get $\mathcal H^j(Lg^*K)\cong
g^*\mathcal H^j(K)$ in the direction in the statement. Preservation of every interval is just
preservation of the intersection $D^{\ge a}\cap D^{\le b}$, using t-exactness and the shift
comparisons; an empty interval contains only zero. These conclusions hold at each finite stage
and on the common-stage category by the same theorem.
Uses: lem-a1-texact-coefficient-stage-descent.
-/
theorem perAdicStratifiedPullbackTExact
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k))]
    (_hl : IsUnit (l : k)) (g : Y ⟶ X) :
    ∃ _nX : IsNoetherian X, ∃ _nY : IsNoetherian Y,
    ∃ _dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)),
    ∃ _dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞)),
    ∃ _iX : Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x)),
    ∃ _iY : Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y)),
      ∃ tX : (pbcScalarSystem l Ω X (Fact.out) (Fact.out)).AdicCommonStageTruncations,
      ∃ tY : (pbcScalarSystem l Ω Y (Fact.out) (Fact.out)).AdicCommonStageTruncations,
      tX.common = pbcQbarStandardT l Ω X ∧
      tY.common = pbcQbarStandardT l Ω Y ∧
      Nonempty (StratifiedAdicPullback.GlobalCalculation l Ω tX tY g) ∧
      ∀ (R : ContinuousRational.Family.{u} l) (E : Type u) [Field E]
        [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        StratifiedAdicPullback.LocalCalculation l E R g := by
  sorry

end AlgebraicGeometry.Scheme
