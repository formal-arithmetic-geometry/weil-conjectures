/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.CompletedCoefficientPresentationTransport
public import Sheaf.Paper.QbarCompactSupportBaseChange
import Sheaf.AlgebraicGeometry.GeometricFiberFinite
import WeilConjectures.Compactification.BaseChange
import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.QcqsCompactSupportRealization
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PbcQbarCompletedPullback
import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
import Sheaf.AlgebraicGeometry.PointedEtaleStalk
import Sheaf.Paper.PbcQbarCategory
import Sheaf.Paper.PbcRationalCategory
public import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.CompletedOpenExchangeTransport
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.Paper.SfCbcExtensionZeroCompletion
import Sheaf.Paper.ProEtaleConstructibleOrigin
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.Paper.PbcDescentFunctors
import Sheaf.Paper.CompletedDirectImageLimits
import Sheaf.Paper.PbcRationalTransport
import Sheaf.Paper.CompleteCompactSupportProetale
import Sheaf.Paper.FiniteExtensionCompactSupportBaseChange
import Sheaf.Paper.GlobalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange
import Sheaf.Paper.IntrinsicQbarCategory

/-!
# The geometric fibre of compactly supported direct image

Source: main-20261015, sec-smooth-purity/sk-prop-an/lem-pur-cfiber-stalk.md
and its proof (blueprint: lem-pur-cfiber-stalk).

The stalk and compactly supported fibre cohomology are presented on Spec Omega:
the source is pullback to that geometric point, and the target is compact support
for the fibre projection. This is the reading fixed in Step 1 of the DAG proof.
At finite coefficients the intrinsic constant-ring realization is undone before
applying the published exchange. At integral coefficients the projection-normalized
coefficient transport is used. Rationalization applies the actual localization
functor to that arrow. The algebraically closed clause uses the normalized
common-stage exchange model, whose existence is part of the conclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.PurityFiniteSetting

/-- The proper Cartesian square of the base-changed compactification, with its literal
pullback identification. Source: lem-pur-cfiber-stalk.proof.md, Step 1
(blueprint: lem-pur-cfiber-stalk). -/
def compactFiberProperSquare {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : S ⟶ Y) :
    ChosenCartesianSquare (pullback.fst c.g s) (c.baseChange s).g c.g s where
  w := pullback.condition
  isoPullback := Iso.refl _
  hom_fst := Category.id_comp _
  hom_snd := Category.id_comp _

/-- The open Cartesian square of the same base-changed compactification. The
identification is the universal one from the recorded open pullback square.
Source: lem-pur-cfiber-stalk.proof.md, Step 1 (blueprint: lem-pur-cfiber-stalk). -/
def compactFiberOpenSquare {X Y S : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (s : S ⟶ Y) :
    OpenImmersionSquare (pullback.fst f s) (c.baseChange s).i c.i (pullback.fst c.g s) where
  w := (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f s)).w
  isoPullback := (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f s)).isoPullback
  hom_fst := (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f s)).isoPullback_hom_fst
  hom_snd := (c.isPullback_i_ofIsPullback (IsPullback.of_hasPullback f s)).isoPullback_hom_snd
  isOpenImmersion := c.isOpenImmersion
  isOpenImmersion' := (c.baseChange s).isOpenImmersion

variable (P : PurityFiniteSetting.{u})
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
  [hXqc : QuasiCompact (X ↘ Spec (.of P.field.k))]
  [hYft : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
  [hYqc : QuasiCompact (Y ↘ Spec (.of P.field.k))]
  (f : X ⟶ Y) [hfOver : f.IsOver (Spec (.of P.field.k))]
  [hfSep : IsSeparated f] [hfft : LocallyOfFiniteType f] [hfqc : QuasiCompact f]
  (Omega : Type u) [Field Omega] [IsAlgClosed Omega]
  (s : Spec (.of Omega) ⟶ Y)

/-- The finite-coefficient canonical comparison, in fixed-scalar coordinates of the
recorded intrinsic category. It is the proper exchange followed by the inverse open
base-change comparison, evaluated on the literal geometric fibre square.
Source: lem-pur-cfiber-stalk.proof.md, Steps 1--2 (blueprint: lem-pur-cfiber-stalk). -/
def compactFiberFiniteMap (c : Compactification f)
    (K : proEtaleDerivedCategory X P.Ring) :=
  letI : Finite P.Ring :=
    Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos
  (ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (ModuleCat.{u + 1} P.Coefficient) (IsPullback.of_hasPullback f s) c).app
      ((sfIntrinsicDerivedEquivalence X P.Ring).inverse.obj K)

include hXft hXqc hYft hYqc hfOver hfSep hfft hfqc in
/-- The finite-level stalk formula for every bounded constructible finite-Tor input.
The quantification over compactifications is presentation independence, not an
additional compactifiability assumption.
Source: main-20261015, lem-pur-cfiber-stalk.md (blueprint: lem-pur-cfiber-stalk).

Proof: Step 1 forms X_s = X times_Y Spec Omega and the base-changed compactification.
The stalk of Rf! is its pullback to Spec Omega; on an etale-origin witness, sections
on Spec Omega compute this stalk by the inverse-image germ comparison and the final
identity pointed neighbourhood (def-weil-pbc-geometric-stalks and
lem-weil-pbc-inverse-image-stalk-germ). Compactly supported fibre cohomology is Rf_s!
of the restricted input. Step 2 uses lem-sf-proetale-constructible-origin to obtain
an etale-origin witness from intrinsic constructibility, after the canonical scalar
realization. Apply thm-cbc-finite-level-proetale to that witness. Its proper factor
is cor-weil-pbc-geometric-fiber-finite and its open factor is extension-by-zero base
change. Step 5 identifies the resulting map with compactFiberFiniteMap, since all
factors are the canonical exchanges. Empty fibres and the zero input give zero;
the identity map and the identity geometric-point square give the identity. -/
theorem compactFiber_finite
    (K : finiteTorConstructibleCategory P.coefficients.l P.extension P.level P.level_pos X) :
    ∀ c : Compactification f, IsIso (compactFiberFiniteMap P f Omega s c K.obj) := by
  sorry

include hXft hXqc hYft hYqc hfOver hfSep hfft hfqc in
/-- The integral formula uses the original finite-Tor category and the recorded
projection-normalized completed coefficient transport. Completeness is asserted,
not assumed, for every generating tuple of the uniformizer ideal.
Source: main-20261015, lem-pur-cfiber-stalk.md (blueprint: lem-pur-cfiber-stalk).

Proof: Step 3 identifies the detailed integral category with the bounded constructible
complete category by lem-weil-pbc-integral-stratified-perfect-characterization.
Its transport is integralDetailedTransport, fixed on every finite projection.
The finite-type schemes are Noetherian and finite-dimensional, and ell is invertible.
Their opens are quasi-compact. Apply thm-cbc-complete-proetale with the uniformizer
ideal, using the compatible etale-origin reductions supplied by the category.
The completed pullback is the same derived limit of finite pullbacks as the chapter's
integral pullback. By lem-cbc-completed-extension-zero-comparison, extension by zero
of the input is complete. The constant-completion equivalence and
lem-sf-cbc-extension-zero-completion give its normalized limit presentation;
prop-weil-pbc-direct-image-limits commutes proper image with that limit. Thus the
source and target identify with the recorded integral compact-support operations.
Reading the result on Spec Omega gives the stalk formula of Step 1. Step 5 keeps
the actual canonical map. This also covers an empty fibre and the zero input. -/
theorem compactFiber_integral
    (K : finiteTorConstructibleIntegralCategory P.coefficients.l P.extension X) :
    ∀ (c : Compactification f) (r : ℕ)
        (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
        (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal),
      ∃ hc : cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a ha
          ((integralDetailedTransport X P.coefficients.l P.extension).obj K.obj),
        IsIso (completedCompactSupportExchange (pbcIntegralDatum P.coefficients.l P.extension)
          c (c.baseChange s) (pullback.fst c.g s)
          (compactFiberProperSquare c s) (compactFiberOpenSquare c s) r a ha
          ⟨(integralDetailedTransport X P.coefficients.l P.extension).obj K.obj, hc⟩) := by
  sorry

include hXft hXqc hYft hYqc hfOver hfSep hfft hfqc in
/-- Rational stalk formula on the unchanged integral objects of the actual raw
rationalization. The arrow is localization of the canonical completed exchange.
Localization of the ambient completed category has the same Hom tensor products
between these objects as the full constructible rational category.
Source: main-20261015, lem-pur-cfiber-stalk.md (blueprint: lem-pur-cfiber-stalk).

Proof: Step 4 identifies the two integral presentations by the projection-normalized
coefficient transport. Their raw rationalizations have the same integral objects and
Hom tensor E, with no added idempotents. The uniqueness in prop-weil-pbc-rational-transport
identifies the rational operations and exchange with the scalar extensions of Step 3,
as in thm-cbc-finite-extension. Every rational object has its recorded integral
representative. Apply the integral exchange to it (integral constructibility provides
the uniform Tor bound), then apply localization. A functor sends the inverse to the
inverse, so the displayed actual localized arrow is invertible. Step 1 reads its ends
as the rational stalk and compactly supported fibre cohomology; Step 5 gives the
canonical comparison, also for zero objects and empty fibres. -/
theorem compactFiber_rational
    (K : sfRationalConstructibleCategory P.coefficients.l P.extension X) :
    ∀ (c : Compactification f) (r : ℕ)
        (a : Fin r → PbcIntegralRing P.coefficients.l P.extension)
        (ha : Ideal.span (Set.range a) = (pbcIntegralDatum P.coefficients.l P.extension).ideal),
      ∃ hc : cbcCompleteProperty (pbcIntegralDatum P.coefficients.l P.extension) X r a ha
          ((integralDetailedTransport X P.coefficients.l P.extension).obj K.obj.obj),
        IsIso ((ScalarLocalization.localization
          (PbcIntegralRing P.coefficients.l P.extension)
          (PbcCompletedDerived (Spec (.of Omega)) (pbcIntegralDatum P.coefficients.l P.extension))
          (pbcUniformizer P.coefficients.l P.extension)).map
          (completedCompactSupportExchange (pbcIntegralDatum P.coefficients.l P.extension)
            c (c.baseChange s) (pullback.fst c.g s)
            (compactFiberProperSquare c s) (compactFiberOpenSquare c s) r a ha
            ⟨(integralDetailedTransport X P.coefficients.l P.extension).obj K.obj.obj, hc⟩)) := by
  sorry

/-- The common-stage formulation of the Qbar stalk comparison. The local instances
are consequences of the fixed geometric setting, constructed from the recorded
finite-dimension and prime-invertibility theorems, rather than extra hypotheses.
The model retains the prescribed completed units and scalar mates, and existence of
such a normalized model is included. Source: lem-pur-cfiber-stalk.proof.md, Step 4
(blueprint: lem-pur-cfiber-stalk). -/
def CompactFiberQbarFormula : Prop :=
  letI : IsNoetherian X :=
    isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of P.field.k))
  letI : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :=
    ⟨exists_topologicalKrullDim_le (X ↘ Spec (.of P.field.k))⟩
  letI : Fact (∀ x : X, IsUnit (P.coefficients.l : X.presheaf.stalk x)) :=
    ⟨P.coefficientPrime_isUnit_stalk X (X ↘ Spec (.of P.field.k))⟩
  letI : Fact (∃ n : ℕ, topologicalKrullDim (Spec (.of Omega)) ≤ (n : WithBot ℕ∞)) :=
    ⟨exists_topologicalKrullDim_le (𝟙 (Spec (.of Omega)))⟩
  letI : Fact (∀ x : Spec (.of Omega),
      IsUnit (P.coefficients.l : (Spec (.of Omega)).presheaf.stalk x)) :=
    ⟨P.coefficientPrime_isUnit_stalk (Spec (.of Omega)) (s ≫ (Y ↘ Spec (.of P.field.k)))⟩
  ∀ c : Compactification f,
    Nonempty (CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar
      c (c.baseChange s) (pullback.fst c.g s)
      (compactFiberProperSquare c s) (compactFiberOpenSquare c s)) ∧
    ∀ (D : CbcQbarExchangeModel P.coefficients.l P.coefficients.Qbar
      c (c.baseChange s) (pullback.fst c.g s)
      (compactFiberProperSquare c s) (compactFiberOpenSquare c s))
      (K : pbcQbarCategory P.coefficients.l P.coefficients.Qbar X),
      IsIso ((StageSystem.Morphism.descNatTrans D.exchange).app K)

include hXft hXqc hYft hYqc hfOver hfSep hfft hfqc in
/-- The Qbar geometric-stalk comparison is the descended normalized exchange, on
all common-stage objects. Source: main-20261015, lem-pur-cfiber-stalk.md
(blueprint: lem-pur-cfiber-stalk).

Proof: Step 4 identifies the chapter's raw finite-stage category with
 def-weil-pbc-qbar-category using the completed coefficient presentation transport.
At every finite field stage Step 3 and its rationalization give the canonical
invertible exchange, as in thm-cbc-finite-extension. The scalar compatibility is
that of def-pur-completed-coefficient-presentation-transport. Apply
prop-weil-pbc-descent-functors and thm-cbc-qbar: the normalized exchange model exists,
and its component at a pair (E,K_E) is represented at every finite overfield M by
the corresponding scalar-extended rational exchange. Its inverse is represented
by that exchange's inverse. The common-stage composition law proves both inverse
identities; eventual equality gives independence of M and of the representative.
Step 1 reads the endpoints on Spec Omega as the stalk and fibre compact support.
Step 5 identifies the map as the canonical comparison and covers the zero, empty,
and identity cases. -/
theorem compactFiber_qbar : CompactFiberQbarFormula P f Omega s := by
  sorry


end WeilConjectures.PurityFiniteSetting
