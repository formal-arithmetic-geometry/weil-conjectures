module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompletedCompactSupportExchange
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.Paper.ExchangeFunctoriality
import all Sheaf.AlgebraicGeometry.FiniteTypeGeometryFibreBound
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionPasting

public import Sheaf.Paper.SemilinearExchangeReindexingData
public import Sheaf.Paper.SemilinearExchangeDescentData
public import Sheaf.Paper.FdCoefficientComparison

/-! # Scalar transport and compactification descent of isomorphism exchange

Source: current Weil blueprint, sec-six-functors/sk-thm-sf-package,
prop-pur-weil-equivariance-compatibilities.proof.md, constituent compatibility;
extracted scalar and refinement argument, Steps 1--9
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent).

Each conclusion below uses the specified completed exchange, its raw localization,
and the unit-normalized common-stage model. No rational reduction is introduced.
The hypotheses are the finite and actual strict integral normalization equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale.ConstantCompactificationExchange
open AlgebraicGeometry.ProEtale.RelativeCompactSupport
open WeilConjectures WeilConjectures.PurityFiniteSetting

namespace WeilConjectures

/-- Finite type schemes over the coefficient setting have the required field-base domain. -/
private theorem fieldBaseDomain (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))] :
    CbcFiniteExtensionDomain P.coefficients.l T := by
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  have : CompactSpace T :=
    QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of P.field.k))
  have : IsNoetherian T := ⟨⟩
  refine ⟨inferInstance, ?_, P.coefficientPrime_isUnit_stalk T (T ↘ _)⟩
  apply AlgebraicGeometry.finiteType_source_dimension_bound (T ↘ Spec (.of P.field.k))
  refine ⟨0, ?_⟩
  change topologicalKrullDim (PrimeSpectrum P.field.k) ≤ 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]


/-- The specified scalar comparisons carry the actual integral exchange between finite
coefficient fields, including equality of fields. The comparisons are the proper
counit/open unit mates and the completion-unit-normalized pullback comparison.
Proof (Step 2): expand the proper mate as unit, square comparison, counit. Commute
scalar extension through those three arrows using the supplied comparison squares,
then through the open comparison. Each intermediate comparison cancels its inverse.
The resulting outer square is the displayed equation. The integral scalar domain
supplies hcF; its tuple is arbitrary. Localization gives the E-to-L equation.
Source: constituent-compatibility assembly, extracted scalar/refinement argument
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeScalarComparison
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearScalar P := by
  sorry

/-- The common-stage exchange has the identical ordered integral representative at every
finite coefficient field and at every further common overfield.
Proof (Steps 2--3): scalar comparisons intertwine the two factors by the unit/counit
calculation. Their identity and tower cocycles cancel all intermediate comparisons.
Thus a representative of a morphism at one common field satisfies precisely finite
stage naturality, and further extension gives the same class. Normalize every model
by its prescribed integral components. On the isomorphism square the two reindexing
factors are invertible, so localization and common-stage inclusion preserve their
inverses. Every equation uses finitely many arrows and can be checked at one common
field; equality there is equality of their classes. No retracts are adjoined.
Source: constituent-compatibility assembly, extracted scalar/refinement argument
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeCommonStage
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearCommonStage P := by
  sorry

/-- Identity and both pasting equations for the rational exchange.
Proof: unfold the three clauses and apply the finite-extension compact-support
identity, horizontal-pasting and vertical-pasting theorems. They retain exactly the
specified complete endpoints, tuple and canonical composition comparisons.
Source: constituent compatibility and fix-lem-exchanges, finite-extension coherence
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeLocalizedPasting
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearRationalCoherence P := by
  unfold PurSemilinearRationalCoherence
  refine ⟨?_, ?_, ?_⟩
  · intros
    apply LiftedCbc.finiteExtension_compactSupportBaseChange_identity <;> assumption
  · intros
    apply LiftedCbc.finiteExtension_compactSupportBaseChange_horizontal <;> assumption
  · intros
    apply LiftedCbc.finiteExtension_compactSupportBaseChange_vertical <;> assumption

/-- Completed exchange is compatible with refinement, compactification changes
and refinement of compatible composition towers.
Proof: apply the completed compact-support refinement equation, its naturality,
identity, composition, independence and cocycle theorem, and its composition-refinement
formula to the supplied complete objects and retained etale-origin witnesses.
Source: constituent compatibility and thm-cbc-complete-proetale, refinement clauses
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeIntegralRefinement
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearRefinement P := by
  unfold PurSemilinearRefinement
  refine ⟨?_, ?_, ?_⟩
  · intros
    apply completeCompactSupportProetale_refinement <;> assumption
  · intros
    apply completeCompactSupportProetale_compactifications
  · intros
    apply completeCompactSupportProetale_composition_refinement <;> assumption

/-- The finite chosen exchange gives the compactification-independent exchange.
Proof: specialize CompactSupportFormalism.lowerShriekBaseChange_eq to the etale
derived-plus formalism and the supplied square and compactification.
Source: constituent compatibility and the compact-support formalism comparison
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeFiniteCompactification
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearFiniteCompactComparison P := by
  unfold PurSemilinearFiniteCompactComparison
  intros
  exact (Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).lowerShriekBaseChange_eq
    _ _

/-- Refinement compatibility in the specified rational and common-stage categories.
Proof: finite-type field-base schemes are Noetherian, have finite dimension and
invertible coefficient prime. The finite-extension theorem therefore supplies the
constructible source and target witnesses for the two compactifications. Apply the
completed refinement equation to the given integral lattice and its compatible origins.
Apply finiteExtensionRationalArrow to this equality, followed respectively by the
inverse rational coefficient equivalence and the common-stage inclusion and inverse
pair equivalence. Congruence preserves the actual paths and comparisons throughout.
Source: constituent compatibility; thm-cbc-complete-proetale refinement;
fix-lem-exchanges finite-extension restriction
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeRefinementScalarImages
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    ∀ (E : Padic.FiniteCoefficientFields P.coefficients.l P.coefficients.Qbar)
      {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
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
      (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
      (gb₁ : c₁'.Z ⟶ c₁.Z) (gb₂ : c₂'.Z ⟶ c₂.Z)
      (sp₁ : ChosenCartesianSquare gb₁ c₁'.g c₁.g g)
      (sj₁ : OpenImmersionSquare g' c₁'.i c₁.i gb₁)
      (sp₂ : ChosenCartesianSquare gb₂ c₂'.g c₂.g g)
      (sj₂ : OpenImmersionSquare g' c₂'.i c₂.i gb₂)
      (u : c₁.Refinement c₂) (u' : c₁'.Refinement c₂')
      (_hu : u'.hom ≫ gb₂ = gb₁ ≫ u.hom)
      (r : ℕ) (a : Fin r → (PbcIntegralRing P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E))) (ha : Ideal.span
      (Set.range a) = (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).ideal)
      (K : PbcBoundedConstructibleComplete X
        (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E))
      [IsNoetherian Y']
      [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
      [iY' : Fact (∀ y : Y', IsUnit (P.coefficients.l : Y'.presheaf.stalk y))]
      (J : FdCoefficientComparison P.coefficients.l P.coefficients.Qbar Y')
      (_origins : PbcHasCompatibleEtaleOrigins X (pbcIntegralDatum P.coefficients.l
      (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E))
      K.obj),
    ∃ (hM : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} P.coefficients.l
      P.coefficients.Qbar E)
        (((pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).completedPull g).obj
      ((cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c₂).obj K.obj)))
      (hN : PbcIsBoundedConstructibleComplete Y' (pbcStageDatum.{u} P.coefficients.l
      P.coefficients.Qbar E)
        ((cbcSupport (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E) c₁').obj
      (((pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E).completedPull g').obj K.obj))),
      LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g).map (cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar
      E)) u K.obj) ≫
          cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) c₁ c₁' gb₁ sp₁ sj₁ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩) =
        LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (        cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u}
      P.coefficients.l P.coefficients.Qbar E)) c₂ c₂' gb₂ sp₂ sj₂ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩ ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) (qf :=
      cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g').obj K.obj)) ∧
      (J.stage E).rational.inverse.map
        (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g).map (cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar
      E)) u K.obj) ≫
          cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) c₁ c₁' gb₁ sp₁ sj₁ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩)) =
        (J.stage E).rational.inverse.map
        (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (        cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u}
      P.coefficients.l P.coefficients.Qbar E)) c₂ c₂' gb₂ sp₂ sj₂ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩ ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) (qf :=
      cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g').obj K.obj))) ∧
      J.equivalence.inverse.map
        (((pbcScalarSystem P.coefficients.l P.coefficients.Qbar Y' dY'.out iY'.out).ι E).map
          (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g).map (cbcRefinementMap
      (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar
      E)) u K.obj) ≫
          cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) c₁ c₁' gb₁ sp₁ sj₁ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩))) =
        J.equivalence.inverse.map
        (((pbcScalarSystem P.coefficients.l P.coefficients.Qbar Y' dY'.out iY'.out).ι E).map
          (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
          (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) hM hN
          (        cbcExchange (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u}
      P.coefficients.l P.coefficients.Qbar E)) c₂ c₂' gb₂ sp₂ sj₂ r a ha ⟨K.obj,
          LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩ ≫
          cbcRefinementMap (pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)) (qf :=
      cbcBaseChangeQuasiCompact c₁ c₁' gb₁ sj₁)
            u' (((pbcIntegralDatum P.coefficients.l (pbcFiniteField.{u} P.coefficients.l
      P.coefficients.Qbar E)).completedPull g').obj K.obj)))) := by
  intro E X X' Y Y' f f' g g' _ _ _ _ _ _ _ _ _ _ _ _ _ _
    c₁ c₂ c₁' c₂' gb₁ gb₂ sp₁ sj₁ sp₂ sj₂ u u' hu r a ha K _ dY' iY' J origins
  let : X'.Over (Spec (.of P.field.k)) := ⟨g' ≫ (X ↘ _)⟩
  have : LocallyOfFiniteType (X' ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (g' ≫ (X ↘ _)))
  have : QuasiCompact (X' ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (g' ≫ (X ↘ _)))
  have hX := fieldBaseDomain P X
  have hY := fieldBaseDomain P Y
  have hX' := fieldBaseDomain P X'
  have := hX.1
  have := hY.1
  have := hX'.1
  obtain ⟨hS₂, _, _, _⟩ := LiftedCbc.finiteExtension_compactSupportBaseChange
    P.coefficients.l (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
    c₂ c₂' gb₂ sp₂ sj₂ hX.2.1 hY.2.1 hX'.2.1 dY'.out
    hX.2.2 hY.2.2 hX'.2.2 iY'.out
  obtain ⟨_, hT₁, _, _⟩ := LiftedCbc.finiteExtension_compactSupportBaseChange
    P.coefficients.l (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E)
    c₁ c₁' gb₁ sp₁ sj₁ hX.2.1 hY.2.1 hX'.2.1 dY'.out
    hX.2.2 hY.2.2 hX'.2.2 iY'.out
  have he := completeCompactSupportProetale_refinement
    (pbcStageDatum.{u} P.coefficients.l P.coefficients.Qbar E)
    c₁ c₂ c₁' c₂' gb₁ gb₂ sp₁ sj₁ sp₂ sj₂ u u' hu r a ha
    ⟨K.obj, LiftedCbc.finiteExtension_cbcComplete P.coefficients.l _ X K r a ha⟩ origins
  have hq := congrArg (LiftedCbc.finiteExtensionRationalArrow P.coefficients.l
    (pbcFiniteField.{u} P.coefficients.l P.coefficients.Qbar E) (hS₂ K) (hT₁ K)) he
  refine ⟨hS₂ K, hT₁ K, hq, ?_, ?_⟩
  · exact congrArg (J.stage E).rational.inverse.map hq
  · exact congrArg (fun v ↦ J.equivalence.inverse.map
      (((pbcScalarSystem P.coefficients.l P.coefficients.Qbar Y' dY'.out iY'.out).ι E).map v)) hq

/-- Canonical finite common-refinement comparisons intertwine the exchange.
Proof: specialize CompactSupportFormalism.shriekBaseChangeOfIsPullback_shriekIso to
the etale derived-plus formalism, the Cartesian square and both compactifications.
The formalism already proves the exact equation, for arbitrary underlying scheme maps.
Source: constituent compatibility and the compact-support formalism refinement law
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeFiniteCommonRefinement
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    ∀ {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
      {g : Y' ⟶ Y} {g' : X' ⟶ X}
      [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
      [IsSeparated (X ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
      [QuasiCompact (X ↘ Spec (.of P.field.k))]
      [IsSeparated (Y ↘ Spec (.of P.field.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
      [QuasiCompact (Y ↘ Spec (.of P.field.k))]
      [f.IsOver (Spec (.of P.field.k))]
      [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] [QuasiCompact f']
      [IsIso g] [IsIso g']
      (sq : IsPullback g' f' f g) (c₁ c₂ : Compactification f),
    Functor.whiskerRight
        ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).shriekIso c₁ c₂).hom
        ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).pb g) ≫
      ((Etale.derivedPlusFormalism
        (ModuleCat.{u + 1} P.Coefficient)).shriekBaseChangeOfIsPullback sq c₂).natTrans =
      ((Etale.derivedPlusFormalism
        (ModuleCat.{u + 1} P.Coefficient)).shriekBaseChangeOfIsPullback sq c₁).natTrans ≫
      Functor.whiskerLeft
        ((Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)).pb g')
        ((Etale.derivedPlusFormalism
          (ModuleCat.{u + 1} P.Coefficient)).shriekIso
            (c₁.ofIsPullback sq) (c₂.ofIsPullback sq)).hom := by
  intros
  exact CompactSupportFormalism.shriekBaseChangeOfIsPullback_shriekIso
    (Etale.derivedPlusFormalism (ModuleCat.{u + 1} P.Coefficient)) _ _ _

/-- Scalar localization carries the actual integral two-factor identity to the ordered
rational reindexing identity, with its quotient-completion unit and the original
constructible endpoints. The tuple may be any finite generating tuple.
Proof (Steps 1 and 5--6): identify both strict factors before Rlim by the supplied
normalization. Their derived limits are completedCompactSupportExchange. Substitute
the ordered identity into the prescribed localization of that map. Functoriality
preserves its two factors and all invertible endpoint comparisons; the inverse unit
fixes the isomorphism e uniquely. Fraction naturality is integral naturality multiplied
by the inverse uniformizer power. For coefficient change, commute through proper units
and counits and the open comparison; the adjacent scalar comparisons cancel. Their
cocycles make common-stage representatives independent of field enlargement. For
refinement apply the strict proper/open equation, its corner normalizations and Rlim,
then localize. Cancellation of the canonical comparison inverses gives independence,
the common-refinement cocycle and compatibility with the compact-support compositor.
Finite evaluation gives the finite formula, with the retained etale-origin witness.
No reduction is applied to a rational arrow.
Source: constituent-compatibility assembly, extracted scalar/refinement argument
(blueprint: lem-pur-isomorphism-exchange-scalar-refinement-descent). -/
theorem isomorphismExchangeScalarRefinementDescent
    (P : PurityFiniteSetting.{u})
    (_finite : PurSemilinearFiniteNormalization P)
    (_finiteIdentity : PurSemilinearFiniteIdentity P)
    (_finiteHorizontal : PurSemilinearFiniteHorizontal P)
    (_finiteVertical : PurSemilinearFiniteVertical P)
    (_finiteReduction : PurSemilinearFiniteCoefficient P)
    (_integral : PurReindexing.PurStrictIntegralGeometricNormalization P)
    (_strict : PurReindexing.PurIntegralStrictMapNormalization
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictHorizontal : PurReindexing.PurIntegralStrictHorizontal
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictVertical : PurReindexing.PurIntegralStrictVertical
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_strictReduction : PurReindexing.PurIntegralStrictReduction
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k)))
    (_completed : PurReindexing.PurIntegralCompletedCoherence
      (pbcIntegralDatum P.coefficients.l P.extension) (Spec (.of P.field.k))) :
    PurSemilinearRational P ∧
      PurSemilinearScalar P ∧
      PurSemilinearCommonStage P ∧
      PurSemilinearRationalCoherence P ∧
      PurSemilinearRefinement P ∧
      PurSemilinearFiniteCompactComparison P := by
  sorry

end WeilConjectures
