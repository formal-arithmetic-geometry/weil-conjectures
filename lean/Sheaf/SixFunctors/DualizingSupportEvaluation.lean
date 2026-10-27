module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.SixFunctors.FiniteDualizing
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.FiniteCoefficientPoint
public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.CompactSupportReductionTowerData
public import Sheaf.Paper.PointSectionsDerivedReductionData
public import Sheaf.SecSmoothPurity.ReductionDirectImageComparison
public import Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction
public import Sheaf.Paper.EtaleProEtaleCoefficientTransport
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.SecSmoothPurity.ReductionExceptional
import Sheaf.Paper.CompactSupportIntrinsicTensorComparison
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.SixFunctors.CoefDualizingConstruction
import Sheaf.Paper.EtaleCompactSupportCoefficientChange
import Sheaf.SixFunctors.OpenScalarTensorNormalization
import Sheaf.Paper.ReductionOpenEtaleOrigin
import Sheaf.AlgebraicGeometry.FixSiteOpenExchange
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Sheaf.Paper.EtaleProEtaleScalarMate
import Sheaf.Paper.EtaleProEtaleScalarPullbackCube
import Sheaf.SixFunctors.FiniteDualitySiteComparison
import Sheaf.Paper.CompactSupportNativeSystemTransition

/-! # Evaluated compact support and scalar-adjunction transitions

Source: blueprint `prop-coef-integral-dualizing.proof.md`, paragraph 2,
specified finite maps before limits (blueprint: lem-coef-dualizing-support-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.DualizingSupportEvaluation

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary compact support on the whole sequence site, with j_! exact and Rp_*
derived on systems. Source: blueprint paragraph 2, before limits
(blueprint: lem-coef-dualizing-support-evaluation). -/
def support {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a) :
    coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
  ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
    (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g

/-- Exact final-object sections on strict towers, with constant integral action.
Source: blueprint paragraph 2; Stacks 03CW
(blueprint: lem-coef-dualizing-support-evaluation). -/
abbrev sectionsTowers :=
  (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pointIntegralSections l E D.k)

/-- Exactness at kernels is levelwise. Source: Stacks 03CW, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance sectionsTowersLimits : PreservesFiniteLimits (sectionsTowers D l E) where
  preservesFiniteLimits _ _ _ := inferInstance

/-- Exactness at cokernels is levelwise. Source: Stacks 03CW, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance sectionsTowersColimits : PreservesFiniteColimits (sectionsTowers D l E) where
  preservesFiniteColimits _ _ _ := inferInstance

/-- The ordinary derived category of constant-R module towers, with no inverse limit.
Source: blueprint paragraph 2; Stacks 05RU, 0941
(blueprint: lem-coef-dualizing-support-evaluation). -/
instance towerHasDerived : HasDerivedCategory
    (ℕᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  HasDerivedCategory.standard _

/-- B(Q): derive proper image first, then point sections on the entire tower.
The completed restriction is only an intermediate presentation: pointIntegralSections
restricts along the actual constant map R to the completed section ring. Its composite
at level n is the actual R to A_(n+1) restriction. No inverse limit is used.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def B {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (c : Compactification a) :=
  support l E c ⋙ coefficientSequenceDerivedRestriction l E (Spec (.of D.k)) ⋙
    (sectionsTowers D l E).mapDerivedCategory

/-- Exact evaluation in the ordinary derived tower category.
Source: Stacks 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
abbrev ev (n : ℕ) :=
  ((evaluation ℕᵒᵖ (ModuleCat.{u + 1}
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).obj (op n)).mapDerivedCategory

/-- The actual localized horizontal map of a strict R-module tower.
Source: Stacks 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def transition {m n : ℕ} (h : n ≤ m) : ev l E m ⟶ ev l E n :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) (.up ℤ)) _ _ _ _
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (ModuleCat.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))).map (homOfLE h).op)
      (.up ℤ)) DerivedCategory.Q)

/-- Final-object sections of a finite-level complex, with the actual constant R action.
Source: blueprint paragraph 2; Stacks 03CW
(blueprint: lem-coef-dualizing-support-evaluation). -/
def sections (n : ℕ) :=
  coefficientFiniteDerivedRestriction l E (Spec (.of D.k)) n ⋙
    (pointIntegralSections l E D.k).mapDerivedCategory

/-- The canonical change from the identified-ring direct image to sectionwise direct
image. Both models use exactly the same constant-section structure map.
Source: Stacks 03D2, 0D6E (blueprint: lem-coef-dualizing-support-evaluation). -/
def supportModel {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    (A : Type u) [CommRing A] [Finite A] :
    reductionCompactSupport A c.i c.g ≅ sfIntrinsicCompactSupport c A :=
  Functor.isoWhiskerLeft (sfIntrinsicExtensionByZero c.i A).mapDerivedCategory
    (eqToIso (AlgebraicGeometry.ProEtale.reductionConstantPush_eq A c.g))

/-- c is the proper coefficient mate followed by the exact open coefficient map,
transported only by the specified direct-image presentation.
Source: blueprint paragraph 2; Stacks 0GL1, 0D6E
(blueprint: lem-coef-dualizing-support-evaluation). -/
def comparison {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) :
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1)) ⋙
        scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y ⟶
      scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X ⋙
        sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) :=
  Functor.whiskerRight (supportModel c (Padic.coefficientExtensionRing l E (m + 1))).inv
      (scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) Y) ≫
    reductionDirectImageComparison (compactSupportLevelQuotient l E m n h) c.i c.g ≫
    Functor.whiskerLeft (scalarExtensionFunctor (compactSupportLevelQuotient l E m n h) X)
      (supportModel c (Padic.coefficientExtensionRing l E (n + 1))).hom

/-- Exact quotient restriction in the two published coefficient presentations.
Source: Stacks 03DA, 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def quotientRestrictionModel (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    normalizedDVRRes l E X h ≅
      scalarRestriction (compactSupportLevelQuotient l E m n h) X :=
  by
    letI := proEtaleRingRestrictScalars_preservesFiniteLimits
      (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))
    letI := proEtaleRingRestrictScalars_preservesFiniteColimits
      (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))
    exact Functor.mapDerivedCategoryNatIso (eqToIso (by
      rw [finiteDualizingRestriction_eq l E X h]
      rfl))

/-- The actual sequence-site transition, transported to constant quotient restriction.
Source: Stacks 0941, blueprint paragraph 2
(blueprint: lem-coef-dualizing-support-evaluation). -/
def sigma (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  (coefficientSequenceDerivedTransition l E X h).app Q ≫
    (quotientRestrictionModel l E X h).hom.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj Q)

/-- alpha is the tensor-restriction adjunct of the actual horizontal transition.
Source: blueprint paragraph 2; Stacks 07A6
(blueprint: lem-coef-dualizing-support-evaluation). -/
def alpha (X : Scheme.{u}) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  ((proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := X) (compactSupportLevelQuotient l E m n h))).homEquiv
      _ _).symm (sigma l E X h Q)

/-- The specified restriction-form arrow eta followed by Res(F_n(alpha) c).
Source: blueprint paragraph 2, displayed d (blueprint: lem-coef-dualizing-support-evaluation). -/
def d {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) (Q : coefficientSequenceDerived l E X) :=
  (proEtaleRingDerivedExtensionAdjunction
    (proEtaleConstantRingMap (T := Y) (compactSupportLevelQuotient l E m n h))).unit.app
      ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).obj
        ((coefficientSequenceDerivedEvaluation l E X m).obj Q)) ≫
    (scalarRestriction (compactSupportLevelQuotient l E m n h) Y).map
      ((comparison l E c h).app ((coefficientSequenceDerivedEvaluation l E X m).obj Q) ≫
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
          (alpha l E X h Q))

/-- R Gamma(s,d), with the canonical composition of quotient and constant-R restrictions.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def sectionTransition {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) {m n : ℕ} (h : n ≤ m)
    (Q : coefficientSequenceDerived l E X) :=
  (sections D l E m).map (d l E c h Q) ≫
    (pointIntegralSections l E D.k).mapDerivedCategory.map
      ((compactSupportRestrictionComp l E (Spec (.of D.k)) m n h).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((coefficientSequenceDerivedEvaluation l E X n).obj Q)))

/-- The finite-level target of Theta, as a functor on the entire derived input category.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def target {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (c : Compactification a) (n : ℕ) :=
  coefficientSequenceDerivedEvaluation l E X n ⋙
    sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)) ⋙ sections D l E n

/-- The canonical evaluation of point sections on a whole strict tower.
Source: Stacks 03CW, 0941 (blueprint: lem-coef-dualizing-support-evaluation). -/
def sectionsEvaluation (n : ℕ) :
    (sectionsTowers D l E).mapDerivedCategory ⋙ ev l E n ≅
      coefficientConstantTowerEvaluation l E (Spec (.of D.k)) n ⋙
        (pointIntegralSections l E D.k).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (Iso.refl _)

/-- Theta is assembled from actual point, quotient, proper and open evaluations.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def theta {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)}
    (c : Compactification a) (n : ℕ) : B D l E c ⋙ ev l E n ≅ target D l E c n := by
  let i₁ := Functor.isoWhiskerLeft
    (support l E c ⋙ coefficientSequenceDerivedRestriction l E (Spec (.of D.k)))
    (sectionsEvaluation D l E n)
  let i₂ := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (support l E c)
      (coefficientRestrictedEvaluationIso l E (Spec (.of D.k)) n))
    (pointIntegralSections l E D.k).mapDerivedCategory
  let i₃ := Functor.isoWhiskerRight (compactSupportSystemEvaluation l E c n)
    (sections D l E n)
  exact Functor.associator _ _ _ ≪≫ i₁ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫ i₂ ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫ i₃ ≪≫ Functor.associator _ _ _

/-- The same d arrow in the published coherent quotient-restriction coordinates.
Only the canonical restriction-presentation isomorphism is applied.
Source: blueprint paragraph 2 (blueprint: lem-coef-dualizing-support-evaluation). -/
def dNormalized {X Y : Scheme.{u}} {a : X ⟶ Y} (c : Compactification a)
    {m n : ℕ} (h : n ≤ m) (Q : coefficientSequenceDerived l E X) :=
  d l E c h Q ≫ (quotientRestrictionModel l E Y h).inv.app
    ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
      ((coefficientSequenceDerivedEvaluation l E X n).obj Q))

/-- The counit-defined finite-dualizing transition in the actual quotient coordinates.
Source: lem-coef-finite-dualizing, finite pro-etale realization
(blueprint: lem-coef-dualizing-support-evaluation). -/
def dualizingTransition (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] (hl : l ≠ D.p) {m n : ℕ} (h : n ≤ m) :=
  integralDualizingExceptionalTransition l E D X hl h ≫
    (quotientRestrictionModel l E X h).hom.app (integralDualizingFiniteTerm l E D X n)

/-- The finite-dualizing site square: the transported actual proper/open coefficient
map equals the etale comparison after canonical scalar and site identifications.
Only lower-bound witnesses are existential, not maps or complexes.
Source: blueprint paragraph 2, finite counit maps
(blueprint: lem-coef-dualizing-support-evaluation). -/
def DualizingSiteCompatibility (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) {m n : ℕ} (h : n ≤ m) : Prop :=
  ∃ hL : DerivedCategory.TStructure.t.plus (finiteDualizingEtaleTerm l E D X m),
    ∃ hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
        (finiteDualizingEtaleTerm l E D X m)),
    (CoefficientCompatibility.liftedScalarExtension
      (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
      ((compactSupportSiteComparison (finiteDualizingCoeff l E m) c).inv.app
        ⟨finiteDualizingEtaleTerm l E D X m, hL⟩) ≫
      (CoefficientCompatibility.transportedRecordedReductionDirectImageComparison
        (compactSupportLevelQuotient l E m n h) c
        (reductionDirectImageComparison (compactSupportLevelQuotient l E m n h)
          c.i c.g)).app
        ((comparisonUpperStar
          (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) X).mapDerivedCategory.obj
            (finiteDualizingEtaleTerm l E D X m)) ≫
      (rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E n)) c).map
        ((pbcComparisonReduction X (finiteDualizingQuotient l E h)).hom.app
          (finiteDualizingEtaleTerm l E D X m)) =
    (pbcComparisonReduction (Spec (.of D.k)) (finiteDualizingQuotient l E h)).hom.app
      ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (finiteDualizingCoeff l E m)) c).obj
          (finiteDualizingEtaleTerm l E D X m)) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
        (Spec (.of D.k))).mapDerivedCategory.map
        (Etale.ExceptionalCoefficients.compactSupportMap (finiteDualizingQuotient l E h)
          c (finiteDualizingEtaleTerm l E D X m)) ≫
      (compactSupportSiteComparison (finiteDualizingCoeff l E n) c).inv.app
        ⟨(Etale.scalarExtension (finiteDualizingQuotient l E h) X).obj
          (finiteDualizingEtaleTerm l E D X m), hLB⟩

/-- Evaluated support, its scalar-unit formula, coherence, and finite-dualizing
normalization, for arbitrary unbounded strict derived inputs.

Source: blueprint prop-coef-integral-dualizing.proof.md, paragraph 2
(blueprint: lem-coef-dualizing-support-evaluation).
Proof:
1. Identify quotient-semilinear systems with modules on the vertical sequence site
(def-coef-ringed-sequence-site). Semilinear derived sections gives proper evaluation;
exact open extension gives open evaluation, without evaluated K-injectivity.
2. The open transition is j_!(alpha) after the normalized open tensor map: its
adjunction transpose is j_!(sigma). Paste with the proper coefficient mate to get c
(lem-fix-open-scalar-tensor-normalization, lem-coef-semilinear-derived-sections).
3. Transpose by derived tensor-restriction adjunction: the restriction arrow is
eta followed by Res(F_n(alpha)c), with no quotient-flatness assumption
(lem-pur-sheaf-ring-derived-coefficient-adjunction).
4. Mate pasting identifies the transpose of c with rho F(eta); naturality at alpha
then gives d=rho F(sigma) (lem-sf-compact-support-restriction-of-scalars,
def-coef-compact-support-tensor-comparison, lem-weil-pbc-mate-pasting).
5. Derive point sections separately on systems. Its evaluation and the exact
constant-R restriction give theta and the section-transition equation. Neither
operation takes an inverse limit (lem-coef-semilinear-derived-sections).
6. Conjugate the actual strict tower identity and composition by theta. This proves
coherence of the specified transitions, without detecting equality by evaluations.
7. For omega, finite dualizing construction and finite Tor site comparison supply
bounded constructible etale origins for omega and its reduction/open extension
(lem-coef-dualizing-construction, det-pe-finite-tor-comparison-noetherian,
lem-fix-reduction-open-etale-origin, lem-weil-finite-duality-site-comparison).
8. The proper scalar-mate/site square and normalized open units identify c with the
finite realization of the etale compactSupportMap. Paste the scalar/pullback cube
and open exchange (lem-sfb-etale-proetale-scalar-mate,
lem-fix-open-scalar-tensor-normalization, lem-fix-site-open-exchange,
lem-sfb-etale-proetale-scalar-pullback-cube, lem-fix-compact-support-coefficient-change).
9. Substitute the counit-defined u using lem-coef-finite-dualizing. Conjugation by
the given level isomorphisms gives exactly the displayed specialized d formula.
All maps used are the named actual operations of Q and the fixed compactification.
-/
theorem evaluatedSupport (hl : l ≠ D.p) (X : Scheme.{u})
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k))) :
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m),
      (transition l E h).app ((B D l E c).obj Q) ≫ (theta D l E c n).hom.app Q =
        (theta D l E c m).hom.app Q ≫ sectionTransition D l E c h Q) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m),
      d l E c h Q =
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
          (sigma l E X h Q) ≫
        (sfCompactSupportRestriction c (compactSupportLevelQuotient l E m n h)).hom.app
          ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) ∧
    (∀ (Q : coefficientSequenceDerived l E X) (n : ℕ),
      sectionTransition D l E c (le_refl n) Q = 𝟙 _) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {r m n : ℕ}
      (hrm : m ≤ r) (hmn : n ≤ m),
      sectionTransition D l E c hrm Q ≫ sectionTransition D l E c hmn Q =
        sectionTransition D l E c (hmn.trans hrm) Q) ∧
    (∀ (Q : coefficientSequenceDerived l E X) (n : ℕ),
      dNormalized l E c (le_refl n) Q ≫
        (normalizedDVRResUnit l E (Spec (.of D.k)) n).hom.app
          ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) = 𝟙 _) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {r m n : ℕ}
      (hrm : m ≤ r) (hmn : n ≤ m),
      dNormalized l E c hrm Q ≫
        (normalizedDVRRes l E (Spec (.of D.k)) hrm).map (dNormalized l E c hmn Q) ≫
        (normalizedDVRResComp l E (Spec (.of D.k)) hrm hmn).hom.app
          ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
            ((coefficientSequenceDerivedEvaluation l E X n).obj Q)) =
        dNormalized l E c (hmn.trans hrm) Q) ∧
    (∀ {m n : ℕ} (h : n ≤ m), DualizingSiteCompatibility D l E X c h) ∧
    (∀ (Q : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m)
      (iₘ : (coefficientSequenceDerivedEvaluation l E X m).obj Q ≅
        integralDualizingFiniteTerm l E D X m)
      (iₙ : (coefficientSequenceDerivedEvaluation l E X n).obj Q ≅
        integralDualizingFiniteTerm l E D X n),
      sigma l E X h Q ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) X).map iₙ.hom =
        iₘ.hom ≫ dualizingTransition D l E X hl h →
      d l E c h Q =
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).map
            iₘ.hom ≫
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Spec (.of D.k))
              (compactSupportLevelQuotient l E m n h))).unit.app
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (m + 1))).obj
              (integralDualizingFiniteTerm l E D X m)) ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
            ((comparison l E c h).app (integralDualizingFiniteTerm l E D X m) ≫
              (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
                (((proEtaleRingDerivedExtensionAdjunction
                  (proEtaleConstantRingMap (T := X)
                    (compactSupportLevelQuotient l E m n h))).homEquiv _ _).symm
                  (dualizingTransition D l E X hl h))) ≫
          (scalarRestriction (compactSupportLevelQuotient l E m n h) (Spec (.of D.k))).map
            ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
              iₙ.inv)) := by
  sorry

end WeilConjectures.DualizingSupportEvaluation
