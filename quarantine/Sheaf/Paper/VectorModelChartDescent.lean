module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.ProjectionPurityAgreement
public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.PurityDncInvariance
public import Sheaf.Paper.AffineDiagonalTateCoordinates
public import Sheaf.Paper.SmoothPurityMap
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.VectorBundleFiniteTypeFrames
public import Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts
public import Mathlib.AlgebraicGeometry.AffineSpace
import Sheaf.Paper.DualizingUnitComposite
import Sheaf.Paper.StandingExceptionalComposition
import Sheaf.Paper.CanonicalOriginCompactSupportComposition
import Sheaf.Paper.DegreeZeroDerivedMapGluing
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Descent of a vector-bundle model comparison from normalized charts

Source: blueprint sec-smooth-purity/sk-thm-smooth-purity, Agreement on the model;
sec-smooth-purity/sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md,
Steps 3--4 (blueprint: lem-pur-vector-model-chart-descent).

The comparison c is an actual isomorphism on the small pro-etale site. Its chart
restriction uses the inverse linear frame, canonical Tate pullback, and the actual
exceptional base-change mate. The smooth map is the coefficient-unit component of
the recorded tensor transpose, in its canonical unit and shift coordinates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The bundle's exceptional coefficient-unit object, with compactification supplied
by its affine finite-type geometry. Source: omega_pi in the model comparison
(blueprint: lem-pur-vector-model-chart-descent). -/
def vectorModelDualizing (P : PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (d : ℕ) (M : Z.Modules) [M.IsFiniteLocallyFreeOfRank d] :=
  letI := (Etale.vectorIntegration_geometry Z d M).1
  letI := (Etale.vectorIntegration_geometry Z d M).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π Z d M) aZ
  P.diagonalDualizing (VectorBundleZeroSection.π Z d M)

/-- Restrict the specified c through the inverse linear chart. The first two
factors are the canonical Tate pullback; the last three are the comparison of
sites and the actual exceptional base-change mate in the inverse-frame square.
No smooth orientation enters this definition.
Source: the hypothesis c|_(V_i) = Gamma, and proof Step 3(c)
(blueprint: lem-pur-vector-model-chart-descent). -/
def vectorModelChartRestriction (P : PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (d : ℕ) (M : Z.Modules) [M.IsFiniteLocallyFreeOfRank d]
    (c : P.diagonalTwist (VectorBundleZeroSection.scheme Z d M) d ≅
      P.vectorModelDualizing Z aZ d M)
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d M U) :=
  letI := (Etale.vectorIntegration_geometry Z d M).1
  letI := (Etale.vectorIntegration_geometry Z d M).2.1
  letI := Dnc.compactifiable P (VectorBundleZeroSection.π Z d M) aZ
  letI := (ProEtale.AffineSpacePurity.projection_geometry U.toScheme d).2
  letI := (VectorBundleZeroSection.finite_type_frames P.field.k Z aZ d M).choose_spec.2.2.2.2.2.1
  let a := Etale.vectorIntegrationChart Z d M U e
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates
  let C := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) (affineTraceTower U.toScheme d)).mapDerivedCategory
  C.map (Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates t a
      (P.diagonalExponent_isUnit (VectorBundleZeroSection.π Z d M ≫ aZ)) d).inv ≫
    (Dnc.pullComparison P a (P.diagonalTwistEtale
      (VectorBundleZeroSection.scheme Z d M) d)).inv ≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
      c.hom ≫
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
      (P.diagonalDualizingComparison (VectorBundleZeroSection.π Z d M)).hom ≫
    (Dnc.pullComparison P a
      (P.diagonalOrdinaryDualizing (VectorBundleZeroSection.π Z d M))).hom ≫
    C.map (P.chartOrdinaryBaseChange d (VectorBundleZeroSection.π Z d M) aZ
      U.ι (affineTraceProjection U.toScheme d) a
      (Etale.vectorIntegrationChart_isPullback Z d M U e)).hom

/-- The coefficient-unit tensor source has its canonical unitor identification.
The equality of the cached tensor presentation supplies only endpoint transport;
the map is pullback of the unit followed by the ordinary left unitor.
Source: proof Step 1, coefficient-unit and twist reassociation
(blueprint: lem-pur-vector-model-chart-descent). -/
def vectorModelTensorUnit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (d : ℕ) :=
  eqToIso (congrArg (fun T ↦ (T.obj
    ((P.smoothPurityPullback f).obj
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) Y).mapDerivedCategory.obj
          (Etale.ordinaryFiniteUnit P.Coefficient Y)))).obj (P.diagonalTwist X d))
    (smoothPurityTensorPresentation (ModuleCat.{u + 1} P.Coefficient) X)) ≪≫
    ((curriedTensor (_root_.DerivedCategory
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))).mapIso
        (P.chartUnitPullback f)).app (P.diagonalTwist X d) ≪≫
      (λ_ (P.diagonalTwist X d))

/-- The specified diagonal smooth purity map on A_Z, expressed as Q -> omega_pi.
The inverse source identification cancels only the pullback unit, tensor unitor
and Tate/shift reassociation. The remaining map is the recorded tensor transpose
in its canonical ordinary-etale presentation, not a newly chosen orientation.
Source: def-pur-smooth-purity-map at K = A_Z and proof Step 1
(blueprint: lem-pur-vector-model-chart-descent). -/
def vectorModelSmoothUnit (P : PurityFiniteSetting.{u})
    (Z : Scheme.{u}) [IsNoetherian Z] (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ]
    (d : ℕ) (M : Z.Modules) [M.IsFiniteLocallyFreeOfRank d] :=
  letI := (Etale.vectorIntegration_geometry Z d M).1
  letI := (Etale.vectorIntegration_geometry Z d M).2.1
  letI := (VectorBundleZeroSection.finite_type_frames P.field.k Z aZ d M).choose_spec.2.2.2.2.2.1
  let f := VectorBundleZeroSection.π Z d M
  let K := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) Z).mapDerivedCategory.obj
      (Etale.ordinaryFiniteUnit P.Coefficient Z)
  let s := P.smoothPurityReassociation (VectorBundleZeroSection.scheme Z d M) d
    ((P.smoothPurityPullback f).obj K)
  (s ≪≫ P.vectorModelTensorUnit f d).inv ≫ s.hom ≫
    P.smoothPurityTensorMapInPresentation f d aZ K
      (Etale.ordinaryFiniteUnit P.Coefficient Z) (Iso.refl _)

/-- The exact local-to-global assertion, with Noetherianity deduced from finite type.
The positive level n+1 ranges over all permitted coefficients. HEq compares the
canonical ordered polynomial towers without an arbitrary endpoint isomorphism.
The set-index type is arbitrary and need not be finite or inhabited.
Source: chart-normalized comparison hypothesis and conclusion
(blueprint: lem-pur-vector-model-chart-descent). -/
def VectorModelChartDescentConclusion
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (M : Z.Modules) [M.IsFiniteLocallyFreeOfRank d] : Prop :=
  let P := projectionSetting F C E n
  letI : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
  ∀ (c : P.diagonalTwist (VectorBundleZeroSection.scheme Z d M) d ≅
        P.vectorModelDualizing Z aZ d M)
    (I : Type w) (U : I → Z.Opens) (_hU : iSup U = ⊤)
    (e : ∀ i : I, VectorBundleZeroSection.Trivialization Z d M (U i)),
    (∀ i : I,
      HEq (P.vectorModelChartRestriction Z aZ d M c (U i) (e i))
        (chartGamma F C E n (U i).toScheme ((U i).ι ≫ aZ) d ≫
          (P.diagonalDualizingComparison (iteratedAffineLineProj (U i).toScheme d)).hom)) →
    P.vectorModelSmoothUnit Z aZ d M = c.hom

/-- A comparison normalized on a linear Zariski cover is the specified diagonal
smooth purity map at the coefficient unit, at every positive finite level.
Source: blueprint sk-thm-smooth-purity, Agreement on the model, and
sk-prop-sp-orientation-charts.proof.md, Steps 3--4
(blueprint: lem-pur-vector-model-chart-descent).

Proof:
1. By lem-pur-dualizing-unit-composite the coefficient-unit tensor transpose is
   the canonical unitor. In def-pur-smooth-purity-map its unit and reassociation
   comparisons cancel, giving gamma_(pi,A) = Pi_pi^-1. Put a = c followed by Pi_pi.
2. Refine the given base cover by finite-type affine opens B. Their inverse images
   are affine polynomial charts. The relative-Spec projection is affine, finite
   type, separated and smooth of pure dimension d; its total space is separated
   finite type over k. These are the chart-normalization hypotheses.
3. On each refined chart lem-pur-diagonal-dnc-chart-normalization identifies Pi_pi
   with pullback of Gamma^-1, through the specified exceptional comparison. Over
   a possibly nonaffine U_i, lem-pur-projection-purity-agreement and the unit clause
   first identify Gamma with the inverse diagonal orientation. Apply target-open
   chart normalization to restrict it to B. The exceptional compositors of
   pur9-def-upper-shriek-composition agree under further restriction by the
   associativity of thm-sf-comp-composition. Hence the hypothesis restricts to the
   same Gamma on B. The inverse factors cancel, so a restricts to identity.
4. The unshifted finite Tate line is an ordinary module sheaf. Remove [2d] from a
   and its identity. Exact restriction commutes with shifts, and the injectivity
   clause of lem-pur-degree-zero-derived-map-gluing gives equality globally.
   Restore the shift and cancel Pi_pi. Rank zero uses identity normalization;
   empty bases allow the empty cover; disconnected bases need no extra argument.
   No coefficient field or ramification-divisibility hypothesis is used. -/
theorem vector_model_chart_descent
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (M : Z.Modules) [M.IsFiniteLocallyFreeOfRank d] :
    VectorModelChartDescentConclusion.{u, w} F C E n Z aZ d M := by
  sorry

end WeilConjectures.PurityFiniteSetting
