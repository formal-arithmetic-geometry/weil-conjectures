module

public import Sheaf.Paper.VectorTensorSiteEquations

public import Sheaf.Paper.PurityFiniteSetting
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted
public import Sheaf.AlgebraicGeometry.CartierKummerMap
public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace
public import Sheaf.AlgebraicGeometry.GeoP1Cohomology
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
public import Sheaf.Paper.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.ProjectionMateExact
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.PurTwistSheafLocallyFree
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroExact
import Sheaf.Paper.CompactSupportSiteCoherence
import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.AlgebraicGeometry.OpenProjectionSiteTransport
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula
import Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance
import Sheaf.Paper.DegreeZeroDerivedMapGluing
public import Sheaf.Paper.BoundedSiteAdjunctionTranspose
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Targets.VectorBundlePurity

/-! # Site comparison of normalized vector-bundle integration
Source: Stacks 099R, 09AF and 0B65; main-20261015, vector-bundle integration
(blueprint: lem-pur-vector-integration-site-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite
variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def ProjectiveCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) : Prop :=
    ((comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.projectiveLineTraceDatum (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1))).decomposition.hom ≫
      (directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom =
      projectiveSum l E n r hA S ≫ projectiveB l E n S hS hI r hA) ∧
    ((directImage (Scheme.finiteTateCoefficient l E n) (ProjectiveLine S ↘ S)
        (linePlus l E n r hA (ProjectiveLine S))).hom ≫
      projectiveTrace l E n S hS hI r hA =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.projectiveLineTrace (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) _ hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)))) ∧
    projectiveH l E n S hS hI r hA ≫ projectiveTrace l E n S hS hI r hA =
      𝟙 (unit (Scheme.finiteTateCoefficient l E n) S)

/-- Comparison carries the ordinary decomposition to the two actual supported-Kummer
components. Source: projective-line trace and Stacks 099R, 0B65
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: the mate's counit equation carries the adjunct of the ordinary Kummer class
to the supported pro-etale class. At the identity it carries the shifted twisted
unit. The two biproduct injections detect equality. Invert the decomposition and
compose with the second projection for the trace equation and its +1 normalization.
-/
theorem projectiveComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (hI : (ProjectiveLine.infinity S).ker.IsInvertible)
    (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    ProjectiveCompatibility l E n S hS hI r hA := by
  sorry

/-- Exact extension comparison preserves the actual open counit.
Source: Stacks 09AF (blueprint: lem-pur-vector-integration-site-comparison).
Proof: both routes restrict to the identity. Transpose using the open adjunction;
its Hom bijection gives equality. Apply termwise to complexes and localize.
-/
theorem openCounitComparison {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (G : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparison A X).map
        (((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) j).ofNatIsoRight
            (Etale.leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) j).symm).counit.app G) =
      (openProjectionExtensionComparison A j).hom.app
        ((Etale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj G) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        ((openProjectionRestrictionComparison A j).hom.app G) ≫
      (openAdjunction A j).counit.app ((comparison A X).obj G) := by
  sorry

/-- The displayed canonical comparison equations, packaged as a proposition.
Source: Stacks 099R, 09AF, 0B65 and the vector-bundle integration formulas
(blueprint: lem-pur-vector-integration-site-comparison). -/
def IntegrationCompatibility (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
    VectorNormalization l E n S r hA d F hS
      (vectorIntegration l E n S r hA d F hS) ∧
    (vectorSite l E n S r hA d F hS).inv ≫
        vectorIntegration l E n S r hA d F hS =
      (comparison (Scheme.finiteTateCoefficient l E n) S).map
        (Etale.vectorBundleIntegration (l ^ (r + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (Scheme.finiteTateCoefficient l E n) hA S
          (by simpa only [Nat.cast_pow] using hS.pow (r + 1)) d F)

/-- The independent local pro-etale integrations glue and compare with the actual
ordinary global trace. Source: vector-bundle integration; Stacks 09AF, 099R
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: compare the projective counit by inverse projection, tensor trace and the
unit equation. Restrict by the compared open counit, then induct on coordinates.
Pasting the compact-support comparisons gives the same chart prefixes. On each
frame this is the ordinary trace. Sources and targets are degree zero, so equality
glues by sheaf-Hom descent. Rank zero uses the identity tower; the empty base has
the unique morphism. None of these steps imposes flatness of A over Z/l^r.
-/
theorem vectorIntegrationSiteComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    IntegrationCompatibility l E n S hS r hA d F := by
  sorry

set_option linter.unusedVariables false in
/-- Tensor projection, integration, and the bounded etale-origin transposes compare.
The projection inverses are specified by equality of their inverses with the actual
maps. Source: Stacks 0944, 0GL1 and 0B65
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: the proper square is the counit-mate tensor square, and the open square is
the unit-normalized open projection square. Paste them. The ordinary projection
is invertible on finite-Tor inputs, hence so is the compared projection. Invert
the square, tensor the global trace equation and apply the normalized unit map.
The bounded Hom chain gives the transpose equation with rho. Ordinary purity
identifies the inverse of the adjunct with its integration-normalized bundle map.
-/
theorem vectorTensorComparison (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r : ℕ)
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d]
    (K : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient l E n) S)
    (hK : Etale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) S K) :
    TensorCompatibility l E n S hS r hA d F K hK := by
  sorry

/-- Exponent transitions preserve the independent global integration.
Source: root projections, ordered traces and degree-zero gluing
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: projections commute with the supported Kummer boundary; thus decomposition,
inverse and trace agree after transition. Restrict with the open counit and iterate
the coordinate maps. Equality on frames glues. The tensor and transpose statements
are independent of exponent by their formulas and Hom naturality as well.
-/
theorem vectorExponentIndependence (S : Scheme.{u}) [IsNoetherian S]
    (hS : IsUnit (l : Γ(S, ⊤))) (r r' : ℕ) (h : r ≤ r')
    (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ)
    (F : SheafOfModules.{u} S.ringCatSheaf) [F.IsFiniteLocallyFreeOfRank d] :
    (rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n))
      (Etale.vectorBundlePurityCompactification S d F)).map
      ((comparison (Scheme.finiteTateCoefficient l E n) _).map
        ((Etale.ordinaryFinitePullback _ (VectorBundleZeroSection.π S d F)).map
          (baseExponentComparison l E n S hS r r' h hA hA' d).hom)) ≫
      vectorIntegration l E n S r hA d F hS =
        vectorIntegration l E n S r' hA' d F hS := by
  sorry

/-- Root-normalized twist comparison, arbitrary scheme pullback, and exponent transitions.
Source: Stacks 03PK and 099R (blueprint: lem-pur-vector-integration-site-comparison).
Proof: finite reduction is induced by root projection after tensoring with A.
Generators determine the comparison, every pullback square, and every exponent
transition. Repeated tensor gives all powers, including the constant zero power.
A common larger exponent compares any two annihilators. No flatness of A is used.
-/
theorem twistCompatibility :
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r : ℕ)
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      Scheme.IsFiniteTateSiteComparison l E n T r hA k (twistComparison l E n T hT r hA k)) ∧
    (∀ (T T' : Scheme.{u}) (v : T' ⟶ T)
      (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
      (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃ (c : (Etale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
            Scheme.finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
        (d : (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).obj
          (Scheme.finiteTateProSheaf l E n T k) ≅ Scheme.finiteTateProSheaf l E n T' k),
      Scheme.IsFiniteTateEtalePullback l E n T v r hA k c ∧
      Scheme.IsFiniteTateProPullback l E n T v k d ∧
      (ProEtale.upperStar (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).mapIso
          (twistComparison l E n T hT r hA k) ≪≫ d =
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) v).app
            (Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T').mapIso c ≪≫
          twistComparison l E n T' hT' r hA k) ∧
    (∀ (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤))) (r r' : ℕ) (_h : r ≤ r')
      (hA : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
      (hA' : ((l ^ (r' + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (k : ℕ),
      ∃! t : Scheme.finiteEtaleTateTwist T (l ^ (r' + 1)) _ hA' k ≅
          Scheme.finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k,
        Scheme.IsFiniteTateEtaleTransition l E n T r r' hA hA' k t ∧
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient l E n)) T).mapIso t ≪≫
            twistComparison l E n T hT r hA k =
            twistComparison l E n T hT r' hA' k) := by
  sorry

/-- Finite-type specialization of the displayed map equations.
Source: the finite-field conventions and the node statement
(blueprint: lem-pur-vector-integration-site-comparison). -/
def FiniteTypeSiteCompatibility (P : WeilConjectures.PurityFiniteSetting.{u})
    (m : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
    letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
    ∃ hS : IsUnit (P.coefficients.l : Γ(S, ⊤)),
      ∀ (r : ℕ)
        (hA : ((P.coefficients.l ^ (r + 1) : ℕ) :
          Scheme.finiteTateCoefficient P.coefficients.l P.extension m) = 0),
      ProjectiveCompatibility P.coefficients.l P.extension m S hS (infinityCartier S) r hA ∧
      IntegrationCompatibility P.coefficients.l P.extension m S hS r hA d F ∧
      ∀ (K : Etale.DerivedCategoryModule
        (Scheme.finiteTateCoefficient P.coefficients.l P.extension m) S)
        (hK : Etale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (Scheme.finiteTateCoefficient P.coefficients.l P.extension m)) S K),
        TensorCompatibility P.coefficients.l P.extension m S hS r hA d F K hK

/-- The exact finite-field, arbitrary positive finite-level specialization, with no
separatedness hypothesis on S. Noetherianity and invertibility of l are consequences.
Source: finite purity conventions and node statement
(blueprint: lem-pur-vector-integration-site-comparison).
Proof: finite type over a field makes S Noetherian. Since l differs from the fixed
characteristic, l is invertible on S. Apply the preceding map equations at every
annihilating exponent and every bounded constructible finite-Tor coefficient.
-/
theorem finiteTypeSiteComparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (m : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (CommRingCat.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] (d : ℕ)
    (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    FiniteTypeSiteCompatibility P m S aS d F := by
  sorry

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
