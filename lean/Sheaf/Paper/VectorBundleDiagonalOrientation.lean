module

public import Sheaf.Paper.PurityDiagonalDualizingObject
public import Sheaf.Paper.VectorIntegrationSiteComparison
public import Sheaf.Paper.VectorBundlePurity
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.Paper.PurityDiagonalBaseChangeCompared
import Sheaf.Paper.PurityDncInvariance
import Sheaf.Paper.CohomologicalSmoothnessTheorem
import Sheaf.Paper.IntegralFinitePullbackComposition
import Sheaf.AlgebraicGeometry.AffineSpaceTopTrace
import Mathlib.CategoryTheory.Adjunction.Basic
import Sheaf.Paper.SmoothPurityMap
import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
import Sheaf.Paper.ExchangeProjectionSuppliedDomains
import Sheaf.Paper.PurTwistSheafLocallyFree
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing

/-! # The diagonal orientation of a vector bundle

Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-vector-bundle.md and its proof
(blueprint: det-sp-orientation-vector-bundle).

The equality is written after inversion: the inverse of the specified diagonal
isomorphism is the transported adjunct of the actual vector integration. This is
an equality in the derived category on the small pro-etale site. The comparison
of sites is the one of lem-pur-vector-integration-site-comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- A rank-d vector-bundle projection has the smooth pure dimension required by
its diagonal orientation. Source: the preparation step of the node proof and
sbc-lem-affine-space-smooth (blueprint: det-sp-orientation-vector-bundle).
Proof: choose the Zariski module frames of def-asd-vector-bundle-zero-section.
On each frame the projection is an isomorphic copy of affine d-space projection,
which is smooth of pure dimension d by sbc-lem-affine-space-smooth. The property
is Zariski local on the target, so it holds globally. The empty cover and rank
zero are included by the same locality and affine-space statements. -/
theorem vectorBundleDiagonalProjection_smooth (S : Scheme.{u}) [IsNoetherian S]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    SmoothOfRelativeDimension d (VectorBundleZeroSection.π S d F) := by
  sorry

/-- The equality of the two specified orientations, in inverse-arrow form.
All scheme hypotheses used to form the arrows are derived from finite type and
the bundle geometry. Normalized root-line pullback presentations are universally
quantified, as in DiagonalOrientationNormalization; they introduce no choice of
orientation. Source: main-20261015, diagonal orientation of a vector bundle
(blueprint: det-sp-orientation-vector-bundle). -/
def VectorBundleDiagonalOrientationConclusion (P : PurityFiniteSetting.{u})
    (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] : Prop :=
  letI : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  letI : IsAffineHom (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).1
  letI : LocallyOfFiniteType (VectorBundleZeroSection.π S d F) :=
    (Etale.vectorIntegration_geometry S d F).2.1
  letI := vectorBundleDiagonalProjection_smooth S d F
  ∀ t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates,
    (P.diagonalDualizingObject d (VectorBundleZeroSection.π S d F) aS).inv =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        (VectorBundleZeroSection.scheme S d F)).mapDerivedCategory.map
          ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t
            (VectorBundleZeroSection.π S d F) (P.diagonalExponent_isUnit aS) d).inv ≫
          (Etale.rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} P.Coefficient)
            (VectorBundleZeroSection.π S d F)).homEquiv _ _
              (Etale.vectorBundleIntegration P.diagonalExponent
                (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
                P.diagonalExponent_annihilates S (P.diagonalExponent_isUnit aS) d F)) ≫
        (P.diagonalDualizingComparison (VectorBundleZeroSection.π S d F)).inv

/-- The diagonal orientation equals inverse integration-transposed vector purity.
The bottom intermediate field is the specified E = Q_l; the fixed setting already
contains n >= 1, the algebraic closure of F_q, and l different from its characteristic.
No absolute separatedness is imposed on S.
Source: main-20261015, sec-smooth-purity/sk-prop-sp-orientation,
sk-prop-sp-orientation-vector-bundle.md
(blueprint: det-sp-orientation-vector-bundle).

Proof:
1. Choose finite-type affine opens of S trivializing F. The bundle projection is
   affine, separated, finite type and smooth of pure dimension d. Finite type
   over the field gives Noetherianity (lem-weil-pbc-finite-type-over-noetherian).
   The affine total-space charts are separated over k; S itself need not be.
2. On each chart form alpha from lem-pur-diagonal-base-change, delta from
   thm-pur-dnc-invariance, and beta from cor-pur-vector-bundle-purity. The given
   diagonal orientation is beta delta alpha^-1. Their base-change clauses and
   lem-weil-pbc-proetale-derived-pullback-composition identify restrictions on
   common affine refinements with these same composites.
3. Apply lem-pur-projection-purity-agreement at the coefficient unit, whose Tor
   amplitude is [0,0]. Its ordered affine comparison is the actual integration
   adjunct: lem-amb-affine-space-top-trace and def-weil-pbc-composite-adjunction
   identify the recursive ordered counit, starting with the identity at d=0.
   def-amb-vector-integration and lem-pur-vector-integration-site-comparison
   identify this map on both sites, with the same normalized Tate pullback.
4. At the coefficient unit, def-pur-smooth-purity-map and def-pur-co-smoothness
   reduce the smooth purity arrow to the inverse orientation. Indeed the unit
   component of def-exchange-projection is the tensor-unit identification; the
   exceptional transpose of its counit is the identity by the adjunction triangle.
   Thus the chartwise inverse orientation is exactly the integration adjunct.
5. The base-change and adjunction compatibilities of cor-pur-vector-bundle-purity
   identify each local adjunct with restriction of the global integration adjunct.
   The comparison of sites identifies the actual integrations and transposes,
   giving exactly the comparison-unit transport displayed in the conclusion.
6. Compose the global orientations to an automorphism of A_V(d)[2d]. Its chart
   restrictions are identities. By lem-pur-twist-sheaf-locally-free the unshifted
   twist is a sheaf. Remove the shift and use lem-weil-pbc-derived-single-fully-faithful.
   Exact pullback and lem-weil-proetale-weakly-etale-localization identify its
   restrictions; lem-pur-sheaf-hom-cover-gluing makes the sheaf map the identity.
   Restore the shift and cancel. This includes empty S, rank zero, and arbitrary
   disconnected or nonreduced S. Inverting gives the displayed inverse-arrow equality. -/
theorem vectorBundleDiagonalOrientation (P : PurityFiniteSetting.{u})
    (_hE : P.extension = ⊥) (S : Scheme.{u}) (aS : S ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS]
    (d : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    P.VectorBundleDiagonalOrientationConclusion S aS d F := by
  sorry

end WeilConjectures.PurityFiniteSetting
