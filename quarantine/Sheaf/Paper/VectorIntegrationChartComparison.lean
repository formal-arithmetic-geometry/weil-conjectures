module

public import Sheaf.Paper.VectorIntegrationChartCoordinates
import Sheaf.Paper.VectorIntegrationChartTranspose
import Sheaf.Paper.AffineIntegrationExponentTransition

/-! # Vector integration in a linear chart

Source: blueprint sec-smooth-purity/sk-prop-an,
thm-amb-vector-bundle-purity.proof.md, second paragraph.
(blueprint: lem-pur-vector-integration-chart-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

/-- Integration-normalized vector purity agrees on every linear chart with the
ordered affine-line comparison, at every positive coefficient level.
Source: main-20261015, thm-amb-vector-bundle-purity.proof.md, second paragraph
(blueprint: lem-pur-vector-integration-chart-comparison).

Proof:
1. Finite type over k gives a Noetherian base; every open chart is separated finite
   type. The coefficient unit is constructible of Tor interval [0,0].
2. The site-comparison theorem identifies inverse unit-object purity with the actual
   integration transpose. Its coefficient-first projection at the unit is the unitor.
3. In the inverse-frame Cartesian square, ordinary integration restricts to the
   affine-space trace. Compact-support site coherence gives the same restriction
   after comparison. Apply purityTraceTranspose_baseChange to obtain exactly the
   exceptional exchange in restrictedMap, with canonical Tate pullback on its source.
4. The ordered affine integration counit transposes to affineSpacePurityComparison:
   compose the restricted projective-line counits in the fixed coordinate order.
   The exceptional compositor is their right-adjoint conjugate. Its recursion uses
   the actual exceptional image at each stage, with the specified tensor associators.
5. At rank zero this is the identity tower. Empty opens and empty bases have the
   unique maps. The site comparison preserves exponent transitions, so pulling its
   canonical factorwise root comparison through this calculation proves the second
   equation. Any two annihilators compare through a common larger exponent. No
   ramification-divisibility hypothesis or flatness over Z/ell^r is used. -/
theorem vectorIntegration_chart_comparison (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (aZ : Z ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    (d : ℕ) (F : Z.Modules) [F.IsFiniteLocallyFreeOfRank d]
    (U : Z.Opens) (e : VectorBundleZeroSection.Trivialization Z d F U) :
    ChartComparison P Z aZ d F U e := by
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType aZ
  let := (open_geometry P Z aZ U).1
  let := (open_geometry P Z aZ U).2.1
  let := (open_geometry P Z aZ U).2.2
  let : IsNoetherian U.toScheme := isNoetherian_of_locallyOfFiniteType (U.ι ≫ aZ)
  have hr (r : ℕ) (hA : ((P.coefficients.l ^ (r + 1) : ℕ) : Ring P) = 0) :
      restrictedMap P Z aZ d F U e r hA =
        affineTranspose P U.toScheme (U.ι ≫ aZ) d r hA := by
    exact eq_of_heq
      ((restrictedMap_existsUnique P Z aZ d F U e r hA).exists.choose_spec.trans
        (chartTranspose_eq_affine P Z aZ d F U e r hA))
  constructor
  · rw [hr, affineTranspose_unit_coordinates]
    rw [(AffineOrderedIntegration.ordered_integration_transposes P U.toScheme (U.ι ≫ aZ)
      (unitPlus P U.toScheme) (Etale.ordinaryFiniteUnit (Ring P) U.toScheme)
      (unit_properties P U.toScheme).2 (Iso.refl _)).1 d]
    rfl
  · intro r r' h hA hA'
    rw [hr, hr]
    exact affineTranspose_exponent_transition P U.toScheme (U.ι ≫ aZ) d r r' h hA hA'

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
