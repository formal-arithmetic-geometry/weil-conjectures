module

public import Sheaf.Paper.ChartDncVectorFactorData

/-! # A compatibility step in the etale-chart orientation argument -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartFactors

/-- Compatibility of the integration adjoints along the actual differential-normal
square. This states the forward transpose equation; inversion of the two integration
orientations is left to its consumer.
Source: blueprint latest, sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 4, first sentence
(blueprint: lem-pur-chart-integration-adjoints).
Proof: the graded conormal pullback sends [a] tensor y to [e*a y]. The canonical
normal models therefore identify the displayed normalMap with the linear pullback
of the affine diagonal normal bundle, preserving projections and augmentations.
Vector-bundle purity supplies the equation E e*gamma_A = gamma_U tau for the
actual integration transpose gamma. Pull this equation along the zero section and
use normalMap z_U = z_A e. The inverse exceptional exchange restricted to zero is
exactly normal, by smooth base-change and normalized etale locality. The inverse
of beta is gamma transported through the canonical normal model. The resulting
equation is beta_U inverse followed by normal = inverse Tate followed by
e*beta_A inverse. The ordinary/pro-etale integration-site comparison preserves
the trace, its transpose, and the pullback constraints, so it gives these specified
maps. Linear trace invariance makes the calculation independent of frames.
In rank zero use the identity-adjunction trace; on an empty source the morphisms
are unique. No DNC map or choice of a coefficient-line orientation is used. -/
theorem chart_integration_adjoints (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}} [IsAffine Y]
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  letI := P.noetherian (h ≫ aY)
  (beta P d h aY N).inv ≫ (normal P d h aY e w).hom =
      (tate P d aY e t).inv ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.map
          (beta P d p aY N).inv := by sorry

end WeilConjectures.PurityFiniteSetting.ChartFactors
