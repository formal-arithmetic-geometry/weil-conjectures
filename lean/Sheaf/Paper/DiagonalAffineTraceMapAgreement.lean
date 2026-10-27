module

public import Sheaf.Paper.DiagonalAffineTraceSiteData

/-! # Actual diagonal purity and trace in comparison coordinates
Source: sec-smooth-purity/sk-thm-smooth-purity,
cor-pur-dualizing-object-purity.md, Kummer normalization sentence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
open AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The original intrinsic diagonal purity and coefficient-valued smooth trace agree
with the transported ordinary transpose and ordered pro-etale integration.
This is the two-map clause only; it asserts neither the integration site square,
the projective normalization, nor the independent rank-zero unit coordinates.
Source: the affine-model agreement, original comparison proof steps 1--3
(blueprint: lem-pur-diagonal-affine-map-agreement).

Proof: projection_purity_agreement identifies the actual diagonal map with the
ordered affine comparison. Evaluate projectionAffineIntrinsic's unique specification
at the given ordinary presentation. ordered_integration_transposes identifies that
comparison with the transpose of the ordered integration. The coefficient root-power
transition from the diagonal exponent to r is exponentIso; its tensor, pullback and
shift identifications give exactly sourceCoordinates. The finite-level site comparison
identifies the ordinary transpose with the pro-etale one through boundedSiteRho.
Apply the inverse exceptional Hom bijection, u ↦ Rp_!(u) followed by the counit,
to obtain the trace identity. The support realization comparison and the realization
counit yield precisely the second component of transportedMaps. Naturality transports
both equations through eK and applies to every presentation, including zero objects.
The root-power comparisons are natural for either order of the two exponents, so the
argument also applies at ramified levels and at every annihilating exponent. -/
theorem diagonalAffineTraceMapAgreement
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    MapAgreement F C E n S aS K hK d Ke hKe eK r hA := by
  sorry

end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
