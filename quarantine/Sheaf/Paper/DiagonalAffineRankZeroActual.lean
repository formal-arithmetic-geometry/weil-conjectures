module

public import Sheaf.Paper.DiagonalAffineTraceSiteData

/-! # Rank-zero diagonal purity and trace normalization
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

/-- At rank zero the actual diagonal purity and smooth trace have their independently
specified identity-pullback, tensor-unit and identity-adjunction coordinates.
Source: original comparison proof step 4, the identity affine tower
(blueprint: lem-pur-diagonal-affine-rank-zero-actual).

Proof: specialize projection_purity_agreement and ordered_integration_transposes to
rank zero. The affine tower is S with identity projection. The empty ordered trace
is the identity and the ordinary source identification is rankZeroOrdinarySource;
its defining heterogeneous equality fixes the identity-pullback tensor-unit map.
The ordinary identity exceptional comparison is rightDerivedUpperShriekIsoOfIso
followed by leftDerivedUpperStarId. Adjoint uniqueness makes this precisely the
transpose of rankZeroOrdinarySupport, the proper identity compact-support map.
The comparison unit gives boundedSiteRho, hence the purity component is the first
component of rankZeroMaps. Apply the inverse exceptional Hom bijection to this
identity: the actual smooth trace is compact-support image followed by its counit.
The proper/open comparison and realization counit identify this composite with the
second component of rankZeroMaps. Naturality gives the formulas for every eK and
annihilator. This uses only the rank-zero identity adjunction, including K=0 and
empty S, and makes no claim about positive-rank integration squares. -/
theorem diagonalAffineRankZeroActual
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K)
    (Ke : Etale.DerivedCategoryModule (projectionSetting F C E n).Coefficient S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (eK : (comparison (projectionSetting F C E n).Coefficient S).obj Ke ≅
      (Scheme.sfIntrinsicDerivedEquivalence S (projectionSetting F C E n).Ring).inverse.obj K)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (projectionSetting F C E n).Coefficient) = 0) :
    RankZeroActual F C E n S aS K hK Ke hKe eK r hA := by
  sorry

end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
