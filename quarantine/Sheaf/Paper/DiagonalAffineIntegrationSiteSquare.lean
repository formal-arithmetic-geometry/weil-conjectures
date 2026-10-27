module

public import Sheaf.Paper.DiagonalAffineTraceSiteData

/-! # Ordered affine integration under site comparison
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

/-- Ordered coefficient-valued affine integration satisfies the actual proper/open
compact-support comparison square on the ordinary tensor source.
Source: the finite-level vector-integration site comparison, original proof step 3
(blueprint: lem-pur-diagonal-affine-integration-site-square).

Proof: compare the normalized projective-line traces and their coefficient-first
projection formulas. Restrict each line trace by the actual open counit; its
comparison square commutes by openCounitComparison. Paste these squares in the
ordered affine tower. The compact-support composition comparison identifies the
pasted map with the canonical comparison at affineTraceProjection. The ordinary
and pro-etale Tate coefficient descents identify the pasted sources by coefficientIso
and ordinarySourceIso. Compare the actual coefficient-first projections, then invert
the square on the bounded constructible finite-Tor coefficient Ke; uniqueness of the
inverse identifies the pro-etale projectionIso. Tensor the compared traces and apply
the unit-normalized tensor comparison and right unitor. The resulting equation is
exactly IntegrationSiteSquare. ordinaryPlus supplies its boundedness certificate.
For d=0 the pasted tower is the identity. No flatness over the Kummer ring is used,
and zero inputs or the empty base satisfy the same formulas. -/
theorem diagonalAffineIntegrationSiteSquare
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (Ke : Etale.DerivedCategoryModule (Scheme.finiteTateCoefficient C.l E n) S)
    (hKe : finiteTorConstructibleEtale C.l E (n + 1) (Nat.succ_pos n) S Ke)
    (r : ℕ) (hA : ((C.l ^ (r + 1) : ℕ) : (Scheme.finiteTateCoefficient C.l E n)) = 0)
    (d : ℕ) :
    TraceSquare F C E n S aS Ke hKe r hA d := by
  sorry

end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
