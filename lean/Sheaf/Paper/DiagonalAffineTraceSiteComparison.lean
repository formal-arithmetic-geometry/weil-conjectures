module

public import Sheaf.Paper.DiagonalAffineTraceSiteData
import Sheaf.Paper.DiagonalAffineTraceMapAgreement
import Sheaf.Paper.DiagonalAffineIntegrationSiteSquare
import Sheaf.Paper.DiagonalAffineRankZeroActual

/-! # Diagonal affine trace and finite-level site comparison

Source: sec-smooth-purity/sk-thm-smooth-purity,
cor-pur-dualizing-object-purity.md, Kummer normalization sentence
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace
open AlgebraicGeometry.ProEtale.VectorIntegrationSite

/-- The diagonal/DNC affine purity has the ordered Kummer integration as its trace,
and both the map and its trace agree with the ordinary-etale arrows under the
specified comparisons. Every positive finite level n+1 and annihilator r+1 occurs;
no ramification-index divisibility or flatness over Z/ell^(r+1) is imposed.
Source: main-20261015, cor-pur-dualizing-object-purity.md, normalization sentence
(blueprint: lem-pur-diagonal-affine-trace-site-comparison).

Proof:
1. Apply lem-pur-projection-purity-agreement with Y=S. It identifies the specified
   diagonal/DNC gamma with the ordered affine comparison. The actual integrations
   and their exceptional transposes are identified by
   lem-pur-affine-ordered-integration-transposes: both are the same ordered
   restricted projective-line traces with inverse coefficient-first projection.
   The source reassociation is exactly sourceCoordinates, without a scalar modification.
2. Invert the exceptional Hom bijection of def-weil-exceptional-inverse-image.
   Its inverse sends u to R p_!(u) followed by epsilon. Thus the equality of
   transposes gives s=a^p, with s exactly def-pur-smooth-trace on the original K.
3. For K=C_S K_0, lem-sf-comparison-tor-amplitude preserves bounded constructibility
   and the finite Tor interval. Apply lem-pur-vector-integration-site-comparison
   to the trivial rank-d bundle. Its Tate and tensor comparisons identify the
   sources, its proper-mate/open comparison is beta, and its exceptional
   comparison preserves the counit. It gives eta^p=C_V(eta^e) and
   a^p beta=C_S(a^e). Combine with steps 1 and 2 and transport through the
   canonical intrinsic realization equivalences. Naturality gives the displayed
   formulas for every presentation of the original K.
4. The zero tower is the identity adjunction; its empty ordered counit and hence
   purity and trace are identities after the recorded unit identifications.
   The projective-line comparison gives t_q h_q=1. Its exponent-independence
   clause and the root-power source comparison give all the same equalities for
   every annihilator. The arguments apply at every E and n+1, including ramified
   levels with e not dividing n+1, zero inputs and the empty base. -/
theorem diagonalAffineTraceSiteComparison
    (F : FiniteFieldDatum.{u}) (C : F.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar) [FiniteDimensional (Padic C.l) E]
    (n : ℕ) (S : Scheme.{u}) (aS : S ⟶ Spec (.of F.k))
    [LocallyOfFiniteType aS] [QuasiCompact aS] [IsSeparated aS]
    (K : Scheme.proEtaleDerivedCategory S (projectionSetting F C E n).Ring)
    (hK : finiteTorConstructible C.l E (n + 1) (Nat.succ_pos n) S K) (d : ℕ) :
    Conclusion F C E n S aS K hK d := by
  let : IsNoetherian S := isNoetherian_of_locallyOfFiniteType aS
  unfold Conclusion
  dsimp only
  intro Ke hKe eK r hA
  refine ⟨diagonalAffineTraceMapAgreement F C E n S aS K hK d Ke hKe eK r hA,
    diagonalAffineIntegrationSiteSquare F C E n S aS Ke hKe r hA d, ?_,
    diagonalAffineRankZeroActual F C E n S aS K hK Ke hKe eK r hA⟩
  exact (projectiveComparison C.l E n S
    (ProEtale.AffineLinePurity.primeUnit (projectionSetting F C E n) S aS)
    (infinityCartier S) r hA).2.2

end WeilConjectures.PurityFiniteSetting.DiagonalAffineTrace

