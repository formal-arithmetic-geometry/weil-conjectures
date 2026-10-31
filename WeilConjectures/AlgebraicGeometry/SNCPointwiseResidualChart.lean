/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SNCResidualChartData

/-! # Pointwise henselian SNC residual charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- Every geometric stratum point has a henselian residual chart above it.
Source: ILO VIII Remark 4.2.2(i), IX Proposition 2.1; Stacks 0A02, 09ZS.
(blueprint: lem-sfb-snc-pointwise-residual-chart).

Proof: choose a labelled affine stratum chart containing the point. Its residual
ring is nonzero and connected. Choose a geometric point on that residual scheme,
henselize its labelled ideal and lift the pointed finite-etale cover system.
The resulting filtered ring is ind-etale and henselian along the residual ideal,
and its residual spectrum is the pointed universal cover. Regular-stage ascent
and the henselian root-domain theorem give domains and nonzero parameter products
at every finite root level and at the full level. Their spectra and punctures are
nonempty connected affine schemes. The punctured root-cover theorem gives the
canonical maps, transition laws, colimit properties and finite/pro-etale covers.
Lift compatible primitive fibre roots to the henselization using normalized pointed
splitting. Restrict the affine chart residual isomorphism to the stratum open to
obtain the required residual point. The empty-label case is the identity pair
henselization and the order-one case is substitution of the original equations. -/
theorem exists_sncResidualChart_at
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    (Y : Scheme.{u}) (y : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (hY : IsRegularScheme Y) (D : Y.IdealSheafData)
    (hD : IsStrictNormalCrossingsBoundary D)
    (a : ℕ) (C : Fin a → Y.IdealSheafData)
    (hC : Function.Injective (fun i ↦ (C i).support) ∧
      (∀ i, IsIntegral (C i).subscheme ∧ IsRegularScheme (C i).subscheme) ∧
      D.support = ⨆ i, (C i).support ∧
      ∀ s : Finset (Fin a), ∀ z : (⨆ i ∈ s, C i).subscheme,
        IsRegularScheme (⨆ i ∈ s, C i).subscheme ∧
        ringKrullDim (Y.presheaf.stalk ((⨆ i ∈ s, C i).subschemeι z)) =
          ringKrullDim ((⨆ i ∈ s, C i).subscheme.presheaf.stalk z) + (s.card : ℕ))
    (I : Finset (Fin a)) (z : (sncStratumIdeal C I).subscheme) :
    ∃ (Q : SNCResidualChart p C I)
      (w : Spec (.of (Q.B ⧸ Ideal.span (Set.range Q.t)))),
      (Q.residualIso.hom ≫ pullback.fst _ _) w = z := by
  sorry

end AlgebraicGeometry.ProEtale
