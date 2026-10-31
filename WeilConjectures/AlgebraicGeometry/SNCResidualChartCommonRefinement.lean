/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SNCResidualChartData

/-! # Common pointed refinements of residual charts -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.ProEtale

/-- A finite family of residual charts admits a common pointed refinement.
Source: ILO VIII Remark 4.2.2(i), IX Proposition 2.1; Stacks 0A02, 09ZS, 0BND.
(blueprint: lem-sfb-snc-residual-chart-common-refinement).

Proof: form the finite pointed fibre product of the affine charts over Y_I,
choose an affine neighbourhood of the marked point, and shrink its residual
scheme to the connected regular component through that point. Equal labelled
Cartier ideals give unit ratios of their equations. Henselization functoriality
and pointed universal-cover functoriality give compatible maps on the actual
henselian covers and on their reductions, including a common lifted point.
Choose compatible fibre roots of each unit ratio and lift them by normalized
splitting on the common universal cover. Multiply root coordinates by those
unit roots. The defining polynomial relations verify the finite maps, and
power compatibility verifies their transition squares. The full presentation
and localization universal properties give the full and punctured maps;
quotient descent gives the residual maps. Every displayed square follows on
coefficients and root generators. With zero charts choose an ordinary pointed
stratum chart first; with zero labels all root maps are the coefficient maps. -/
theorem exists_sncResidualChart_common_refinement
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
    (I : Finset (Fin a))
    (q : ℕ) (Q : Fin q → SNCResidualChart p C I)
      (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω') ⟶ (sncStratumIdeal C I).subscheme)
      (sv : ∀ d : Fin q,
        Spec (.of Ω') ⟶ Spec (.of ((Q d).B ⧸ Ideal.span (Set.range (Q d).t))))
    (hsv : ∀ d, sv d ≫ (Q d).residualIso.hom ≫ pullback.fst _ _ = s) :
    ∃ (R : SNCResidualChart p C I)
      (sr : Spec (.of Ω') ⟶ Spec (.of (R.B ⧸ Ideal.span (Set.range R.t))))
      (f : ∀ d : Fin q, SNCResidualRefinement (Q d) R)
      (ur : Spec (.of Ω') ⟶ Spec R.H)
      (uv : ∀ d : Fin q, Spec (.of Ω') ⟶ Spec (Q d).H),
      sr ≫ R.residualIso.hom ≫ pullback.fst _ _ = s ∧
      ur ≫ Spec.map R.b = sr ≫ Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span (Set.range R.t)))) ∧
      (∀ d, ur ≫ Spec.map (f d).lift = uv d) ∧
      (∀ d, uv d ≫ Spec.map (Q d).b =
        sv d ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range (Q d).t))))) ∧
      ∀ d, sr ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range R.t)))) ≫ Spec.map (f d).base =
        sv d ≫ Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span (Set.range (Q d).t)))) := by
  sorry

end AlgebraicGeometry.ProEtale
