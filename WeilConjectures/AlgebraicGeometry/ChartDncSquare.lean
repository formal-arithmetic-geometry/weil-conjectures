/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralChartComparisons
import WeilConjectures.AlgebraicGeometry.PuritySectionEtaleRestriction
import WeilConjectures.AlgebraicGeometry.DiagonalEtaleSourceEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalEtaleNormalEndpoint

/-! # Naturality of the normalized chart DNC comparison

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 3; parent comparison proof Steps 6--7.
(blueprint: lem-pur-chart-dnc-square).

The comparison uses the actual source and normal maps of an etale chart morphism,
with the canonical etale/pro-etale transports and normalized compact support.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

private theorem span_square {C : Type*} [Category C]
    {T Y Z X NT NY NZ NX : C}
    (a : T ≅ Y) (b : T ≅ Z) (c : X ≅ Z)
    (an : NT ≅ NY) (bn : NT ≅ NZ) (cn : NX ≅ NZ)
    (dt : T ≅ NT) (dy : Y ≅ NY) (dz : Z ≅ NZ) (dx : X ≅ NX)
    (ha : dt.hom ≫ an.hom = a.hom ≫ dy.hom)
    (hb : dt.hom ≫ bn.hom = b.hom ≫ dz.hom)
    (hc : dx.hom ≫ cn.hom = c.hom ≫ dz.hom) :
    dy.hom ≫ (an.inv ≫ bn.hom ≫ cn.inv) =
      (a.inv ≫ b.hom ≫ c.inv) ≫ dx.hom := by
  have ha' : dy.hom ≫ an.inv = a.inv ≫ dt.hom := by
    apply (a.eq_inv_comp).2
    rw [← Category.assoc, ← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc' : dz.hom ≫ cn.inv = c.inv ≫ dx.hom := by
    apply (c.eq_inv_comp).2
    rw [← Category.assoc, ← hc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    _ = a.inv ≫ dt.hom ≫ bn.hom ≫ cn.inv := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ bn.hom ≫ cn.inv) ha'
    _ = a.inv ≫ b.hom ≫ dz.hom ≫ cn.inv := by
      simpa only [Category.assoc] using congrArg (fun k ↦ a.inv ≫ k ≫ cn.inv) hb
    _ = _ := by rw [hc']; simp only [Category.assoc]

/-- The normalized DNC comparison commutes with the canonical etale chart comparisons.
Source: orientation-charts proof Step 3 and parent comparison proof Steps 6--7.
(blueprint: lem-pur-chart-dnc-square).

Proof: remove the off-diagonal complement so that both diagonal centres are Cartesian.
Flat conormal base change identifies the normal map induced by sourceLift and the
base-change map with normalMap: on each affine open, a degree-one coordinate difference
is sent to its pulled-back difference. The extended Rees map has exactly these maps on
its one and zero fibres. Apply the endpoint equations of section-etale restriction to
this Rees map, and normalized base compatibility of the DNC comparison to the Cartesian
factor. Cancel the restriction comparison for the intermediate open neighbourhood. By
definition, the remaining source comparison is q and the remaining normal comparison
is r. The DNC comparison is fixed by its endpoint at one. Transport the equation through
the canonical site comparisons. The same argument covers rank zero and empty charts. -/
theorem chart_dnc_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    delta P aV C ≪≫ r P aV e = q P aV e N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (delta P aV B) := by
  classical
  let := P.noetherian (C.proj ≫ aV)
  obtain ⟨D⟩ := DiagonalEtaleComparison.centreSpan_nonempty d B.proj C.proj
    e.hom e.over_eq
  have he : e.hom ≫ (B.proj ≫ aV) = C.proj ≫ aV := by
    rw [← Category.assoc, e.over_eq]
  have ha := ((SectionRestriction.coherence P).2.2.1 C.X (C.proj ≫ aV) d
    D.pair (DiagonalEtaleComparison.diagonalPair d C.proj) D.left).2.2
  have hb := ((SectionRestriction.coherence P).2.2.1 C.X (C.proj ≫ aV) d
    D.pair (DiagonalEtaleComparison.basePair d B.proj e.hom) D.right).2.2
  have hc := ((SectionRestriction.coherence P).2.2.2.1 B.X C.X
    (B.proj ≫ aV) (C.proj ≫ aV) e.hom he d
    (DiagonalEtaleComparison.diagonalPair d B.proj)
    (DiagonalEtaleComparison.basePair d B.proj e.hom)
    (DiagonalEtaleComparison.baseSquare d B.proj e.hom)).2.2
  have hs := DiagonalEtaleComparison.span_source_endpoint P d B.proj C.proj aV
    e.hom e.over_eq N D
  have hn := DiagonalEtaleComparison.span_normal_endpoint P d B.proj C.proj aV
    e.hom e.over_eq D
  have hδ (A : Chart V d) : delta P aV A =
      SectionRestriction.delta P (A.proj ≫ aV)
        (DiagonalEtaleComparison.diagonalPair d A.proj) := by
    apply (Dnc.existsUnique_dncInvariance P d _ (A.proj ≫ aV) _
      (CategoryTheory.Limits.pullback.diagonal_fst A.proj)).unique
    · exact (Dnc.existsUnique_dncInvariance P d _ (A.proj ≫ aV) _
        (CategoryTheory.Limits.pullback.diagonal_fst A.proj)).exists.choose_spec
    · exact (Classical.choose_spec (Dnc.existsUnique_dncInvariance P d _
        (A.proj ≫ aV) _ (CategoryTheory.Limits.pullback.diagonal_fst A.proj))).1
  rw [hδ C, hδ B]
  apply Iso.ext
  change _ ≫ (DiagonalEtaleComparison.normal P d B.proj C.proj aV
    e.hom e.over_eq).hom =
    (DiagonalEtaleComparison.source P d B.proj C.proj aV e.hom e.over_eq N).hom ≫ _
  rw [← hs, ← hn]
  exact span_square _ _ _ _ _ _ _ _ _ _
    (congrArg Iso.hom ha) (congrArg Iso.hom hb) (congrArg Iso.hom hc)

end WeilConjectures.PurityFiniteSetting.ChartComparisons
