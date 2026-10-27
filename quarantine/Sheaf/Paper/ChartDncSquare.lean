/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.GeneralChartComparisons

/-! # Naturality of the normalized chart DNC factor -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The endpoint square for the specified normalized deformation comparison.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-orientation/sk-prop-sp-orientation-charts.proof.md, Steps 2--3
(blueprint: lem-pur-chart-dnc-square).

Proof: cut out the off-diagonal complement so both diagonal centres are Cartesian.
Flat conormal base change identifies the normal map induced by sourceLift and the
base-change map with normalMap: on each affine it sends the degree-one class of a
coordinate difference to the corresponding pulled-back difference. The extended
Rees map has exactly these one- and zero-fibre maps. Apply the endpoint equations
of section-etale restriction to this Rees map, and normalized base compatibility of
the DNC comparison to the Cartesian factor. Cancel the restriction comparison for
the intermediate open neighbourhood. The remaining source comparison is q and the
remaining normal comparison is r, by their definitions; the chosen DNC comparison
is fixed by its endpoint at one. Transport through the site comparisons. The argument
uses the actual normal map and covers rank zero and empty charts. -/
theorem chart_dnc_square (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    delta P aV C ≪≫ r P aV e = q P aV e N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (delta P aV B) := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartComparisons
