module

public import Sheaf.Paper.DiagonalDncChartNormalization
public import Sheaf.Paper.AffineTargetDiagonalDnc

/-! # Canonical diagonal assembly data for target-open descent

Source: sec-smooth-purity/sk-prop-sp-orientation, chart proof, Steps 1--4.
(blueprint: def-pur-chart-diagonal-assembly-data).

These abbreviations re-export the published constructions without copying them.
They assert no chart-normalization or affine-target DNC theorem conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

/-- The canonical alpha-inverse, delta, beta composite, with its original hypotheses.
Source: chart proof, Steps 3--4
(blueprint: def-pur-chart-diagonal-assembly-data). -/
abbrev chartDiagonalAssemblyData (P : PurityFiniteSetting.{u})
    {U V : Scheme.{u}} (d : ℕ) (h : U ⟶ V)
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aV : V ⟶ Spec (.of P.field.k)) [IsSeparated (h ≫ aV)]
    [LocallyOfFiniteType aV] [QuasiCompact aV]
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) :=
  P.chartDiagonalAssembly d h aV t

/-- The actual ordinary smooth base-change isomorphism, including coefficient units.
Source: chart proof, Step 3 and its target-open restriction
(blueprint: def-pur-chart-diagonal-assembly-data). -/
abbrev chartOrdinaryBaseChangeData (P : PurityFiniteSetting.{u})
    {X Y X' Y' : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (b : Y' ⟶ Y) (f' : X' ⟶ Y') (a : X' ⟶ X)
    [HasCompactification f'] [QuasiCompact f'] (sq : IsPullback a f' f b) :=
  P.chartOrdinaryBaseChange d f aY b f' a sq

/-- The existing instance dictionary on one affine target and its actual self-product.
This is data to state restriction formulas, with no assertion that it is inhabited.
Source: chart proof, Step 1 and affine-target restriction
(blueprint: def-pur-chart-diagonal-assembly-data). -/
abbrev ChartAffineDiagonalGeometryData (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (aY : Y ⟶ Spec (.of P.field.k)) (d : ℕ) (V : Y.affineOpens) :=
  P.AffineDiagonalGeometry f aY d V

end WeilConjectures.PurityFiniteSetting
