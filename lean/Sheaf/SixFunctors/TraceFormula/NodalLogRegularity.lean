module



public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
import Sheaf.AlgebraicGeometry.LogSmoothLogRegular
import Sheaf.SixFunctors.TraceFormula.NodalEtaleChart
import Sheaf.TraceFormula.NodalDivisorialChart

/-!
# Log regularity of a marked nodal curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI,
Proposition 1.9, printed pp. 70--71 (blueprint: lem-trf-nodal-log-regularity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper flat nodal relative curve with an étale Cartier marking is log regular after
including the vertical boundary. Source: Illusie--Laszlo--Orgogozo, Exposé VI,
Proposition 1.9, printed pp. 70--71 (blueprint: lem-trf-nodal-log-regularity).

Proof: apply the étale local normal-form statement for nodal families. On smooth charts use
 the base chart, and on marked charts adjoin the chart for the Cartier coordinate. On a nodal
 chart use the fine saturated pushout chart whose monoid algebra is `uv = h`. The logarithmic
 smoothness criterion gives log regularity and identifies these charts with the divisorial
 structure of the complement. Glue the local structures and use the density conclusion in
 the logarithmic criterion to obtain that `|D| ∪ f⁻¹(T)` is nowhere dense and that its
 complement defines a divisorial fine saturated log regular pair.
-/
theorem nodal_log_regular
    {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    (f : X ⟶ Y) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hgeom : HasNodalGeometricFibres f)
    (T : Set Y) (hT : IsClosed T)
    (U : Y.Opens) (hU : (U : Set Y) = Tᶜ) (hUdense : DenseRange U.ι)
    (hYlog : IsDivisorialFineSaturatedLogRegularPair Y U U.ι hUdense)
    (hfsmooth : ∀ x : X, f x ∉ T → x ∈ f.smoothLocus)
    (D : Scheme.{u}) (i : D ⟶ X) (hD : IsEffectiveCartierCenter i)
    (hDsmooth : ∀ d : D, i d ∈ f.smoothLocus)
    [Etale (i ≫ f)] :
    IsNowhereDense (Set.range i ∪ f ⁻¹' T) ∧
      ∃ (V : X.Opens) (hV : (V : Set X) = (Set.range i ∪ f ⁻¹' T)ᶜ)
        (hVdense : DenseRange V.ι),
        IsDivisorialFineSaturatedLogRegularPair X V V.ι hVdense := by
  sorry

end AlgebraicGeometry
