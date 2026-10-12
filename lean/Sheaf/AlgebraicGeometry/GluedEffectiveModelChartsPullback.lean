module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.GluedEffectiveModelChartPullbackSingle

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The local chart squares are cartesian after the gluing data is constructed.
(blueprint: lem-pd-glued-effective-model-charts-pullback) -/
theorem glued_model_chart_pullbacks
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (hcart : ∀ i, IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀) :
    ∀ i, IsPullback (q i) (U i).ι (j i) q₀ := by
  intro i
  exact glued_model_chart_pullback_single U W q W₀ q₀ j i (hcart i) hopen hcover hover hcomm

end CategoryTheory.Over.DescentDatum
