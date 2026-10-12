module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- The pullback property for one chart follows from local cartesian chart data
and the open cover of the glued model.  This is the local chart-square verification
in Stacks Project, Descent, Tag 0AP4.
(blueprint: lem-pd-glued-effective-model-chart-pullback-single)

The proof covers the inverse image of the chosen chart by all glued charts.  On each
piece the assumed cartesian square identifies the piece with the corresponding
intersection; these identifications agree on overlaps by `hcomm`, so the universal
property of the glued inverse image gives the pullback square. -/
theorem glued_model_chart_pullback_single
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left)
    (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : ∀ i, IsOpenImmersion (j i))
    (hcover : ∀ w : W₀.left, ∃ i, ∃ z : (W i).left, j i z = w)
    (hover : ∀ i, j i ≫ W₀.hom = (W i).hom)
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀) :
    IsPullback (q i) (U i).ι (j i) q₀ := by
  sorry

end CategoryTheory.Over.DescentDatum
