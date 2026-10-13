module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/-- STATEMENT-DISPUTED: the displayed data do not specify the descended overlaps.

Source: Stacks Project, Tag 0AP4, chart-square verification. The intended proof
identifies the inverse image of each target chart with its source open using the
construction of the descended overlaps, then applies the open-subscheme pullback
criterion indexwise. The displayed hypotheses omit this construction and do not
imply those inverse-image equalities. For a nonempty X, take p and j to be identities,
V = X coproduct X, U its first component, q the component isomorphism, and q₀ the
fold map, with a singleton index. All hypotheses hold, but a cartesian chart square
would make U.ι an isomorphism. Hence no proof exists for the unchanged statement;
the missing gluing compatibility must be supplied in an upstream interface repair.
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
  sorry

end CategoryTheory.Over.DescentDatum
