module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

/- STATEMENT-DISPUTED: The hypotheses do not specify the descended overlaps or cover V.
Take X = Y = W₀ = Spec k, p = identity, V = Spec k ⨿ Spec k over X by the fold map,
I a singleton, U its first component, W the identity object over Y, q the component
isomorphism, q₀ the fold map, and j the identity. All hypotheses hold. The conclusion
would make U.ι an isomorphism (a pullback of j = identity), although it misses the
second component. Even adding a cover of V and cartesianity for all charts is
insufficient: use two indices for the two components and let both j be identity.
The specified data permit identifying disjoint source charts in the target.
See report.md for the hypothesis-by-hypothesis check and compiled counterexample. -/

/-- Core open-immersion pullback step for a glued chart.

This is the gluing argument needed after restricting the cartesian square to a
single open chart. The open immersion and compatibility equations are intended
to identify the candidate square locally; the full scheme gluing argument is
isolated here so that the chart theorem below only has to apply this core step.
(blueprint: lem-pd-glued-effective-model-chart-pullback-single-core) -/
theorem glued_model_chart_pullback_core
-- STATEMENT-DISPUTED: the stated hypotheses do not force the chart square to
-- be cartesian; a chart may be empty while other charts cover the glued model.
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left) (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : IsOpenImmersion (j i))
    (hover : j i ≫ W₀.hom = (W i).hom)
    (hcomm : q i ≫ j i = (U i).ι ≫ q₀) :
    Nonempty (IsLimit (PullbackCone.mk (q i) (U i).ι hcomm)) := by
  sorry

/-- The pullback property for one chart follows from the local chart-square step.
(blueprint: lem-pd-glued-effective-model-chart-pullback-single) -/
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
  have _ := hcover
  apply IsPullback.mk
  · exact glued_model_chart_pullback_core U W q W₀ q₀ j i hcart (hopen i) (hover i) (hcomm i)
  · exact ⟨hcomm i⟩

end CategoryTheory.Over.DescentDatum
