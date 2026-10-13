module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.OpenImmersion

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

/-- Core open-immersion pullback step with the necessary inverse-image condition.

Source: Mathlib's `IsOpenImmersion.isPullback`, the universal property of an open
subscheme (Stacks Project, Tag 01IN). The range of the inclusion of `U i` is `U i`.
The inverse-image condition therefore identifies this range with the inverse image
of the range of `j i`. The commuting square of open immersions is consequently a
pullback; its limit cone gives the conclusion. The local cartesian hypothesis is
retained for compatibility but is not needed for this argument.
(blueprint: lem-pd-glued-effective-model-chart-pullback-single-core) -/
theorem glued_model_chart_pullback_core
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    {I : Type u} (U : I → V.left.Opens) (W : I → Over Y)
    (q : ∀ i, (U i).toScheme ⟶ (W i).left)
    (W₀ : Over Y) (q₀ : V.left ⟶ W₀.left)
    (j : ∀ i, (W i).left ⟶ W₀.left) (i : I)
    (hcart : IsPullback (q i) ((U i).ι ≫ V.hom) (W i).hom p)
    (hopen : IsOpenImmersion (j i))
    (hover : j i ≫ W₀.hom = (W i).hom)
    (hcomm : q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    Nonempty (IsLimit (PullbackCone.mk (q i) (U i).ι hcomm)) := by
  have _ := hcart
  have _ := hover
  have h : IsPullback (q i) (U i).ι (j i) q₀ :=
    IsOpenImmersion.isPullback _ _ _ _ hcomm.symm
      (by simpa only [Scheme.Opens.opensRange_ι] using hpreimage)
  exact h.isLimit'

/-- STATEMENT-DISPUTED: the inverse image of a target chart need not be the source chart.

Source: Stacks Project, Tag 0AP4, chart-square verification. The intended argument
identifies `q₀ ⁻¹ᵁ (j i).opensRange` with `U i`, then applies the universal property
of open subschemes, as proved in `glued_model_chart_pullback_core`. The displayed
hypotheses do not imply that identification: the two-component counterexample above
satisfies them all. Thus there is no valid proof in words for this statement as written;
the missing compatibility of descended overlaps must be supplied upstream.
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
  sorry

end CategoryTheory.Over.DescentDatum
