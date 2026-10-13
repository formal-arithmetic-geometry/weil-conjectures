module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace CategoryTheory.Over.DescentDatum

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

/-- The chart square is cartesian when its inverse image is the specified source open.

Source: Mathlib's `IsOpenImmersion.isPullback`, the universal property of an open
subscheme (Stacks Project, Tag 01IN). Apply `glued_model_chart_pullback_core` to the
commuting square and the inverse-image equality, then recover `IsPullback` from
its limit cone. The open-cover and local-cartesian hypotheses alone do not imply
this equality; it must be established from the descended overlap construction.
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
    (hcomm : ∀ i, q i ≫ j i = (U i).ι ≫ q₀)
    (hpreimage : q₀ ⁻¹ᵁ (j i).opensRange = U i) :
    IsPullback (q i) (U i).ι (j i) q₀ := by
  have _ := hcover
  obtain ⟨hlimit⟩ := glued_model_chart_pullback_core U W q W₀ q₀ j i hcart
    (hopen i) (hover i) (hcomm i) hpreimage
  exact IsPullback.of_isLimit hlimit

end CategoryTheory.Over.DescentDatum
