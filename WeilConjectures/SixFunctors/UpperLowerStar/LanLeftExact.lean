/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

/-!

# Left exactness of the base-change `Lan` on the small étale site, reduced to one input

`AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian`
(`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension`) is sorried. This
file records what is actually left of it: **one** hypothesis, namely that the colimits
computing the pointwise left Kan extension exist.

Everything else is already available on `master`:

* `AlgebraicGeometry.Etale.representablyFlat_overPullback` — base change along an arbitrary
  `g : Z ⟶ Y` is representably flat, because the small étale site has finite limits and
  base change preserves them. This is proved, not assumed.
* `AB5` for the coefficient category, from `IsGrothendieckAbelian`.
* `CategoryTheory.preservesFiniteLimits_op_lan_of_flat_of_final`, which assembles the two.

So the `sorry` reduces to
`[∀ K, HasColimitsOfShape (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op K) A]`,
and that is *the same input* as the sorried
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`: a left Kan
extension along `F.op` exists pointwise exactly when those colimits do. The two sorries
have one primitive obligation between them, not two.

That obligation cannot be discharged by essential smallness of the comma categories,
because they are not essentially small — the `∐_{i : I} X` argument of
`AlgebraicGeometry.Scheme.not_essentiallySmall_etale` applies to them verbatim. It has to
come from a final functor out of an essentially small category, i.e. from the affine slice,
which is the same reduction the sheafification story uses.

## Main results

- `AlgebraicGeometry.Etale.hasLeftKanExtension_op_overPullback_of_hasColimitsOfShape`: the
  sorried `hasLeftKanExtension_op_overPullback`, conditional on that one input. This one is
  `sorryAx`-free, which is what pins the reduction down.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_op_lan_overPullback_of_final`:
  the sorried left-exactness statement, conditional on the same input.

## A note on axioms

`preservesFiniteLimits_op_lan_overPullback_of_final` still reports `sorryAx`, and it is
worth being precise about why, because it is *not* a gap in its proof. Its statement
mentions `F.op.lan`, and `Functor.lan` takes the existence of the Kan extension as an
instance argument, which instance search discharges with the sorried
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`. A
`Lean.collectAxioms` root walk confirms that this is the **only** `sorry` root reached, and
that it is the same single root reached by the sorried statement being reduced. The
companion `hasLeftKanExtension_op_overPullback_of_hasColimitsOfShape` below mentions the
class rather than `Functor.lan`, so it needs no such instance and is `sorryAx`-free; that is
the declaration that actually certifies the reduction.

-/

@[expose] public section

universe u u' v v'

open CategoryTheory Limits Functor AlgebraicGeometry MorphismProperty

namespace AlgebraicGeometry.Etale

/-- The sorried `CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`,
specialised to `@Etale` and made conditional on the colimits that compute the pointwise
left Kan extension. `sorryAx`-free: the existence of the Kan extension follows from those
colimits through the pointwise Kan extension, with nothing else assumed.

The proof term is deliberately explicit. Writing `inferInstance` here also typechecks, but
instance search then discharges the goal with the *sorried* global instance
`CategoryTheory.GrothendieckTopology.hasLeftKanExtension_op_overPullback`, and the result
reports `sorryAx` — which would make this declaration certify nothing. -/
theorem hasLeftKanExtension_op_overPullback_of_hasColimitsOfShape
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [∀ K : Z.Etaleᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op K) A]
    (G : Y.Etaleᵒᵖ ⥤ A) :
    (MorphismProperty.Over.pullback @Etale ⊤ g).op.HasLeftKanExtension G :=
  (Functor.pointwiseLeftKanExtensionIsPointwiseLeftKanExtension _ G).hasLeftKanExtension

/-- Left exactness of the base-change left Kan extension on the small étale site, given
that the colimits computing it exist and are approximated by an essentially small filtered
category. See the module docstring for why this still reports `sorryAx`. -/
theorem preservesFiniteLimits_op_lan_overPullback_of_final
    (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    [∀ K : Z.Etaleᵒᵖ,
      HasColimitsOfShape (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op K) A]
    {S : Z.Etaleᵒᵖ → Type v} [∀ K, Category.{v'} (S K)] [∀ K, EssentiallySmall.{u} (S K)]
    [∀ K, IsFiltered (S K)]
    (i : ∀ K, S K ⥤ CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ g).op K)
    [∀ K, (i K).Final] :
    PreservesFiniteLimits
      ((MorphismProperty.Over.pullback @Etale ⊤ g).op.lan : (Y.Etaleᵒᵖ ⥤ A) ⥤ Z.Etaleᵒᵖ ⥤ A) :=
  preservesFiniteLimits_op_lan_of_flat_of_final A _ i

end AlgebraicGeometry.Etale
