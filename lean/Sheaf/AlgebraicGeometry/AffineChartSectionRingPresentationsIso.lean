module

public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
/-- The initial upper-tail chart projection is an isomorphism.
Source: Stacks Project, Tag 01ZR. (blueprint: new-affine-chart-section-ring-presentations-iso).

Proof: the representative of the initial antisymmetrized upper-tail index is the
subtype `⟨j, le_rfl⟩`. Its transition morphism is therefore the identity of
`Spec (R.obj j)`, by functoriality of `R.map` and `Scheme.Spec.map`. The
pullback of an identity morphism is an isomorphism, and `pullback.snd` is the
corresponding projection, so typeclass transport gives the asserted `IsIso`. -/
theorem affine_chart_section_ring_presentations_iso
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (j : I) {A : Scheme.{u}}
    (g : A ⟶ Spec (R.obj j)) :
    IsIso (pullback.snd (Spec.map (R.map (homOfLE
      ((OrderEmbedding.ofAntisymmetrization (α := {k : I // j ≤ k})).monotone.functor.obj
        (toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k}))).property))) g) := by
  sorry
end AlgebraicGeometry
