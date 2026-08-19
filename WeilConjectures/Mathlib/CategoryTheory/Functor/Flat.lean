/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!

# Left exactness of `Lan` along a representably flat functor, into a Grothendieck abelian
category

Mathlib proves that left Kan extension along the opposite of a representably flat functor
preserves finite limits — `CategoryTheory.lan_preservesFiniteLimits_of_flat` — but only
under two hypotheses that the small sites of `WeilConjectures.SixFunctors` do not meet:

* the source and target of `F` must be `SmallCategory`; the small étale site is not even
  *essentially* small, see
  `AlgebraicGeometry.Scheme.not_essentiallySmall_etale`; and
* the coefficient category must be **concrete**, with a forgetful functor preserving limits
  and filtered colimits and reflecting isomorphisms, whereas here it is an arbitrary
  Grothendieck abelian category.

This file redoes that argument with `AB5` in place of concreteness, and with a *cofinality*
hypothesis in place of smallness. The point of the cofinality formulation is that
smallness of the comma categories is not merely unavailable but false in the intended
application, for the same reason `X.Etale` itself is not essentially small: the disjoint
unions `∐_{i : I} X` give a proper class of pairwise non-isomorphic objects. What is true,
and what the plus-construction and the sheafification story already rely on elsewhere in
this repository, is that the comma categories admit a *final functor from an essentially
small category* — the affine slice. That is exactly the hypothesis taken here.

## Main results

- `CategoryTheory.lanEvalIsoColim`: mathlib's `lanEvaluationIsoColim` restated without the
  `SmallCategory` hypotheses on the source and target. The proof is unchanged; the
  smallness in mathlib's version comes from its section variables and is not used.
- `CategoryTheory.hasColimitsOfShape_costructuredArrow_op_of_final`: the colimits computing
  the pointwise left Kan extension exist as soon as the comma categories admit final
  functors from essentially small categories.
- `CategoryTheory.preservesFiniteLimits_op_lan_of_flat_of_final`: the main result.
- `CategoryTheory.preservesFiniteLimits_op_lan_of_flat`: the special case in which the
  comma categories are themselves essentially small.

-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃ u₄

open CategoryTheory Limits Functor

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (A : Type u₃) [Category.{w} A] [Abelian A] [IsGrothendieckAbelian.{w} A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The evaluation of `F.lan` at `X` is the colimit over the costructured arrows over `X`.

This is `CategoryTheory.lanEvaluationIsoColim` with the `SmallCategory` hypotheses on `C`
and `D` dropped: mathlib states it inside a section whose variables force smallness, but
the proof only ever uses that the pointwise left Kan extension exists, which is what
`[∀ X : D, HasColimitsOfShape (CostructuredArrow F X) A]` supplies. -/
noncomputable def lanEvalIsoColim (F : C ⥤ D) (X : D)
    [∀ X : D, HasColimitsOfShape (CostructuredArrow F X) A] :
    F.lan ⋙ (evaluation D A).obj X ≅
      (Functor.whiskeringLeft _ _ A).obj (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
    (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
    (colimit.isColimit _)) (fun {G₁ G₂} φ => by
      apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
      intro T
      have h₁ := fun (G : C ⥤ A) => IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X) (colimit.isColimit _) T
      have h₂ := congr_app (F.lanUnit.naturality φ) T.left
      dsimp at h₁ h₂ ⊢
      simp only [Category.assoc] at h₁ ⊢
      simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
      rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
        ι_colimMap, Functor.whiskerLeft_app]
      rfl)

variable (F : C ⥤ D)

/-- If every comma category `CostructuredArrow F.op K` admits a final functor from an
essentially small category, then the colimits computing the pointwise left Kan extension
along `F.op` exist in a Grothendieck abelian `A`.

Note that this is strictly weaker than asking the comma categories to be essentially small
themselves, and that is the point: for the small étale site they are not. -/
lemma hasColimitsOfShape_costructuredArrow_op_of_final {S : Dᵒᵖ → Type u₄}
    [∀ K, Category.{v₃} (S K)] [∀ K, EssentiallySmall.{w} (S K)]
    (i : ∀ K, S K ⥤ CostructuredArrow F.op K) [∀ K, (i K).Final] (K : Dᵒᵖ) :
    HasColimitsOfShape (CostructuredArrow F.op K) A :=
  letI : HasColimitsOfShape (S K) A := hasColimitsOfShape_of_essentiallySmall.{w} _ _
  Functor.Final.hasColimitsOfShape_of_final (i K)

/-- **Left exactness of the base-change left Kan extension.** If `F` is representably flat
and each comma category `CostructuredArrow F.op K` admits a final functor from an
essentially small *filtered* category, then left Kan extension along `F.op` into a
Grothendieck abelian category preserves finite limits.

The proof is mathlib's, with two substitutions. Concreteness of the coefficient category is
replaced by `AB5`, which is available for small filtered shapes from
`IsGrothendieckAbelian` and is transported to the (large) comma category along the final
functor by `hasExactColimitsOfShape_of_final`. Smallness of the source and target is
replaced by the cofinality hypothesis, which is what makes the colimits exist at all. -/
theorem preservesFiniteLimits_op_lan_of_flat_of_final [RepresentablyFlat F]
    [∀ K : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op K) A] {S : Dᵒᵖ → Type u₄}
    [∀ K, Category.{v₃} (S K)] [∀ K, EssentiallySmall.{w} (S K)] [∀ K, IsFiltered (S K)]
    (i : ∀ K, S K ⥤ CostructuredArrow F.op K) [∀ K, (i K).Final] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) := by
  constructor
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation (F.op.lan : (Cᵒᵖ ⥤ A) ⥤ Dᵒᵖ ⥤ A) J
  intro K
  letI : IsFiltered (CostructuredArrow F.op K) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F K.unop)
  letI : IsFiltered (SmallModel.{w} (S K)) := IsFiltered.of_equivalence (equivSmallModel _)
  letI : HasColimitsOfShape (S K) A := hasColimitsOfShape_of_essentiallySmall.{w} _ _
  letI : HasExactColimitsOfShape (S K) A :=
    HasExactColimitsOfShape.of_domain_equivalence A (equivSmallModel _).symm
  letI : HasExactColimitsOfShape (CostructuredArrow F.op K) A :=
    hasExactColimitsOfShape_of_final A (i K)
  exact preservesLimitsOfShape_of_natIso (lanEvalIsoColim A _ _).symm

/-- The special case of `CategoryTheory.preservesFiniteLimits_op_lan_of_flat_of_final` in
which the comma categories are themselves essentially small, obtained by taking the final
functor to be the identity. Filteredness is then automatic from representable flatness. -/
theorem preservesFiniteLimits_op_lan_of_flat [RepresentablyFlat F]
    [∀ K : Dᵒᵖ, EssentiallySmall.{w} (CostructuredArrow F.op K)]
    [∀ K : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow F.op K) A] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) := by
  letI : ∀ K : Dᵒᵖ, IsFiltered (CostructuredArrow F.op K) := fun K =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F K.unop)
  exact preservesFiniteLimits_op_lan_of_flat_of_final A F (fun K => 𝟭 _)

end CategoryTheory
