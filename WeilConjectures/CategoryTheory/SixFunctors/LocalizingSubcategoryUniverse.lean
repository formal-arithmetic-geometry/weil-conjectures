/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Localizing subcategories and the indexing universe

Source: the nonzero-support argument of
`lem-exc-coproduct-preservation-universe-extension`, applied to the definition of a
localizing subcategory in `sk-def-localizing-closure`
(blueprint: lem-sfb-localizing-subcategory-universe).
-/

@[expose] public section

set_option autoImplicit false

universe u v w w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The nonzero summands of an existing coproduct inject into its endomorphisms. -/
private theorem coproduct_small_support
    {D : Type v} [Category.{w} D] [Preadditive D] [LocallySmall.{u} D]
    {I : Type w₂} (K : I → D) (t : Cofan K) (ht : IsColimit t) :
    Small.{u} {i // ¬ IsZero (K i)} := by
  classical
  let p (i : I) : t.pt ⟶ K i := ht.desc (Cofan.mk (K i) (Pi.single i (𝟙 (K i))))
  have hp (i j : I) : t.inj j ≫ p i = Pi.single (M := fun j ↦ K j ⟶ K i) i (𝟙 (K i)) j :=
    ht.fac (Cofan.mk (K i) (Pi.single i (𝟙 (K i)))) (Discrete.mk j)
  apply small_of_injective (f := fun i : {i // ¬ IsZero (K i)} ↦ p i.val ≫ t.inj i.val)
  intro i j hij
  apply Subtype.ext
  by_contra hne
  have he := congrArg (fun f ↦ t.inj i.val ≫ f ≫ p i.val) hij
  have hi : t.inj i.val ≫ p i.val = 𝟙 (K i.val) := by simp [hp]
  have hj : t.inj i.val ≫ p j.val = 0 := by simp [hp, hne]
  have hid : 𝟙 (K i.val) = 0 := by
    simpa only [← Category.assoc, hi, hj, Category.id_comp, zero_comp] using he
  exact i.property ((IsZero.iff_id_eq_zero _).mpr hid)

-- An existing large coproduct has small nonzero support, by the library's
-- idempotent-endomorphism argument. Dropping its zero summands preserves its vertex.
private theorem closed_coproducts_of_locallySmall
    {C : Type v} [Category.{w} C] [Preadditive C] [LocallySmall.{u} C]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (hP : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
    {I : Type v} (K : I → C) (t : Cofan K) (ht : IsColimit t)
    (hK : ∀ i, P (K i)) : P t.pt := by
  classical
  have : Small.{u} {i // ¬ IsZero (K i)} :=
    coproduct_small_support K t ht
  let J := {i // ¬ IsZero (K i)}
  have : P.IsClosedUnderColimitsOfShape (Discrete (Shrink.{u} J)) := hP _
  have : P.IsClosedUnderColimitsOfShape (Discrete J) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (equivShrink J)).symm
  let r : Cofan (fun i : J ↦ K i.val) := Cofan.mk t.pt (fun i ↦ t.inj i.val)
  have hr : IsColimit r := by
    refine Cofan.IsColimit.mk r (fun s ↦ ht.desc (Cofan.mk s.pt
      (fun i ↦ if hi : ¬ IsZero (K i) then s.inj ⟨i, hi⟩ else 0))) ?_ ?_
    · intro s i
      obtain ⟨i, hi⟩ := i
      change t.ι.app (Discrete.mk i) ≫ _ = _
      rw [ht.fac]
      simp only [Cofan.mk_ι_app, dite_eq_left hi]
    · intro s m hm
      apply ht.hom_ext
      intro ⟨i⟩
      rw [ht.fac]
      by_cases hi : ¬ IsZero (K i)
      · simpa only [r, cofan_mk_inj, Cofan.inj, Cofan.mk_ι_app, dite_eq_left hi]
          using hm ⟨i, hi⟩
      · exact (not_not.mp hi).eq_of_src _ _
  exact P.prop_of_isColimit (J := Discrete J) hr (fun i ↦ hK i.as.val)

/-- Closure under existing coproducts in a universe in which the category is locally
small implies closure under all existing coproducts in the object universe.

Source: the idempotent-endomorphism proof of
`lem-exc-coproduct-preservation-universe-extension` and `sk-def-localizing-closure`
(blueprint: lem-sfb-localizing-subcategory-universe).

Proof: for an existing coproduct, the projection onto a nonzero summand followed by its
inclusion is a nonzero idempotent of the vertex. Distinct summands give distinct
idempotents, so their set is small in the hom universe. Discard the zero summands:
the same vertex is a coproduct of the nonzero summands, since arrows from the omitted
summands are unique. Reindex these summands by a small equivalent type. The assumed
closure puts this vertex in the subcategory. This includes empty and entirely zero
families. The triangulated and replete conditions are unchanged. -/
theorem isLocalizingSubcategory_of_locallySmall
    {C : Type v} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [LocallySmall.{u} C] (P : ObjectProperty C)
    (hP : IsLocalizingSubcategoryOfSize.{u} P) : IsLocalizingSubcategory P := by
  have : P.IsClosedUnderIsomorphisms := hP.2.1
  refine ⟨hP.1, hP.2.1, ?_⟩
  intro I E hE hobj
  have : HasColimit E := hE
  have hsmall (I : Type u) : P.IsClosedUnderColimitsOfShape (Discrete I) := by
    apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
    rintro _ ⟨E', hE'⟩
    exact hP.2.2 E' inferInstance (fun i ↦ hE' ⟨i⟩)
  let t : Cofan (fun i : I ↦ E.obj ⟨i⟩) :=
    (Cocone.precompose (Discrete.natIsoFunctor (F := E)).inv).obj (colimit.cocone E)
  have ht : IsColimit t :=
    (IsColimit.precomposeHomEquiv (Discrete.natIsoFunctor (F := E)).symm _).2
      (colimit.isColimit E)
  exact closed_coproducts_of_locallySmall P hsmall _ t ht hobj

end CategoryTheory
