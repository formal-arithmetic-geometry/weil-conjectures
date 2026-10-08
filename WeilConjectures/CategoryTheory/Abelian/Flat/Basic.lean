/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!

# Flat objects of a braided closed monoidal category

Four elementary properties of `CategoryTheory.ObjectProperty.flat` that are not part of
`WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`. The first two are used by the
flat separator criterion of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`.

The first one says that in a *closed* monoidal category only left exactness has to be
tracked: `tensorLeft X` is then a left adjoint, so it preserves colimits for free, and a
braiding carries both exactness conditions from `tensorLeft X` to `tensorRight X`.

The second one says that flat objects are stable under coproducts in a Grothendieck
abelian category. This is what makes the functorial flat cover `∐_{g : G ⟶ X} G` attached
to a flat separator `G` flat.

The last two say that a zero object is flat, and that an object with a tensor inverse is
flat, tensoring with it being an equivalence of categories, hence exact.

## Main results

- `CategoryTheory.ObjectProperty.flat_iff_preservesFiniteLimits`: flatness is left
  exactness of tensoring.
- `CategoryTheory.ObjectProperty.flat_coproduct`: a coproduct of flat objects is flat.
- `CategoryTheory.ObjectProperty.flat_of_isZero`: a zero object is flat.
- `CategoryTheory.ObjectProperty.flat_of_tensorIso`: an object with a tensor inverse is
  flat.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.ObjectProperty

variable {A : Type u'} [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

omit [Abelian A] [IsGrothendieckAbelian.{u} A] in
/-- In a braided *closed* monoidal category, flatness is left exactness of tensoring:
`tensorLeft X` is a left adjoint, so it preserves colimits for free, and the braiding
identifies `tensorLeft X` with `tensorRight X`. -/
lemma flat_iff_preservesFiniteLimits (X : A) :
    flat X ↔ PreservesFiniteLimits (tensorLeft X) := by
  refine ⟨fun h ↦ h.1.1, fun h ↦ ⟨⟨h, ?_⟩, ?_, ?_⟩⟩
  · exact inferInstanceAs (PreservesFiniteColimits (tensorLeft X))
  · exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)
  · exact preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)

/-- A coproduct of flat objects of a Grothendieck abelian braided closed monoidal category
is flat.

`curriedTensor A` preserves the coproduct — colimits in `A ⥤ A` are pointwise, and in
each variable tensoring is a left adjoint — so `tensorLeft (∐ f)` is the colimit of the
`tensorLeft (f i)`, that is, the composite of `A ⥤ Discrete I ⥤ A` with
`colim : (Discrete I ⥤ A) ⥤ A`. The first factor is left exact because each
`tensorLeft (f i)` is, and `colim` is left exact by `AB4`. -/
lemma flat_coproduct {I : Type u} (f : I → A) (hf : ∀ i, flat (f i)) :
    flat (∐ f) := by
  have (i : I) : PreservesFiniteLimits (tensorLeft (f i)) :=
    (flat_iff_preservesFiniteLimits (f i)).1 (hf i)
  rw [flat_iff_preservesFiniteLimits]
  have : PreservesColimit (Discrete.functor f) (curriedTensor A) :=
    MonoidalCategory.Limits.preservesCoLimit_curriedTensor _
  have e : tensorLeft (∐ f) ≅ (Discrete.functor f ⋙ curriedTensor A).flip ⋙ colim :=
    preservesColimitIso (curriedTensor A) (Discrete.functor f) ≪≫ colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((Discrete.functor f ⋙ curriedTensor A).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (f j.as))))
  exact preservesFiniteLimits_of_natIso e.symm

omit [IsGrothendieckAbelian.{u} A] [BraidedCategory A] [MonoidalClosed A] in
/-- A zero object `Z` is flat: tensoring with it is the zero functor, which is exact. -/
lemma flat_of_isZero [MonoidalPreadditive A] {Z : A} (hZ : IsZero Z) : flat Z := by
  have h (W : A) : IsZero (Z ⊗ W) ∧ IsZero (W ⊗ Z) :=
    ⟨(IsZero.iff_id_eq_zero _).2 (by
      rw [← id_whiskerRight, hZ.eq_of_src (𝟙 Z) 0, MonoidalPreadditive.zero_whiskerRight]),
    (IsZero.iff_id_eq_zero _).2 (by
      rw [← whiskerLeft_id, hZ.eq_of_src (𝟙 Z) 0, MonoidalPreadditive.whiskerLeft_zero])⟩
  have hL : IsZero (tensorLeft Z) := Functor.isZero _ fun W ↦ (h W).1
  have hR : IsZero (tensorRight Z) := Functor.isZero _ fun W ↦ (h W).2
  have := (tensorLeft Z).preservesLimitsOfSize_of_isZero hL
  have := (tensorLeft Z).preservesColimitsOfSize_of_isZero hL
  have := (tensorRight Z).preservesLimitsOfSize_of_isZero hR
  have := (tensorRight Z).preservesColimitsOfSize_of_isZero hR
  exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
    (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

omit [Abelian A] [IsGrothendieckAbelian.{u} A] [MonoidalClosed A] in
/-- An object `X` with a tensor inverse, `X ⊗ Y ≅ 𝟙`, is flat: `tensorLeft X` is an
equivalence, with inverse `tensorLeft Y`, so it is exact, and the braiding identifies
`tensorLeft X` with `tensorRight X`. -/
lemma flat_of_tensorIso {X Y : A} (e : X ⊗ Y ≅ 𝟙_ A) : flat X := by
  let E : A ≌ A := .mk (tensorLeft X) (tensorLeft Y)
    ((leftUnitorNatIso A).symm ≪≫ (curriedTensor A).mapIso (β_ Y X ≪≫ e).symm ≪≫
      tensorLeftTensor Y X)
    ((tensorLeftTensor X Y).symm ≪≫ (curriedTensor A).mapIso e ≪≫ leftUnitorNatIso A)
  have : (tensorLeft X).IsEquivalence := E.isEquivalence_functor
  exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
    preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X),
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight X)⟩

end CategoryTheory.ObjectProperty
