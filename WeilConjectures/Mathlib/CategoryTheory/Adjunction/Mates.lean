/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Coherence of the conjugation bijection, in isomorphism form

Mathlib records the compatibility of `CategoryTheory.conjugateEquiv` with composition, the
unitors, the associator and whiskering as statements about natural *transformations*. Since
`CategoryTheory.conjugateIsoEquiv` is built from `CategoryTheory.conjugateEquiv` on the
`hom` and the `inv`, each of these statements has a counterpart for natural *isomorphisms*,
and it is the latter that one wants when transporting the coherence of a pseudofunctor
`X ↦ F X` from the right adjoints to the left adjoints.

## Main results

- `CategoryTheory.conjugateIsoEquiv_trans`: conjugation turns a composite of natural
  isomorphisms into the composite in the opposite order.
- `CategoryTheory.conjugateIsoEquiv_leftUnitor`,
  `CategoryTheory.conjugateIsoEquiv_rightUnitor`,
  `CategoryTheory.conjugateIsoEquiv_associator`: conjugation carries the unitors and the
  associator of the left adjoints to those of the right adjoints.
- `CategoryTheory.conjugateIsoEquiv_isoWhiskerLeft` and
  `CategoryTheory.conjugateIsoEquiv_isoWhiskerRight`: conjugation exchanges left and right
  whiskering.
-/

@[expose] public section

namespace CategoryTheory


universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

section

variable {L₁ L₂ L₃ : A ⥤ B} {R₁ R₂ R₃ : B ⥤ A}
variable (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- Conjugating the inverse of a natural isomorphism gives the inverse of the conjugate. -/
lemma conjugateIsoEquiv_iso_symm (e : L₂ ≅ L₁) :
    conjugateIsoEquiv adj₂ adj₁ e.symm = (conjugateIsoEquiv adj₁ adj₂ e).symm :=
  rfl

/-- Conjugation turns a composite of natural isomorphisms of left adjoints into the
composite, in the opposite order, of the conjugate natural isomorphisms. -/
lemma conjugateIsoEquiv_trans (e : L₂ ≅ L₁) (e' : L₃ ≅ L₂) :
    conjugateIsoEquiv adj₁ adj₃ (e' ≪≫ e) =
      conjugateIsoEquiv adj₁ adj₂ e ≪≫ conjugateIsoEquiv adj₂ adj₃ e' := by
  ext : 1
  exact (conjugateEquiv_comp adj₁ adj₂ adj₃ e.hom e'.hom).symm

end

/-- Conjugation carries the left unitor of a left adjoint to the right unitor of its right
adjoint. -/
lemma conjugateIsoEquiv_leftUnitor {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateIsoEquiv adj (Adjunction.id.comp adj) L.leftUnitor = R.rightUnitor.symm := by
  ext : 1
  exact conjugateEquiv_leftUnitor_hom adj

/-- Conjugation carries the right unitor of a left adjoint to the left unitor of its right
adjoint. -/
lemma conjugateIsoEquiv_rightUnitor {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) :
    conjugateIsoEquiv adj (adj.comp Adjunction.id) L.rightUnitor = R.leftUnitor.symm := by
  ext : 1
  exact conjugateEquiv_rightUnitor_hom adj

/-- Conjugation carries the associator of three composable left adjoints to the associator
of their right adjoints. -/
lemma conjugateIsoEquiv_associator {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
    {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂) :
    conjugateIsoEquiv (adj₀₁.comp (adj₁₂.comp adj₂₃)) ((adj₀₁.comp adj₁₂).comp adj₂₃)
        (L₀₁.associator L₁₂ L₂₃) = R₃₂.associator R₂₁ R₁₀ := by
  ext : 1
  exact conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃

/-- Conjugation exchanges left whiskering with right whiskering. -/
lemma conjugateIsoEquiv_isoWhiskerLeft {L₁ L₂ : B ⥤ C} {R₁ R₂ : C ⥤ B} {L : A ⥤ B} {R : B ⥤ A}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj.comp adj₁) (adj.comp adj₂) (Functor.isoWhiskerLeft L e) =
      Functor.isoWhiskerRight (conjugateIsoEquiv adj₁ adj₂ e) R := by
  ext : 1
  exact conjugateEquiv_whiskerLeft adj₁ adj₂ adj e.hom

/-- Conjugation exchanges right whiskering with left whiskering. -/
lemma conjugateIsoEquiv_isoWhiskerRight {L₁ L₂ : A ⥤ B} {R₁ R₂ : B ⥤ A} {L : B ⥤ C} {R : C ⥤ B}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj : L ⊣ R) (e : L₂ ≅ L₁) :
    conjugateIsoEquiv (adj₁.comp adj) (adj₂.comp adj) (Functor.isoWhiskerRight e L) =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv adj₁ adj₂ e) := by
  ext : 1
  exact conjugateEquiv_whiskerRight adj₁ adj₂ adj e.hom

end CategoryTheory
