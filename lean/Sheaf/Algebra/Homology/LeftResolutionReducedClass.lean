/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Mathlib.Algebra.Homology.LeftResolution.Reduced

import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Reduced left-resolution datum from a class of covers

Source: blueprint `main-20261015`,
`sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`,
first three sentences (blueprint: lem-sfb-left-resolution-reduced-class).
This stage-2 module records the statement for independent compilation.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian

set_option autoImplicit false

set_option linter.unusedVariables false in
/--
Let `A` be abelian and let `F` be a class containing a zero object and closed under
isomorphisms, finite biproducts, and retracts.  A functorial epimorphic cover by `F`
can be reduced to a zero-morphism-preserving cover functor whose source is a full,
faithful additive subcategory of `A` on objects of `F`.

Source: blueprint `main-20261015`,
`sec-proetale-coefficients/sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`,
first three sentences (blueprint: lem-sfb-left-resolution-reduced-class).  The proof
uses the full subcategory on `F`, abelian idempotent completeness, and
`CategoryTheory.Abelian.LeftResolution.reduced` from
`Mathlib/Algebra/Homology/LeftResolution/Reduced.lean`.

Proof:
1. Take the full subcategory of `A` on the objects satisfying `F`.  The zero-object
   and finite-biproduct closure give a zero object and finite coproducts there, and
   fullness gives a fully faithful additive inclusion.  Splitting an idempotent in
   `A` and using retract closure of `F` shows that this subcategory is idempotent
   complete.
2. Regard `P` as a functor to this full subcategory and `ε` as its epimorphic natural
   transformation.  Apply the reduced left-resolution construction, which supplies
   a zero-morphism-preserving functor `Q` and the epimorphic natural transformation
   `π` in the conclusion.
-/
theorem leftResolution_reduced_class
    (A : Type u) [Category.{v} A] [Abelian A]
    (F : ObjectProperty A)
    (P : A ⥤ A) (ε : P ⟶ 𝟭 A)
    (hF_zero : ∃ Z : A, IsZero Z ∧ F Z)
    (hF_iso : ∀ {X Y : A}, F X → (X ≅ Y) → F Y)
    (hF_biproduct : ∀ (X Y : A), F X → F Y → F (X ⊞ Y))
    (hF_retract : ∀ {X Y : A} (i : X ⟶ Y) (e : Y ⟶ X),
      i ≫ e = 𝟙 X → F Y → F X)
    (hP : ∀ X : A, F (P.obj X))
    (hε : ∀ X : A, Epi (ε.app X)) :
    ∃ (C : Type u) (cC : Category.{v} C) (pC : @Preadditive C cC)
      (zC : @HasZeroObject C cC) (fcC : @HasFiniteCoproducts C cC)
      (zmC : @HasZeroMorphisms C cC)
      (ι : @CategoryTheory.Functor C cC A (inferInstance : Category.{v} A)),
      @Functor.Full C cC A (inferInstance : Category.{v} A) ι ∧
      @Functor.Faithful C cC A (inferInstance : Category.{v} A) ι ∧
      @Functor.Additive C A cC (inferInstance : Category.{v} A) pC
        (inferInstance : Preadditive A) ι ∧
      (∀ X : C, F (ι.obj X)) ∧
      ∃ (Q : @CategoryTheory.Functor A (inferInstance : Category.{v} A) C cC)
        (zQ : @Functor.PreservesZeroMorphisms A (inferInstance : Category.{v} A) C cC
          (inferInstance : HasZeroMorphisms A) zmC Q)
        (π : @NatTrans A (inferInstance : Category.{v} A) A (inferInstance : Category.{v} A)
          (Q ⋙ ι) (𝟭 A)),
        ∀ X : A, Epi (π.app X) := by
  classical
  let : F.ContainsZero := ⟨hF_zero⟩
  let : F.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hF_iso h e⟩
  let : F.IsClosedUnderBinaryCoproducts := .mk' (by
    rintro _ ⟨D, hD⟩
    exact hF_iso
      (hF_biproduct _ _ (hD ⟨WalkingPair.left⟩) (hD ⟨WalkingPair.right⟩))
      (biprod.isoCoprod _ _ ≪≫ (HasColimit.isoOfNatIso (diagramIsoPair D)).symm))
  let : F.IsClosedUnderFiniteCoproducts := .mk'
  let : IsIdempotentComplete F.FullSubcategory := ⟨by
    intro X p hp
    obtain ⟨Y, i, e, hie, hei⟩ :=
      IsIdempotentComplete.idempotents_split X.obj p.hom (F.ι.congr_map hp)
    refine ⟨⟨Y, hF_retract i e hie X.property⟩,
      ObjectProperty.homMk i, ObjectProperty.homMk e, ?_, ?_⟩
    · exact ObjectProperty.hom_ext _ hie
    · exact ObjectProperty.hom_ext _ hei⟩
  let Λ : LeftResolution F.ι :=
    { F := F.lift P hP
      π := ε
      epi_π_app := hε }
  refine ⟨F.FullSubcategory, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, F.ι, inferInstance, inferInstance, inferInstance,
    fun X ↦ X.property, Λ.reduced.F, inferInstance, Λ.reduced.π, ?_⟩
  intro X
  infer_instance

end CategoryTheory.Abelian
