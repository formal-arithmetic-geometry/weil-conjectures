module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise

/-!
# Left derived functors computed by projective localization representatives

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
projective-representative form; compare Differential Graded Algebra, Tags 09LS and 09KY.
(blueprint: lem-sfb-projective-localization-left-derived)
-/

@[expose] public section

universe uC vC uD vD uH vH

namespace CategoryTheory

/-- A localization with enough representatives whose outgoing Hom maps are bijective admits
universal left derived functors, and every universal counit is invertible on those representatives.
The restriction of the counit to their full subcategory is a natural isomorphism.

Source: Stacks Project, Derived Categories, Tag 06XN, `lemma-find-existence-computes`,
projective-representative form; compare DGA, Tag 09LS, `lemma-derived-bc`, and Tag 09KY,
`lemma-hom-derived`. (blueprint: lem-sfb-projective-localization-left-derived)

Proof:
1. For `Y : D`, choose an isomorphism `Y ≅ Q.obj X` by essential surjectivity and a
   representative `q : P ⟶ X`. Its image gives an isomorphism `a : Y ≅ Q.obj P`.
   In `StructuredArrow Y Q`, the object `(P, a.hom)` is initial: the arrow to `(Z, b)`
   is the unique lift of `a.inv ≫ b` under the outgoing Hom bijection.
2. The diagram `StructuredArrow.proj Y Q ⋙ F` therefore has a limiting cone with vertex
   `F.obj P` and legs the images of those unique arrows. Any cone factors by its leg
   at the initial object, uniquely since the initial object's endomorphism is the identity.
3. Apply `lem-sfb-pointwise-right-kan-from-limits`, implemented by Mathlib's
   `Functor.pointwiseRightKanExtension`, its counit and its universal property. The counit
   at `X` is the limit projection at `(X, identity)`, and the universal Hom equivalence
   sends `β` to `Functor.whiskerLeft Q β ≫ ε`.
4. For a representative `P`, `(P, identity)` is itself initial in the corresponding comma
   category. The projection of any limiting cone at this object is invertible: the cone
   with vertex `F.obj P` gives an inverse by the limiting property, and cone compatibility
   and uniqueness give both inverse identities. Thus the constructed counit is invertible at `P`.
5. For every other universal pair, `lem-sfb-right-kan-extension-unique-iso`, implemented by
   `Functor.rightKanExtensionUnique`, identifies its counit with this one composed with a
   natural isomorphism. Its components at representatives are consequently invertible.
   Naturality is the displayed equation; the inverses satisfy inverse naturality, giving
   a natural isomorphism on the full subcategory. -/
theorem exists_leftDerived_of_projective_localization
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {H : Type uH} [Category.{vH} H]
    (W : MorphismProperty C) (Q : C ⥤ D) [Q.IsLocalization W]
    (S : ObjectProperty C)
    (hrep : ∀ X : C, ∃ P : C, S P ∧ ∃ q : P ⟶ X, IsIso (Q.map q))
    (hhom : ∀ (P X : C), S P →
      Function.Bijective (Q.map : (P ⟶ X) → (Q.obj P ⟶ Q.obj X)))
    (F : C ⥤ H) :
    (∃ (LF : D ⥤ H) (ε : Q ⋙ LF ⟶ F),
      ∀ G : D ⥤ H, Function.Bijective
        (fun β : G ⟶ LF ↦ Functor.whiskerLeft Q β ≫ ε)) ∧
    (∀ (LF : D ⥤ H) (ε : Q ⋙ LF ⟶ F),
      (∀ G : D ⥤ H, Function.Bijective
        (fun β : G ⟶ LF ↦ Functor.whiskerLeft Q β ≫ ε)) →
      (∀ P : C, S P → IsIso (ε.app P)) ∧
      IsIso (Functor.whiskerLeft S.ι ε) ∧
      ∀ (P P' : C), S P → S P' → ∀ f : P ⟶ P',
        LF.map (Q.map f) ≫ ε.app P' = ε.app P ≫ F.map f) := by
  sorry

end CategoryTheory
