/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Right-fraction localization of a dense full subcategory

Source: Stacks Project, `derived.tex`, Tag 0GSL (blueprint:
lem-trf-right-fraction-dense-subcategory).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂ u₃ v₃

open CategoryTheory

namespace CategoryTheory

/-
The hypotheses package the ambient right-fraction axioms, the full subcategory
and its objectwise supply of denominators, and universal-property localizations
of the ambient and restricted categories.  The conclusion records both the
restricted right calculus and the equivalence induced by the inclusion.
-/
/--
(blueprint: lem-trf-right-fraction-dense-subcategory)

Let `C` be a category and `W` a class of arrows containing identities and closed
under composition, satisfying the right-fraction Ore and cancellation axioms.
Let `P` define a full subcategory, and suppose every object of `C` receives a
`W`-arrow from an object of this subcategory.  If `Q` and `QB` are
localizations of `C` at `W` and of the full subcategory at the restricted class,
then the restricted class has a right calculus of fractions and the inclusion
induces an equivalence of the two localized categories.

Source: Stacks Project, Tag 0GSL, categorical right-fraction refinement argument.
Proof plan:
1. Identities and composition restrict to the full subcategory. For an Ore square
   in `C`, choose a denominator from the subcategory into its auxiliary source.
   Precomposing both legs gives the restricted Ore square by fullness; only the
   original denominator, not the other original leg, must belong to `W`.
2. Apply ambient cancellation and precompose the resulting equalizer with a
   denominator from the subcategory. This proves restricted cancellation and
   hence the first conclusion.
3. The localization universal property
   (`lem-weil-pbc-localization-universal-property`) gives `F` and a natural
   isomorphism `QB ⋙ F ≅ P.ι ⋙ Q`. Naturality identifies its conjugated Hom map
   on roofs with the corresponding ambient roof map.
4. Represent an ambient localized arrow by a right fraction
   (`lem-pc-right-fraction-representation`). Refine its source by a denominator
   from the subcategory; the numerator and denominator then lie in the full
   subcategory and represent the same arrow. This proves Hom surjectivity.
5. Represent two restricted arrows by roofs. If their ambient images agree,
   `lem-pc-right-fraction-common-refinement` supplies a common refinement.
   Refine its source again into the subcategory and use the restricted
   common-refinement criterion to obtain equality. Only the common composite
   denominator must belong to `W`; the two refinement legs need not do so.
6. Essential surjectivity of `QB`
   (`lem-trf-localization-essentially-surjective`) transports these Hom
   bijections by conjugation to every pair of objects of `E`. Thus `F` is full
   and faithful.
7. Essential surjectivity of `Q` and a denominator from the subcategory show
   that every object of `D` is isomorphic to an image under `F`. The criterion
   `lem-trf-fully-faithful-ess-surj-equivalence` now gives `F.IsEquivalence`.
-/
theorem rightFractionDenseSubcategory
    {C : Type u₁} [Category.{v₁} C]
    (W : MorphismProperty C)
    (hW : W.HasRightCalculusOfFractions)
    (P : ObjectProperty C)
    (hP : ∀ X : C, ∃ (B : P.FullSubcategory) (s : P.ι.obj B ⟶ X), W s)
    {D : Type u₂} [Category.{v₂} D]
    (Q : C ⥤ D) [Q.IsLocalization W]
    {E : Type u₃} [Category.{v₃} E]
    (QB : P.FullSubcategory ⥤ E)
    [QB.IsLocalization (W.inverseImage P.ι)] :
    (W.inverseImage P.ι).HasRightCalculusOfFractions ∧
      ∃ (F : E ⥤ D), F.IsEquivalence ∧ Nonempty (QB ⋙ F ≅ P.ι ⋙ Q) := by
  sorry

end CategoryTheory
