/-
Copyright (c) 2026 Wei Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Yang
-/
import WeilConjectures.CategoryTheory.Sites.LocalizationLowerShriek

/-!
# Identity and composition for the localization lower shriek

For morphisms `g : W ⟶ V` and `f : V ⟶ U` in a site `(C, J)` we prove the coherence
isomorphisms of the lower shriek functors of localized sites:

- `localizationLowerShriekIdIso` : `j_{(𝟙 U)!} ≅ 𝟭`;
- `localizationLowerShriekCompIso` : `j_{(g ≫ f)!} ≅ j_{g!} ⋙ j_{f!}`
  (note the order: in Lean's convention `F ⋙ G` applies `F` first, so this is
  the expected `(f ∘ g)_! ≅ f_! ∘ g_!`).

Both are obtained from uniqueness of left adjoints (`Adjunction.leftAdjointUniq`),
transporting along mathlib's coherence isomorphisms `J.overMapPullbackId` and
`J.overMapPullbackComp` for the restriction functors. These are the object-level
compatibilities of the lower shriek with the pseudofunctor structure of
`J.pseudofunctorOver A` (whose 1-cell images are the restriction functors
`J.overMapPullback A f`); a fully coherent "lower shriek pseudofunctor" is left
for future work.
-/

universe v' v u' u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (A : Type u') [Category.{v'} A]

section Identity

variable (U : C)
variable [∀ P : (Over U)ᵒᵖ ⥤ A, (Over.map (𝟙 U)).op.HasLeftKanExtension P]
variable [HasWeakSheafify (J.over U) A]

/-- The lower shriek along the identity morphism is isomorphic to the identity functor,
by uniqueness of left adjoints. -/
noncomputable def localizationLowerShriekIdIso :
    J.localizationLowerShriek A (𝟙 U) ≅ 𝟭 (Sheaf (J.over U) A) :=
  Adjunction.leftAdjointUniq (J.localizationLowerShriekAdjunction A (𝟙 U))
    (Adjunction.id.ofNatIsoRight (J.overMapPullbackId A U).symm)

end Identity

section Composition

variable {W V U : C} (g : W ⟶ V) (f : V ⟶ U)
variable [∀ P : (Over W)ᵒᵖ ⥤ A, (Over.map g).op.HasLeftKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ A, (Over.map f).op.HasLeftKanExtension P]
variable [∀ P : (Over W)ᵒᵖ ⥤ A, (Over.map (g ≫ f)).op.HasLeftKanExtension P]
variable [HasWeakSheafify (J.over V) A] [HasWeakSheafify (J.over U) A]

/-- The lower shriek along a composite `g ≫ f` is the composite of the lower shrieks:
`j_{(g ≫ f)!} ≅ j_{g!} ⋙ j_{f!}`, by uniqueness of left adjoints applied to the
composite adjunction and the compatibility `J.overMapPullbackComp` of the restriction
functors. -/
noncomputable def localizationLowerShriekCompIso :
    J.localizationLowerShriek A (g ≫ f) ≅
      J.localizationLowerShriek A g ⋙ J.localizationLowerShriek A f :=
  Adjunction.leftAdjointUniq (J.localizationLowerShriekAdjunction A (g ≫ f))
    (((J.localizationLowerShriekAdjunction A g).comp
      (J.localizationLowerShriekAdjunction A f)).ofNatIsoRight
        (J.overMapPullbackComp A g f))

end Composition

end CategoryTheory.GrothendieckTopology
