module

public import Sheaf.CategoryTheory.SiteExtensionByZeroPresheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Adjunction for extension by zero on a localized site

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-site-extension-by-zero-presheaf-adjoint).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

/-- The sheafified direct-sum presheaf is left adjoint to restriction.

Source: literature/stacks-project/sites-modules.tex, Modules on Sites, Lemma 03DI
(blueprint: lem-weil-pbc-site-extension-by-zero-presheaf-adjoint).

Given a morphism `α : F ⟶ G|_W`, the first proof step defines a presheaf map by
sending the section in the `φ`-summand to `α.app (Over.mk φ)`. Naturality in the
slice gives compatibility with restrictions, and the direct-sum universal property
provides the unique map on each section. The second step factors this map uniquely
through sheafification. Conversely, composing a map from the sheafification with
the canonical presheaf map and restricting to each summand gives the inverse map.
The sheafification universal property proves that these constructions are inverse;
naturality in `F` and `G` follows componentwise. The displayed hom-set
bijections are represented by the hom-equivalences of the resulting adjunction.
-/
theorem siteExtensionByZeroPresheaf_adjunction
    {C : Type u} [SmallCategory C]
    (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (W : C) :
    ∃ e : siteExtensionByZeroSheaf J W ⊣
        (Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
          (J.toGrothendieck.over W) J.toGrothendieck,
      ∀ (F : Sheaf (J.toGrothendieck.over W) AddCommGrpCat.{u})
        (G : Sheaf J.toGrothendieck AddCommGrpCat.{u}),
        ∀ (α : F ⟶
          ((Over.forget W).sheafPushforwardContinuous AddCommGrpCat.{u}
            (J.toGrothendieck.over W) J.toGrothendieck).obj G),
          e.homEquiv F G ((e.homEquiv F G).symm α) = α := by
  sorry

end CategoryTheory
