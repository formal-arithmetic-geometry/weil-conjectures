import Mathlib.CategoryTheory.Sites.Plus
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Injectivity into the plus construction for a separated presheaf

Source: `literature/stacks-project/sites.tex`, Definition 00WA and
Theorem 00WB, part (2), proof of item-sheaf
(blueprint: lem-weil-pbc-site-plus-injective-separated).
-/

universe u

open CategoryTheory Opposite

namespace CategoryTheory.GrothendieckTopology.Plus

/-- For a separated presheaf, the canonical map into the plus construction is
injective on every object.

Source: Stacks, Sites, Definition 00WA (definition-separated) and Theorem 00WB,
part (2) (item-sheaf).

1. If sections `a` and `b` over `U` have equal images under the canonical map,
   the equality criterion for the plus construction gives a covering of `U`
   on which their restrictions agree. This is the theta case of clause (2) of
   lem-weil-pbc-site-plus-construction-presheaf: equality in the filtered colimit
   is witnessed after refinement of the identity covering to some covering.
2. Apply the separatedness hypothesis to that covering to obtain `a = b`.
   Thus the canonical map is injective for every object `U`.

The plus construction is the recorded sieve presentation of
 def-weil-pbc-site-plus-construction; its covering-family comparison is a stage-3 bridge.
(blueprint: lem-weil-pbc-site-plus-injective-separated) -/
theorem inj_of_separated_presheaf
    {C : Type u} [SmallCategory C] (J : Precoverage C)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    (G : Cᵒᵖ ⥤ Type u)
    (hG : ∀ (U : C) (E : J.ZeroHypercover.{u} U) (a b : G.obj (op U)),
      (∀ i : E.I₀, G.map (E.f i).op a = G.map (E.f i).op b) → a = b) :
    ∀ (U : C), Function.Injective ((J.toGrothendieck.toPlus G).app (op U)) := by
  sorry

end CategoryTheory.GrothendieckTopology.Plus
