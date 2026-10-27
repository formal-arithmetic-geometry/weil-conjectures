module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Equivalence

import Sheaf.CategoryTheory.ChosenObjectQuasiInverse

/-!
# Fibrewise equivalences of categories fibred in groupoids

Source: Stacks Project, Tag 003Z, `lemma-equivalence-fibred-categories`, parts (1) and (2)
(blueprint: lem-sfb-fibred-groupoid-equivalence-criterion).

The fibre functor is Mathlib's induced functor applied to the inclusion of a fibre.
Cartesian arrows in the node have Mathlib's strong cartesian universal property.
-/

@[expose] public section

universe u

namespace CategoryTheory.Functor

/-- The functor on the fibre over `T` induced by a functor commuting with the projections.
This specializes Mathlib's `Fiber.inducedFunctor`, with no choice of fibre model.

Source: Stacks Project, Tag 003Z, `lemma-equivalence-fibred-categories`
(blueprint: lem-sfb-fibred-groupoid-equivalence-criterion). -/
def mapFiber {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
    {p : A ⥤ C} {q : B ⥤ C} (G : A ⥤ B) (hG : G ⋙ q = p) (T : C) :
    Fiber p T ⥤ Fiber q T :=
  Fiber.inducedFunctor
    ((Functor.assoc (Fiber.fiberInclusion : Fiber p T ⥤ A) G q).trans
      ((congrArg (fun K : A ⥤ C => (Fiber.fiberInclusion : Fiber p T ⥤ A) ⋙ K) hG).trans
        Fiber.fiberInclusion_comp_eq_const))

/-- A fibrewise fully faithful and essentially surjective cartesian functor of categories
fibred in groupoids admits a cartesian quasi-inverse over the base, with vertical comparison
isomorphisms. All categories and their morphism sets lie in the common larger universe.

Source: Stacks Project, Tag 003Z, `lemma-equivalence-fibred-categories`, parts (1) and (2)
(blueprint: lem-sfb-fibred-groupoid-equivalence-criterion).

Proof: For an arrow `u : S ⟶ T`, choose a cartesian lift `v` with prescribed target in `A`.
Factoring through `v` identifies arrows over `u` with vertical arrows in the fibre over `S`.
The same factorization through `G.map v` in `B` intertwines the Hom map of `G` with that of
`mapFiber G hG S`. Fibrewise full faithfulness therefore makes `G` fully faithful on total
categories. Next choose, for each `b` over `T`, an object `a_b` in the same fibre and a
vertical isomorphism `i_b : b ≅ G.obj a_b`, using fibrewise essential surjectivity. The size
convention `def-weil-size-convention` permits these simultaneous choices. Apply
`exists_quasiInverse_with_objIso` (`lem-sfb-chosen-object-quasi-inverse`) to these prescribed
objects and comparisons. Its arrow formula shows, after applying `q`, that the resulting
functor `H` satisfies `H ⋙ p = q`. Its comparison formula similarly shows that the
components of `G ⋙ H ≅ 𝟭 A` lie over identities. The inverse of the chosen comparison gives
`H ⋙ G ≅ 𝟭 B`, also vertical. Finally any arrow in a fibred groupoid factors as a vertical
arrow followed by a cartesian lift. The vertical arrow is invertible because the fibre is
a groupoid. Factoring through the lift and then its vertical inverse proves the strong
cartesian universal property for the original arrow (Tag 003V). Thus `H` preserves
cartesian arrows, giving the claimed inverse over the base. -/
theorem exists_cartesian_quasiInverse_of_fibrewise_equivalence
    {C A B : Type u} [Category.{u} C] [Category.{u} A] [Category.{u} B]
    (p : A ⥤ C) (q : B ⥤ C) [p.IsFibered] [q.IsFibered]
    (hp : ∀ T : C, IsGroupoid (Fiber p T))
    (hq : ∀ T : C, IsGroupoid (Fiber q T))
    (G : A ⥤ B) (hG : G ⋙ q = p)
    (hcart : ∀ {S T : C} (u : S ⟶ T) {a a' : A} (v : a ⟶ a'),
      p.IsStronglyCartesian u v → q.IsStronglyCartesian u (G.map v))
    (hfull : ∀ T : C, (mapFiber G hG T).Full)
    (hfaithful : ∀ T : C, (mapFiber G hG T).Faithful)
    (hessSurj : ∀ T : C, (mapFiber G hG T).EssSurj) :
    ∃ H : B ⥤ A, H ⋙ p = q ∧
      (∀ {S T : C} (u : S ⟶ T) {b b' : B} (v : b ⟶ b'),
        q.IsStronglyCartesian u v → p.IsStronglyCartesian u (H.map v)) ∧
      ∃ (e : G ⋙ H ≅ 𝟭 A) (i : H ⋙ G ≅ 𝟭 B),
        (∀ a : A, p.IsHomLift (𝟙 (p.obj a)) (e.hom.app a)) ∧
        (∀ b : B, q.IsHomLift (𝟙 (q.obj b)) (i.hom.app b)) := by
  sorry

end CategoryTheory.Functor
