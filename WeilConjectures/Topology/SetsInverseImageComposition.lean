/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Composition of inverse images of sheaves of sets

Inverse images of sheaves of sets compose by a natural isomorphism.

## Implementation details

The comparison is obtained by composing the adjunctions for the two maps and using the canonical
pushforward composition isomorphism; uniqueness follows from the composite adjunction.

## References

* [Stacks Project, Tags 008I and 008E](https://stacks.math.columbia.edu/tag/008I)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat.Sheaf

/-- Inverse images compose by a natural isomorphism whose component at each sheaf is the
unique sheaf morphism compatible with the adjunction units on every section. -/
theorem exists_sets_inverseImage_comp
    {X Y Z : TopCat.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ e : pullback (Type u) g ⋙ pullback (Type u) f ≅ pullback (Type u) (f ≫ g),
      ∀ G : Z.Sheaf (Type u),
        (∀ (W : Opens Z) (s : G.obj.obj (op W)),
          (e.hom.app G).hom.app (op ((Opens.map (f ≫ g)).obj W))
            (((pullbackPushforwardAdjunction (Type u) f).unit.app
                ((pullback (Type u) g).obj G)).hom.app (op ((Opens.map g).obj W))
              (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app
                (op W) s)) =
            ((pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G).hom.app
              (op W) s) ∧
        (∀ c : (pullback (Type u) f).obj ((pullback (Type u) g).obj G) ⟶
            (pullback (Type u) (f ≫ g)).obj G,
          (∀ (W : Opens Z) (s : G.obj.obj (op W)),
            c.hom.app (op ((Opens.map (f ≫ g)).obj W))
              (((pullbackPushforwardAdjunction (Type u) f).unit.app
                  ((pullback (Type u) g).obj G)).hom.app (op ((Opens.map g).obj W))
                (((pullbackPushforwardAdjunction (Type u) g).unit.app G).hom.app
                  (op W) s)) =
              ((pullbackPushforwardAdjunction (Type u) (f ≫ g)).unit.app G).hom.app
                (op W) s) →
          c = e.hom.app G) := by
  let adj := (pullbackPushforwardAdjunction (Type u) g).comp
    (pullbackPushforwardAdjunction (Type u) f)
  let adj' : pullback (Type u) (f ≫ g) ⊣
      pushforward (Type u) f ⋙ pushforward (Type u) g :=
    pullbackPushforwardAdjunction (Type u) (f ≫ g)
  let e := adj.leftAdjointUniq adj'
  refine ⟨e, fun G ↦ ?_⟩
  have heq := adj.unit_leftAdjointUniq_hom_app adj' G
  constructor
  · intro W s
    rw [Adjunction.comp_unit_app] at heq
    exact congrArg (fun k ↦ k.hom.app (op W) s) heq
  · intro c hc
    apply (adj.homEquiv G _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, heq]
    apply CategoryTheory.Sheaf.hom_ext
    ext W s
    rw [Adjunction.comp_unit_app]
    exact hc W.unop s

end TopCat.Sheaf
