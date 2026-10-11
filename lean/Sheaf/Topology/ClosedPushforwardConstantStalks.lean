/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.Topology.ClosedPushforwardConstantPresheaf
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Sheaves on Spaces, Tags 006W, 007B and 00AE
(blueprint: lem-weil-pbc-closed-pushforward-constant-stalks).
-/

set_option autoImplicit false

universe w

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- The closed direct image is a sheaf; its stalk evaluates bijectively to the coefficient
set on the closed subset, and is a singleton elsewhere.
Source: Stacks Project, Sheaves on Spaces, Tags 006W, 007B and 00AE
(blueprint: lem-weil-pbc-closed-pushforward-constant-stalks).

Proof:
1. Compatible locally constant maps on an open cover glue pointwise. Local constancy is
checked in a covering member containing the point; uniqueness is pointwise. This is
lem-weil-pbc-locally-constant-maps-sheaf (Tag 006W).
2. At a point in C, each neighbourhood in C is the intersection with an ambient open
neighbourhood. Thus representatives and their germ equivalence relations identify the
stalk with that of locally constant maps on C. The unique evaluation map and its
bijectivity follow from lem-weil-pbc-locally-constant-germ-evaluation (Tag 007B).
The stalk and germ use the colimit of def-weil-pbc-category-colimit.
3. Outside C the open complement is a neighbourhood carrying the unique empty map.
Every germ restricts to that map after shrinking into the complement, so the stalk
has exactly one element (Tag 00AE). -/
theorem closed_pushforward_constant_stalks
    (X : TopCat.{w}) (C : Set X) (hC : IsClosed C) (R : Type w) :
    (closedPushforwardConstantPresheaf X C R).IsSheaf ∧
    (∀ (x : X) (hxC : x ∈ C),
      ∃ ev : (closedPushforwardConstantPresheaf X C R).stalk x → R,
        (∀ (V : Opens X) (hxV : x ∈ V)
            (g : LocallyConstant {y : X // y ∈ V ∧ y ∈ C} R),
          ev ((closedPushforwardConstantPresheaf X C R).germ V x hxV g) =
            g ⟨x, hxV, hxC⟩) ∧
        Function.Bijective ev ∧
        (∀ ev' : (closedPushforwardConstantPresheaf X C R).stalk x → R,
          (∀ (V : Opens X) (hxV : x ∈ V)
              (g : LocallyConstant {y : X // y ∈ V ∧ y ∈ C} R),
            ev' ((closedPushforwardConstantPresheaf X C R).germ V x hxV g) =
              g ⟨x, hxV, hxC⟩) → ev' = ev)) ∧
    (∀ (x : X), x ∉ C →
      Nonempty ((closedPushforwardConstantPresheaf X C R).stalk x) ∧
      Subsingleton ((closedPushforwardConstantPresheaf X C R).stalk x)) := by
  sorry

end TopCat
