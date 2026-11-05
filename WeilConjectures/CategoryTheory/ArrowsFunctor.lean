/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The set of arrows as a functor on categories

Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor).

## Main definitions

* `CategoryTheory.Cat.arrows`: the set-valued functor of all arrows.

## Main statements

* `CategoryTheory.Cat.arrows_map_id`: identity preserves every arrow.
* `CategoryTheory.Cat.arrows_map_comp`: composition acts by successive arrow maps.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Cat

end CategoryTheory.Cat
