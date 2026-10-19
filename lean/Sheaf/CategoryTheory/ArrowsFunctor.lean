/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.CategoryTheory.ArrowsFunctor

/-! # The set of arrows as a functor on categories

Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: def-weil-pbc-arrows-functor).

## Main definitions

* `CategoryTheory.Cat.arrows`: the set-valued functor of all arrows.

## Main statements

* `CategoryTheory.Cat.arrows_map_id`: identity preserves every arrow.
* `CategoryTheory.Cat.arrows_map_comp`: composition acts by successive arrow maps.
-/
