/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Higher right derived functors of exact functors

Source: Stacks Project, Derived Categories, Lemma 13.16.9, Tag 015F, part (5)
(blueprint: lem-sc-exact-functor-higher-derived-vanishing).
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- An exact additive functor between abelian categories with enough injectives has zero
higher right derived functors: `R^{q+1} v (M) = 0` for every `q : ℕ`, i.e. `R^q v (M) = 0`
for every integer `q > 0`, in the natural-number indexing of `Functor.rightDerived`.

Source: Stacks Project, Derived Categories, Lemma 13.16.9, Tag 015F, part (5)
(blueprint: lem-sc-exact-functor-higher-derived-vanishing).

Proof: Exactness implies left exactness and additivity, so choose an injective resolution
`M → I` as in [def-sp-left-exact-additive] and [def-sp-injective-resolutions]. Its cohomology
vanishes in every positive degree. The exact-functor cohomology comparison
[lem-weil-pbc-exact-functor-complex-cohomology] identifies `H^q(v(I))` with `v(H^q(I))`.
This is zero, since `H^q(I)` is zero and an additive functor preserves zero objects.
Finally, [def-sp-left-exact-additive] identifies `R^q v(M)` with `H^q(v(I))`, giving the
claimed vanishing. -/
theorem isZero_rightDerived_obj_of_exact
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] [EnoughInjectives A] [EnoughInjectives B]
    (v : A ⥤ B) [v.Additive] [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (M : A) (q : ℕ) : IsZero ((v.rightDerived (q + 1)).obj M) :=
  sorry

end CategoryTheory.Functor
