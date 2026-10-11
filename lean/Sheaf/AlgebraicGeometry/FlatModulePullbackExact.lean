/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Flat module pullback is exact and direct image preserves injectives

Source: literature/stacks-project/modules.tex; literature/stacks-project/cohomology.tex,
Modules 02N4 and Cohomology 02N5
(blueprint: lem-weil-pbc-flat-module-pullback-exact-pushforward-injective).
-/

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- For a flat morphism of schemes, module pullback is exact and pushforward preserves
injective objects.

Source: Stacks Project, Modules 02N4, `lemma-pullback-flat`, and Cohomology 02N5,
`lemma-pushforward-injective-flat`.

Proof (the three steps of the node):
1. For an exact complex F → G → H on Y and x in X, put y = h(x).
   By lem-weil-pbc-module-stalk-exact the complex of stalks at y is exact.
   The natural stalk isomorphism of lem-weil-pbc-module-stalk-pullback identifies
   its tensor product with O_{X,x} with the stalk of the pulled-back complex.
   Naturality identifies its two differentials with the tensor maps a_y ⊗ 1 and b_y ⊗ 1.
2. By def-weil-flat-morphism, O_{X,x} is flat over O_{Y,y}.
   Apply lem-weil-pbc-flat-tensor-exact to obtain exactness of the tensor complex.
   It follows that the pulled-back complex is exact at every stalk, and hence exact
   as a complex of module sheaves by lem-weil-pbc-module-stalk-exact.
3. The inverse-image-and-tensor construction of def-pc-module-pullback is additive:
   inverse image preserves sums of morphisms, and (a + a') ⊗ 1 = a ⊗ 1 + a' ⊗ 1
   on pure tensors, hence after sheafification. It sends zero to zero. Apply steps 1
   and 2 also at the ends of short exact sequences to get exactness, equivalently
   preservation of finite limits and finite colimits in these abelian categories.
   The same dependency gives the adjunction to module pushforward. For injective I
   (def-sp-injective-resolutions), a map M → h_*I corresponds to h^*M → I.
   A monomorphism M → N pulls back to a monomorphism, so injectivity extends this
   map to h^*N → I. Its adjoint N → h_*I extends the original map by naturality.
(blueprint: lem-weil-pbc-flat-module-pullback-exact-pushforward-injective) -/
theorem flat_module_pullback_exact_pushforward_injective
    {X Y : Scheme.{u}} (h : X ⟶ Y) [Flat h] :
    (PreservesFiniteLimits (Scheme.Modules.tensorPullback h) ∧
      PreservesFiniteColimits (Scheme.Modules.tensorPullback h)) ∧
      (Scheme.Modules.pushforward h).PreservesInjectiveObjects := by
  sorry

end AlgebraicGeometry
