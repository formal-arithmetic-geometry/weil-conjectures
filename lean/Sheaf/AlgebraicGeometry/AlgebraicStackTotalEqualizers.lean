/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
import Mathlib.AlgebraicGeometry.Pullbacks
import Sheaf.AlgebraicGeometry.AlgebraicSpace

/-! # Equalizers in the total category of an algebraic stack

Source: Stacks Project, stacks-sheaves.tex, Tag 06WY, lemma-fibre-products (2), (3)
(blueprint: lem-sfb-algebraic-stack-total-equalizers).

The equalizers are ordinary categorical equalizers of arbitrary parallel arrows in the
whole total category, including arrows with different underlying scheme morphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace CategoryTheory

open Limits

/-- The total category of an algebraic stack has equalizers, without separatedness or
finiteness assumptions on its diagonal.

Source: Stacks Project, stacks-sheaves.tex, Tag 06WY, lemma-fibre-products (2), (3)
(blueprint: lem-sfb-algebraic-stack-total-equalizers).

Proof:
1. For parallel arrows a, b : z → z', write f, g for their base maps U → V.
   Form W = U ×_(V ×_S V) V using (f,g) and the diagonal of V, by
   def-pc-fibre-product. Its projection j : W → U equalizes f and g. Any
   r : T → U equalizing f and g lifts uniquely to (r,fr) : T → W, so j
   is their equalizer, without any separatedness assumption.
2. Lift j to c : x → z using def-sfb-stable-pointed-moduli-groupoids. Put
   A = ac and B = bc. The strong cartesian property factors every arrow h
   equalizing a,b uniquely through c over its uniquely determined base factor
   through j. The resulting d satisfies Ad = Bd. Conversely such a d gives h = cd.
3. The same strong cartesian property gives a unique vertical automorphism i of x
   with Ai = B: factoring in reverse constructs its inverse, with the inverse
   identities following by uniqueness. For any d : t → x, Ad = Bd is equivalent
   to id = d, by uniqueness of factorization through A over the fixed base map.
4. Apply lem-sfb-stack-isom-space-locally-finite-type only for representability:
   the automorphism presheaf of x over W is an algebraic space G → W.
   Its identity and i give sections e and sigma. Their restrictions along
   r : T → W represent the identity and the restriction of i, respectively.
5. By def-trf-algebraic-space, pull back the representable diagonal of G over W
   along (e,sigma) : h_W → G ×_W G. This is a scheme M with a monomorphism
   m : M → W. Its T-points are exactly the maps r : T → W on which i
   restricts to the identity. Indeed the diagonal pullback has one point over
   such an r and none otherwise. It is also W ×_(e,G,sigma) W, since both
   sections have structural composite the identity, forcing their base maps equal.
6. Lift m to v : x_M → x. Then iv = v, so E = cv equalizes a,b.
   Given h equalizing a,b, step 2 gives a unique d over r with cd = h, and
   step 3 gives id = d. Factoring d through a pullback of x along r gives
   an isomorphism in the fibre, so this equation means i restricts to the identity
   over the base of t. Step 5 uniquely factors r through m. The strong cartesian
   property uniquely factors d through v over that map, giving h through E.
   For any other factor, uniqueness through j fixes its composite base map to W;
   uniqueness through c fixes its composite with v; uniqueness through m fixes
   its base map to M; finally uniqueness through v identifies the factors. -/
theorem hasEqualizers_of_isAlgebraicModuliStack
    {S : AlgebraicGeometry.Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) : HasEqualizers F.obj := by
  sorry

end CategoryTheory
