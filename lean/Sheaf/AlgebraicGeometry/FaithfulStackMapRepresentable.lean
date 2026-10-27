/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Sheaf.AlgebraicGeometry.AlgebraicStackFibreProducts
import Sheaf.AlgebraicGeometry.AlgebraicSetoidSpace

/-! # Faithful algebraic-stack morphisms are representable by algebraic spaces

Source: Stacks Project, Algebraic Stacks, Tag 04Y5,
lemma-characterize-representable-by-algebraic-spaces, (1) and (3)
(blueprint: lem-sfb-faithful-stack-map-representable).

The criterion uses the actual induced functor on each fibre and its map on
isomorphisms. Representability retains the projection to each test scheme.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ v₂ w₁ w₂

open AlgebraicGeometry

namespace CategoryTheory

/-- A morphism of algebraic stacks is representable by algebraic spaces exactly
when it is injective on isomorphisms between every pair of objects in every fibre.
Source: Stacks Project, Algebraic Stacks, Tag 04Y5,
lemma-characterize-representable-by-algebraic-spaces, (1) and (3)
(blueprint: lem-sfb-faithful-stack-map-representable).

Proof:
1. Suppose the map is representable. For fibre objects x and x' over T and
   isomorphisms a,b with the same image alpha, form h_T ×_Y X using the
   object F(x). Both a and b give arrows from (id,x,id) to (id,x',alpha).
   A presentation by a discrete algebraic-space groupoid makes these arrows
   equal, hence a = b (def-sfb-stable-pointed-moduli-groupoids).
2. Conversely assume injectivity. For T and y in Y(T), the discrete groupoid
   h_T is algebraic: its descent is unique gluing of maps, its diagonal is
   represented by scheme fibre products, and its identity is an etale
   surjective atlas. Use def-trf-scheme-algebraic-space and
   lem-sfb-fibred-groupoid-representable-smooth-calculus to regard this as
   a smooth atlas (def-sfb-algebraic-moduli-stack).
3. By lem-sfb-algebraic-stack-fibre-products, W = h_T ×_Y X is algebraic.
4. An arrow between triples (t,x,alpha) and (t',x',alpha') forces t = t'
   and satisfies F(a) alpha = alpha'. Cancel alpha for any two such arrows;
   injectivity implies they agree. Thus all fibre automorphisms of W
   are identities (def-sfb-stable-pointed-moduli-groupoids).
5. Apply lem-sfb-algebraic-setoid-space to obtain an algebraic space R and
   an equivalence h_R ≃ W over S. Composing with W → h_T gives a map R → T,
   since maps of these discrete groupoids are natural transformations of
   their sheaves (def-trf-algebraic-space). With this map the equivalence
   is over T; its inverse is over T because its unit and counit map to
   equalities in h_T. This presents every scheme 2-base change as required. -/
theorem isRepresentableByAlgebraicSpaces_iff_injective_mapIso
    {S : Scheme.{u}} (X : BasedCategory.{v₁, w₁} (Over S))
    (Y : BasedCategory.{v₂, w₂} (Over S))
    (hX : IsAlgebraicModuliStack X) (hY : IsAlgebraicModuliStack Y)
    (F : BasedFunctor X Y) :
    IsRepresentableByAlgebraicSpaces F ↔
      ∀ (T : Over S) (x x' : Functor.Fiber X.p T),
        Function.Injective (fun α : x ≅ x' ↦ (moduliFiberMap F T).mapIso α) := by
  sorry

end CategoryTheory
