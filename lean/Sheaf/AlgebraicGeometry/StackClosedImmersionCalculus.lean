/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.StackPointTopologyFlatLfpOpen
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.StackPointTopology
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # Closed immersions of algebraic stacks

Source: Stacks Project, stacks-properties.tex, Tags 04YL, 0501, 0502 and 0H20;
stacks-morphisms.tex, Tags 06FV and 06FT
(blueprint: lem-sfb-stack-closed-immersion-calculus).

Closed immersion means the existing scheme base-change test, retaining the equivalence
with the actual 2-fibre product and its projection. Local finite type over a field is
written using a smooth surjective scheme atlas with locally finite type structure map.
No finite presentation or Deligne--Mumford condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂ v₃ w₃

open AlgebraicGeometry

namespace CategoryTheory

/-- Closed immersions are preserved by arbitrary algebraic-stack base change: the
2-fibre product `X ×_Y Z` is an algebraic stack and its projection to `X` passes the
closed-immersion scheme test.
Source: Stacks Project, Tags 04YL and 0501
(blueprint: lem-sfb-stack-closed-immersion-calculus).

Proof (node step 1): for a scheme T mapping to X, reassociate
T ×_X (X ×_Y Z) as T ×_Y Z over T. The equivalence forgets the redundant X-object
and composes its specified comparison isomorphisms; its inverse inserts the image of
the T-object. The scheme test for i makes the latter a scheme closed in T, which is
the required scheme test for the projection. The fibre product is an algebraic stack
by lem-sfb-algebraic-stack-fibre-products. The reassociation uses the object-and-
isomorphism construction of def-sfb-stable-pointed-moduli-groupoids. -/
theorem stack_closedImmersion_baseChange {S : Scheme.{u}}
    {Z : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    {X : BasedCategory.{v₃, w₃} (Over S)}
    (hZ : IsAlgebraicModuliStack Z) (hY : IsAlgebraicModuliStack Y)
    (hX : IsAlgebraicModuliStack X) (i : BasedFunctor Z Y) (a : BasedFunctor X Y)
    (hi : ModuliSchemeTest @IsClosedImmersion i) :
    IsAlgebraicModuliStack (moduliTwoFiberProduct a i) ∧
      ModuliSchemeTest @IsClosedImmersion (moduliTwoFiberFst a i) := by
  sorry

/-- Composites of closed immersions of algebraic stacks are closed immersions.
Source: Stacks Project, Tag 0502
(blueprint: lem-sfb-stack-closed-immersion-calculus).

Proof (node step 2): for a scheme T mapping to Y, put V = T ×_Y X and
W = V ×_X Z. The scheme tests make V closed in T and W closed in V.
The explicit 2-fibre product of def-sfb-stable-pointed-moduli-groupoids identifies
W with T ×_Y Z over T by composing the displayed isomorphisms. Scheme closed
immersions compose by lem-weil-pbc-closed-immersion-comp, so W is closed in T.
This is exactly the scheme test for the composite. -/
theorem stack_closedImmersion_comp {S : Scheme.{u}}
    {Z : BasedCategory.{v₁, w₁} (Over S)} {X : BasedCategory.{v₂, w₂} (Over S)}
    {Y : BasedCategory.{v₃, w₃} (Over S)}
    (hZ : IsAlgebraicModuliStack Z) (hX : IsAlgebraicModuliStack X)
    (hY : IsAlgebraicModuliStack Y) (i : BasedFunctor Z X) (j : BasedFunctor X Y)
    (hi : ModuliSchemeTest @IsClosedImmersion i)
    (hj : ModuliSchemeTest @IsClosedImmersion j) :
    ModuliSchemeTest @IsClosedImmersion (i.comp j) := by
  sorry

/-- The point map of a closed immersion is a closed embedding and sends closed sets
 to closed sets. Source: Stacks Project, Tag 0H20
(blueprint: lem-sfb-stack-closed-immersion-calculus).

Proof (node steps 3 and 4): if two field objects have the same image point, then
lem-sfb-stack-point-topology gives an isomorphism of their images over a common
extension L. They give L-points of Spec L ×_X Z. This scheme is closed in Spec L,
hence is Spec(L/I) by def-weil-closed-immersion; an L-point forces I = 0.
Its discrete groupoid has a unique L-point, so the original objects become
isomorphic over L. Thus the point map is injective.
Choose a smooth surjective atlas U → X and form V = U ×_X Z. Its projection
h:V → U is a scheme closed immersion and r:V → Z is a smooth surjective atlas by
lem-sfb-stack-chartwise-smooth-etale-calculus. For a closed D in |Z|, continuity
makes r⁻¹(D) closed, and h sends it to a closed subset of U. The identity
p⁻¹(i(D)) = h(r⁻¹(D)) follows from the 2-fibre-product objects and their comparison
isomorphisms: equal image points become isomorphic over a common field extension,
and conversely a fibre-product object has equal image point classes.
The atlas closed-subset criterion in lem-sfb-stack-point-topology makes i(D)
closed. Taking D to be the whole point space gives closed image. Continuity is
provided by lem-sfb-stack-point-topology-flat-lfp-open, and an injective continuous
closed map is a homeomorphism onto its closed image. -/
theorem stack_closedImmersion_topology {S : Scheme.{u}}
    {Z : BasedCategory.{v₁, w₁} (Over S)} {X : BasedCategory.{v₂, w₂} (Over S)}
    (hZ : IsAlgebraicModuliStack Z) (hX : IsAlgebraicModuliStack X)
    (i : BasedFunctor Z X) (hi : ModuliSchemeTest @IsClosedImmersion i) :
    Topology.IsClosedEmbedding (moduliPointMap i) ∧ IsClosedMap (moduliPointMap i) := by
  sorry

/-- A closed substack of an algebraic stack locally of finite type over a field
is locally of finite type, with both properties tested on smooth scheme atlases.
Source: Stacks Project, stacks-morphisms.tex, Tags 06FV and 06FT
(blueprint: lem-sfb-stack-closed-immersion-calculus).

Proof (node step 5): choose a smooth surjective scheme atlas U → X whose
structural morphism is locally of finite type over k. The scheme test makes
V = U ×_X Z a scheme closed in U. Its projection to Z is a smooth surjective
atlas by lem-sfb-stack-chartwise-smooth-etale-calculus. Over each affine
Spec A of U, the scheme V is Spec(A/I), by def-weil-closed-immersion.
A finite k-algebra generating set of A maps to a generating set of A/I.
Thus V is locally of finite type over k by def-weil-finite-type-morphism,
and this atlas establishes exactly the same property for Z. No finite
generation of I or finite presentation of i is required. -/
theorem stack_closedImmersion_locallyFiniteType (k : Type u) [Field k]
    {Z : BasedCategory.{v₁, w₁} (Over (Spec (.of k)))}
    {X : BasedCategory.{v₂, w₂} (Over (Spec (.of k)))}
    (hZ : IsAlgebraicModuliStack Z) (hX : IsAlgebraicModuliStack X)
    (i : BasedFunctor Z X) (hi : ModuliSchemeTest @IsClosedImmersion i)
    (hXft : ∃ (U : Over (Spec (.of k)))
      (p : BasedFunctor (discreteModuli (yoneda.obj U)) X),
      IsSmoothModuliAtlas X U p ∧ LocallyOfFiniteType U.hom) :
    ∃ (V : Over (Spec (.of k))) (q : BasedFunctor (discreteModuli (yoneda.obj V)) Z),
      IsSmoothModuliAtlas Z V q ∧ LocallyOfFiniteType V.hom := by
  sorry

end CategoryTheory
