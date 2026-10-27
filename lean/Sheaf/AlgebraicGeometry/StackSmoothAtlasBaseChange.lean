/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.ModuliSchemeBaseChange
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange

/-! # Smooth atlas comparison and arbitrary scheme base change

Source: Stacks Project, Tags 06FM, 075U, 075W, 04T2 and 04WV
(blueprint: lem-sfb-stack-smooth-atlas-base-change).

The test maps in the atlas criterion are representable smooth scheme maps; they
need not be surjective. The three base-change assertions refer to the explicit
iso-comma restriction and the specified scheme atlas map, without finiteness or
separation assumptions on the base or the stack.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

/-- Smoothness is detected by all representable smooth maps from schemes, without
requiring them to be surjective. Source: Stacks Project, Tags 06FM and 075U
(blueprint: lem-sfb-stack-smooth-atlas-base-change).

Proof:
1. Choose a smooth surjective atlas U → F with U → S smooth, using
   def-sfb-algebraic-moduli-stack. For a representable smooth W → F, the space
   R = U ×_F W is smooth over U and smoothly surjects onto W by
   lem-sfb-fibred-groupoid-representable-smooth-calculus. Use the representable
   spaces of def-trf-scheme-algebraic-space. Apply
   lem-sfb-space-smooth-source-point-locality to R → U → S and then R → W → S.
   Every point of W lifts to R, so W → S is smooth everywhere. This uses no
   surjectivity of W → F.
2. Conversely apply the test to an atlas supplied by hF. Its smooth structural
   composite witnesses IsSmoothModuliStack by def-sfb-algebraic-moduli-stack. -/
theorem isSmoothModuliStack_iff_forall_smooth_scheme_map
    {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) :
    IsSmoothModuliStack F ↔
      ∀ (W : Over S) (p : BasedFunctor (discreteModuli (yoneda.obj W)) F),
        (∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) F),
          ∃ (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
            HasSpaceBaseChange p T t Z a ∧ SpaceMapIsSmooth Z T a) →
        Smooth W.hom := by
  sorry

/-- Arbitrary scheme base change of an algebraic stack is algebraic over the new
base. Source: Stacks Project, Tags 04T2 and 04WV
(blueprint: lem-sfb-stack-smooth-atlas-base-change).

Proof (step 3 of the node): schemes define algebraic stacks through their Yoneda
sheaves, as in def-trf-scheme-algebraic-space. Apply
lem-sfb-algebraic-stack-fibre-products to F → S ← S'. Then apply
lem-sfb-etale-stack-localization to read its total category over S'. The explicit
iso-comma construction of def-sfb-moduli-scheme-base-change retains precisely
these objects and arrows. Diagonal tests do not change. The scheme base change
of an atlas is an atlas by lem-sfb-fibred-groupoid-representable-smooth-calculus,
using def-pc-fibre-product and the triples of def-sfb-stable-pointed-moduli-groupoids.
Thus descent, the diagonal condition, and existence of a smooth atlas all hold. -/
theorem isAlgebraicModuliStack_schemeBaseChange
    {S S' : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) (g : S' ⟶ S) :
    IsAlgebraicModuliStack (moduliSchemeBaseChange F g) := by
  sorry

/-- Every specified smooth surjective scheme atlas remains such an atlas after
arbitrary scheme base change. Source: Stacks Project, Tags 075W, 0302 and 045C
(blueprint: lem-sfb-stack-smooth-atlas-base-change).

Proof (atlas clause of step 3): let U' = U ×_S S'. The triples in
 def-sfb-stable-pointed-moduli-groupoids identify U' with U ×_F (F ×_S S').
The map moduliSchemeBaseChangeAtlas is the map of this square, on objects and
arrows, by def-sfb-moduli-scheme-base-change and def-pc-fibre-product.
Apply lem-sfb-fibred-groupoid-representable-smooth-calculus to the original atlas:
representability, smoothness and surjectivity survive 2-base change. The resulting
space presentations and their projections give exactly IsSmoothModuliAtlas. -/
theorem isSmoothModuliAtlas_schemeBaseChange
    {S S' : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) (U : Over S)
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (ha : IsSmoothModuliAtlas F U a) (g : S' ⟶ S) :
    IsSmoothModuliAtlas (moduliSchemeBaseChange F g) ((Over.pullback g).obj U)
      (moduliSchemeBaseChangeAtlas a g) := by
  sorry

/-- Smoothness of an algebraic stack over a scheme survives arbitrary scheme base
change. Source: Stacks Project, Tag 075W
(blueprint: lem-sfb-stack-smooth-atlas-base-change).

Proof (step 4): choose a smooth surjective atlas U → F whose structural map
U → S is smooth, using def-sfb-algebraic-moduli-stack. Step 3 gives the
base-changed atlas U ×_S S' → F ×_S S'. By lem-pc-smooth-flat, U → S is flat
and locally of finite presentation. Apply
lem-sfb-scheme-flat-smooth-point-base-change to its scheme base change, as in
def-pc-fibre-product: it is smooth near each point because U → S is smooth near
its image. These neighbourhoods cover the pullback, so its structural map to S'
is smooth. The base-changed atlas therefore witnesses IsSmoothModuliStack. -/
theorem isSmoothModuliStack_schemeBaseChange
    {S S' : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (hF : IsAlgebraicModuliStack F) (hs : IsSmoothModuliStack F) (g : S' ⟶ S) :
    IsSmoothModuliStack (moduliSchemeBaseChange F g) := by
  sorry

end CategoryTheory
