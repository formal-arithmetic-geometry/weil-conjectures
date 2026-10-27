/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation
public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.CategoryTheory.GroupoidStackificationLocalDescription
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest

/-! # Algebraicity of a classifying stack forces flatness and local finite presentation

Source: Stacks Project, criteria.tex, Tag 06PL, lemma-BG-algebraic, converse
(blueprint: lem-sfb-algebraic-classifying-stack-flatness).

The two endpoints are the same structure map. A quotient presentation retains the
actual arrow sheaf and multiplication. No flatness or finiteness is imposed on the group.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Algebraicity of the fppf classifying stack implies flatness and local finite
presentation of the group algebraic space over its base.

Source: Stacks Project, criteria.tex, Tag 06PL, lemma-BG-algebraic, converse
(blueprint: lem-sfb-algebraic-classifying-stack-flatness).

The group operations are maps of the underlying presheaves of algebraic spaces;
`presentation.groupoid` imposes the group laws on every test scheme. Both endpoints
are `p`, so all arrows are automorphisms and composition is the specified multiplication.
The local arrow and object conditions characterize the fppf stackification, as in
lem-sfb-groupoid-stackification-local-description.

Proof:
1. Apply lem-sfb-algebraic-quotient-flat-refinement to this groupoid. Obtain B' to B
such that B' ×_B G to B is sheaf-surjective and both projections of
R' = B' ×_B G ×_B B' to B' are flat and locally of finite presentation.
2. Fibre products are algebraic spaces by lem-trf-space-fibre-products-etale-covers.
Locally lift a point of B through B' ×_B G to show that B' to B is sheaf-surjective.
The map R' to Y = G ×_B B' forgetting the first B' coordinate is also
sheaf-surjective: locally lift the common base point of (a,b'_2) to b'_1.
3. Apply lem-sfb-space-sheaf-surjective-property-descent to R' to Y to B',
separately for flatness and local finite presentation. Thus Y to B' has both
properties; flatness of B' to B has not been assumed.
4. Choose a surjective etale scheme chart T to B. Sheaf surjectivity supplies an
fppf covering T_i to T lifting to B'. Form W as their disjoint union using
lem-weil-pbc-scheme-coproduct-family. By lem-sfb-stack-chartwise-smooth-etale-calculus,
W to T is flat and locally of finite presentation, and the covering makes it
surjective. The same calculus base changes Step 3 to G ×_B W to W. Algebraic
spaces are discrete algebraic stacks and their maps are representable, using
def-trf-algebraic-space, def-sfb-algebraic-moduli-stack and
lem-sfb-fibred-groupoid-representable-smooth-calculus. The pullback identification
sends ((a,b'),w) to (a,w), with inverse (a,w) to ((a,b'(w)),w).
5. Apply lem-sfb-representable-fppf-etale-open-descent over W to T, separately for
both properties, to obtain them for G ×_B T to T. The base-change identification
forgets the redundant T coordinate. Take any surjective etale scheme chart U of
G ×_B T. By lem-sfb-space-local-properties-chart-test, first over T and then
using T to B, both properties hold for G to B. No quasi-compactness is used.
For empty B all spaces over B are empty and the same chart tests apply. -/
theorem algebraic_classifying_stack_flatness {S : Scheme.{u}}
    {B G : AlgebraicSpace S} (p : G ⟶ B)
    (e : B.obj.obj ⟶ G.obj.obj) (i : G.obj.obj ⟶ G.obj.obj)
    (m : Limits.pullback p.hom.hom p.hom.hom ⟶ G.obj.obj)
    (F : BasedCategory.{max u v, max (u + 1) w} (Over S))
    (a : BasedFunctor (discreteModuli B.obj.obj) F)
    (presentation : SpaceGroupoidQuotientPresentation p.hom.hom p.hom.hom e i m F a)
    (hF : IsAlgebraicModuliStack F) :
    MapIsFlat p ∧ MapIsLocallyOfFinitePresentation p := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
