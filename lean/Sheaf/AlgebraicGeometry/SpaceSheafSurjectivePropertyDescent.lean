/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O2
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus

/-! # Descent through an fppf sheaf surjection

Source: Stacks Project, Descent on Spaces, Tag 06NR, lemma-curiosity
(blueprint: lem-sfb-space-sheaf-surjective-property-descent).

The three allowed scheme properties are extended by the existing universal étale chart
predicate. Surjectivity means local lifting of sections on the big fppf site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Flatness, local finite type and local finite presentation descend from a composite
through a morphism surjective as an fppf sheaf. The disjunction selects one property at a
time; no morphism property is imposed on the sheaf surjection itself.

Source: Stacks Project, Descent on Spaces, Tag 06NR, lemma-curiosity
(blueprint: lem-sfb-space-sheaf-surjective-property-descent).

Proof:
1. Choose surjective étale scheme charts W → Z and V → Y ×_Z W. Put
   A = X ×_Y V and choose a surjective étale scheme chart U → A.
   By lem-trf-space-fibre-products-etale-covers these fibre products are algebraic
   spaces. By lem-trf-space-representable-etale-scheme-tests, U → X ×_Z W is
   surjective étale. The chart test lem-sfb-space-local-properties-chart-test applied
   to the composite gives P(U → W).
2. Local surjectivity supplies an fppf covering V_i → V and lifts V_i → X over Y.
   Pair each lift with V_i → V to obtain V_i → A, and form D_i = V_i ×_A U.
   Representable surjective étale base change makes D_i a scheme and D_i → V_i
   surjective étale. Clauses (1), (3), (4) of lem-sfb-space-fppf-covering-calculus
   give an fppf covering D_i → V. Its members factor through U → V because the
   two projections to A agree. No property of U → V is required.
3. Apply lem-sfb-scheme-fppf-refinement-property-descent (Stacks Tag 06NB) to
   U → V → W and that refinement, obtaining P(V → W). Apply
   lem-sfb-space-local-properties-chart-test to conclude P(Y → Z).
   This argument applies separately to each of the three indicated properties. -/
theorem sheaf_surjective_property_descent {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u})
    (hP : P = @Flat ∨ P = @LocallyOfFiniteType ∨ P = @LocallyOfFinitePresentation)
    {X Y Z : AlgebraicSpace S} (a : X ⟶ Y) (b : Y ⟶ Z)
    (hab : MapIsLocally P (a ≫ b))
    (ha : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a.hom.hom) :
    MapIsLocally P b := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
