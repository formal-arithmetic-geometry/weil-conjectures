/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q15
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Composition of finite-type morphisms of algebraic spaces

Source: Stacks Project, Morphisms of Spaces, Tag 03XG, finite-type clause;
Tags 0AML, 03MJ and 03HG (blueprint: lem-sfb-space-finite-type-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The composite of two finite-type morphisms of algebraic spaces is of finite type.
Source: Stacks Project, Morphisms of Spaces, Tag 03XG, finite-type clause
(blueprint: lem-sfb-space-finite-type-composition).

Proof, following the four steps of the node:
1. Let P be local finite type for schemes. It is etale local on source-and-target by
   lem-sfb-scheme-etale-source-target-properties. Choose a surjective etale scheme atlas
   W of Z, then an atlas V of Y ×_Z W, and an atlas U of X ×_Y V. Pullback and composition
   of coverings give compatible etale surjective charts U → X, V → Y and W → Z
   [def-trf-algebraic-space, lem-trf-space-fibre-products-etale-covers,
   lem-trf-space-chartwise-etale-permanence]. By lem-a1-space-point-open-calculus,
   point surjectivity agrees with surjectivity on scheme base changes here. The chart
   tests in def-sfb-space-morphism-properties give P for U → V and V → W.
2. Scheme composition preserves P by clause (e) of lem-weil-pbc-proper-fp-permanence.
   This gives a presentation of the composite whose top map has P. P respects
   isomorphisms by its affine-cover definition [def-weil-finite-type-morphism]. Apply
   lem-sfb-space-etale-presentation-property-criterion and the locality from step 1 to
   obtain the chart test for the composite [def-sfb-space-morphism-properties].
3. For an affine T → Z, put A = Y ×_Z T and B = X ×_Z T. Quasi-compactness of g makes
   |A| compact. Choose a surjective etale affine atlas E → A using
   lem-sfb-qc-space-affine-etale-atlas. Quasi-compactness of f makes the point space of
   D = X ×_Y E compact [def-sfb-proper-curve-moduli, def-sfb-space-morphism-properties].
   The canonical identification D ≅ B ×_A E follows by forgetting or inserting the
   forced T coordinate on sections. Pullback of the cover E → A makes D → B a cover
   [lem-trf-space-fibre-products-etale-covers]. Its point map is continuous and
   surjective by lem-a1-space-point-open-calculus.
4. Pull an open cover of |B| back to |D|, choose a finite subcover by compactness, and
   use surjectivity to see that the same finite original opens cover |B|. Thus every
   affine test of the composite has compact point space, giving quasi-compactness
   [def-sfb-proper-curve-moduli]. Combine with step 2 to obtain finite type
   [def-sfb-space-morphism-properties]. Empty spaces are included: an atlas of an
   empty A may be empty, and the compactness argument still applies. -/
theorem mapIsFiniteType_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : MapIsFiniteType f) (hg : MapIsFiniteType g) :
    MapIsFiniteType (f ≫ g) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
