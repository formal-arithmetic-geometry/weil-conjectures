/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RationalTatePullback

/-! Composition of the normalized unshifted rational Tate-line comparisons. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients

attribute [local irreducible] coefficient line lineComparison CondensedRing.upperStar
  CondensedRing.upperStarComp

/-- The prescribed unshifted Tate-line comparison preserves composition.

Source: Cartesian coefficients, integral/rational/colimit paragraphs, and the
canonical-map compatibilities in the second rational projective-line triangle.

Proof: transpose the two linear maps under the module pullback adjunction and
forget the actions. The characterization in `linePull_existsUnique` reduces this
to composition of the prescribed abelian comparisons. For integral coefficients,
postcompose with every finite root projection. The normalization in
`spIntegralComparison_existsUnique` reduces the equality to composition of the
coefficient map and restriction of roots of unity. Both are the canonical pullback
maps, so functoriality of restriction proves the equality. Uniqueness of the map
to the inverse limit then gives the integral equation. For a finite rational
field, precompose with the scalar-extension quotient and use `rational_scalar`;
monoidality of the inverse-image compositor and the integral equation identify
the two maps on pure tensors. The scalar-extension adjunction makes this
precomposition injective on linear maps. For the closure, precompose with every
finite-field coprojection and use `qbar_coprojection`; the rational equations
identify the composites, and the colimit universal property gives equality.
The module compositor is the one obtained by conjugating the pushforward
compositor, so its adjunct is exactly the iterated adjunct used in this argument.
Faithfulness of forgetting actions and the adjunction bijection finish the proof.
Identity morphisms are covered by the same formulas; no properness or base-change
invertibility is used.
(blueprint: lem-sfb-rational-tate-line-comparison-composition) -/
theorem lineComparison_comp
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)] :
    (CondensedRing.upperStarComp (coefficient l c).X f g).hom.app (line l c Z) ≫
        (CondensedRing.upperStar (coefficient l c).X f).map (lineComparison l c g).hom ≫
        (lineComparison l c f).hom = (lineComparison l c (f ≫ g)).hom := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
