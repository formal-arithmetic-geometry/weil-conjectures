/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientCoherenceData

/-! # Scalar tower and unit equations for the fixed smooth-purity source maps

Source: the identity and successive coefficient changes in the coefficient-change
proof, as required by its source comparison.
(blueprint: lem-pur-condensed-source-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.PurityCoefficientChange

/-- The specified tensor/pullback/Tate source comparisons respect the actual
scalar tower and unit isomorphisms.

Source: sk-thm-purity-transport-coefficient-change, coefficient comparisons and
successive changes; parent proof Steps 7 and 9
(blueprint: lem-pur-condensed-source-coherence).

Proof in words:
1. For ordinary module extension along a then b, the scalar associator is the
counit-compatible identification with extension along ab. Its balanced-tensor
formula sends c tensor (b tensor m) to cb tensor m. The identity scalar unitor
sends 1 tensor m to m. Prove these formulas by the extension/restriction Hom
bijection. They also show that both comparisons are monoidal for the
scalar-unit-normalized tensorators.
2. The normalized first Tate-line comparison is scalar association from the
integral root-tower line. Applying the associativity formula to that line proves
its coefficient tower and unit identities. Induct on the tensor power d, using
monoidality from Step 1; d=0 uses the monoidal unit equation. The normalization
fields of P identify its power maps with these maps, for every allowed arrow.
3. Derive these identities using K-flat representatives. The comparison from
ordinary single objects to their derived scalar extensions is the adjunct of
the ordinary unit. Therefore the derived associator specified by scalarSixTower
is this same comparison: conjugating back gives the specified transitivity of
restriction of scalars. The same argument identifies scalarUnit. Single and
shift preserve the identities, giving the tower and unit equations for
scalarLineMap, including the prescribed shift by 2d.
4. The normalized scalar/pullback comparison is theta, by thetaNormalization.
Its tower equation is ScalarSixPullbackData.tower. Its identity equation follows
by taking the mate of the restriction-of-scalars identity comparison; naturality
of the scalar unit and the two adjunction identities give exactly that equation.
Transport across leftDerivedUpperStarIsoMapDerivedCategory on both sides.
5. Expand sourceMap into its inverse tensorator and the tensor product of the
pullback and line comparisons. Use the monoidal tower/unit equations from
Steps 1 and 3, then substitute Steps 2 and 4. Naturality moves the scalar
associator or unitor past the tensor factors. Reassociate to obtain precisely
SourceCompositionCoherent and SourceIdentityCoherent. The argument uses no
flatness of a coefficient map and applies also to d=0 and the zero ring. -/
theorem source_coefficient_coherence (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (P : Coordinates.{u} ell) :
    SourceCompositionCoherent ell D P ∧ SourceIdentityCoherent ell D P := by sorry

end AlgebraicGeometry.ProEtale.PurityCoefficientChange
