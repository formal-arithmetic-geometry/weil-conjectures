/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData

/-! # Two-level finite smooth reduction

Source: main-20261015, sk-prop-sp-orientation and sk-lem-sp-reduction/compatibilities
(blueprint: lem-pur-finite-smooth-two-level-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Two-level reduction of the specified finite smooth maps.
Source: sk-lem-sp-reduction-exceptional and sk-lem-sp-reduction-compatibilities (3)
(blueprint: lem-pur-finite-smooth-two-level-reduction).
Proof: construct the root comparison by the ell^(r-m) power map. Its inclusion in
G_m and its values on scalar/root generators fix the sheaf comparison; derive the
actual scalar counit and iterate its normalized tensor and shift comparisons. Do
this for every positive quotient and apply finiteSmoothQuotientCoherence to obtain
the compact-support cocycle needed by exceptional_coefficient_comparison.
The projective-line Kummer and diagonal classes reduce to their counterparts, and
the splitting has free rank-one summands. Thus the ordered affine-line counits and
bundle integration commute with reduction. For the diagonal deformation, transport
diagonalOrientationCompatibility from its single lifted coefficient presentation to
the double lift here. The actual scalar comparison on the family has the specified
one-fibre transpose. Uniqueness of normalized specialization identifies its zero
fibre. Paste with the diagonal smooth-base-change mate and inverse bundle comparison.
Substitute both supplied OrientationNormalized equations and cancel the invertible
factors. This proves the unit-orientation coefficient equation for a.alpha and b.alpha.
Tensor compatibility of exceptional_coefficient_comparison, composed with this unit
equation, gives ordinary_purity. Its other three edges are invertible, so the actual
exceptional mate is invertible. Its defining adjunction gives the counit equation.
For reduction_ctf on arbitrary T use scalarExtensionFunctor_preserves_constructible_tor,
which has no invertibility hypothesis on T. Canonical realization and uniqueness of
scalar left adjoints identify its extension with proScalar; finite homology support
and bounded intervals are equivalent. On X and Y the stronger ordinary-origin result
of finiteReduction_constructibility also applies. Canonical tensor/pullback comparisons
commute reduction with inverse image. Transport the compact, exceptional and purity
maps through exact site comparison and scalar comparison. The actual ordinary-origin
counits are invertible on this domain. Adjoint transposition identifies transported
counits and naturality, and cancellation of origin counits gives the pro equations.
All maps retain their original formulas; equal positive levels and zero inputs are
included. This is the source's two-level coefficient argument. -/
theorem finiteSmoothTwoLevelReduction
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (r m : ℕ) (hm : 1 ≤ m) (hmr : m ≤ r)
    (a : Level ell r f d) (b : Level ell m f d) :
    Nonempty (ReductionData (FiniteReduction.quotient ell hmr) f d a b) := by sorry

end AlgebraicGeometry.Etale.FiniteSmoothPurity
