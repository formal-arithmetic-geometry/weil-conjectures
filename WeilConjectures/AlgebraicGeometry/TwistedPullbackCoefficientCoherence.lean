/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.TwistedPullbackSquareCoordinates
public import WeilConjectures.AlgebraicGeometry.TwistedPullbackSquareShiftEquations

/-! # Normalized coefficient and shift coherence of twisted pullbacks

Source: purity transport, common presentations and unit, tower and shift calculations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TwistedPullbackScalars
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {X X' Y Y' : Scheme.{u}}
  [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
  [Fact (∃ n : ℕ, topologicalKrullDim X ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim X' ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y ≤ n)]
  [Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ n)]
  [Fact (∀ x : X, IsUnit (l : X.presheaf.stalk x))]
  [Fact (∀ x : X', IsUnit (l : X'.presheaf.stalk x))]
  [Fact (∀ y : Y, IsUnit (l : Y.presheaf.stalk y))]
  [Fact (∀ y : Y', IsUnit (l : Y'.presheaf.stalk y))]
variable
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ x : X', Invertible (l : X'.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
  [∀ y : Y', Invertible (l : Y'.residueField y)]
  (u : X' ⟶ X) (f : X ⟶ Y) (f' : X' ⟶ Y') (v : Y' ⟶ Y)
  (sq : u ≫ f = f' ≫ v) (d : ℕ)

attribute [local irreducible] D rationalDerivedPullback

/-- The common normalized presentations and the coefficient and shift laws.
This contains no scalar-square equation and requires neither a Cartesian square
nor smoothness. Source: purity transport, Steps 1 and 8--10 of the scalar-square
calculation; Stacks 099N and 0D6D.
(blueprint: lem-pur-twisted-pullback-coefficient-coherence).

Proof: Restrict exact coefficient relabeling to the constructible integral
categories and localize its hom maps on pure tensors to obtain the presentations.
Use the simultaneous framework/PBC bridge: its whole-tower pullback identity and
zero shifted coordinate give PullCoordinates, and its chi-normalized scalar map
gives ScalarCoordinates and PullScalarCompatible in the inverse PBC direction.
Relabel the actual Tate line term by term. Remove completion on a flat K-flat
representative, collapse the degree-zero tensor factor, and descend the resulting
natural tensor-to-termwise isomorphism beta. Transport the canonical termwise
shifts through beta and localize; these are ShiftData, and give TwistCoordinates.
For p and q the unit law is multiplication by one, and the tower law is
associativity of balanced scalar multiplication. For q check each ordered Tate
factor, with the empty tensor using the same coefficient unit. Whisker and paste
these laws to get PU, PV, a, rA and rB; naturality moves the associators through
the intervening comparisons. The signed cochain pullback/tensor and completed
scalar shift comparisons commute with every tower map. The Tate factor has degree
zero and the shift is 2d, so these descend to all family shift laws and to the
shift laws of z and t. Pasting those last two gives the shift law of m. This
constructs ShiftCoherence and SquareShiftEquations with the same beta, as required.
All equal-field inclusions, d=0, negative shifts and empty schemes are included. -/
theorem twistedPullbackCoefficientCoherence :
    ∃ s : ShiftCoherence l Ω u f f' v d,
      Nonempty (SquareCoordinates l Ω u f f' v d s) ∧
      TowerCoherence l Ω u f f' v d ∧ SquareShiftEquations l Ω u f f' v sq d s := by sorry

end WeilConjectures.TwistedPullbackScalars
