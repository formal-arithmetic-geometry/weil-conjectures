/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ExceptionalRefinement.ExceptionalRefinementMatesData

/-! # Normalized geometric left refinement comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalRefinement
open WeilConjectures.ConstructibleExceptionalCoefficients

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  (D : FiniteFieldDatum.{max u v}) (hl : l ≠ D.p)
  {X Y : Scheme.{max u v}} {f : X ⟶ Y}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  {c d : Compactification f}

/-- Existence of only the left refinement maps, with their ring and field normalizations.
Source: Zheng 2.23, 2.29, 3.16, 5.22 and 5.24; Stacks 0F7B and 0F7I;
retained refinement proof steps 1, 3, 4 and 6--8
(blueprint: lem-sf-exceptional-refinement-left-construction).

Proof: At finite coefficients use compactification coherence on the etale-origin input.
Its proper/open comparison is the unique transpose of the open unit. Invert it and
compose with proper direct-image composition; full faithfulness of the full finite-Tor
inclusion lifts the result to the given left operations. The coefficient/site refinement
mate identifies this comparison with its prescribed ambient normalization. At integral
coefficients form the same proper/open word on reduction systems. Reconstruction gives
normalized inputs with etale-origin levels and uniform bounds, and system transport
gives the same properties at the open/proper intermediates. Finite evaluation detects
invertibility of this word. Its total-limit realization, conjugated by A.left and B.left,
therefore lifts to a unique left isomorphism and satisfies the displayed open-unit
normalization. Open/clopen cochain shift models, adjoint shift uniqueness and realization
shift coherence give the shifts of these left maps. The proper/open scalar square,
whiskered by the proper image, and its compositor equation give coefficient compatibility
before total limit; keep ramified levels en and pass by their cofinality. Localize these
actual integral maps. Naturality on a fraction is integral naturality multiplied by the
inverse denominator. The prescribed localization normalizations give the rational
formula. On a common-field object use the rational component conjugated by the two
prescribed q comparisons. Every arrow is represented over a common finite field;
the scalar square and commonTransitionNormalized prove independence under enlargement
and naturality there.
Inverses and shifts descend by the same construction, giving the common-field formula.
This constructs no right adjoint map and asserts no system-realization package. Empty
schemes and identity refinements use the same units and comparisons, with no positive
dimension or nonempty hypothesis. -/
theorem exceptional_refinement_left_construction
    (A : Transport.{u, v} l Ω D hl c) (B : Transport.{u, v} l Ω D hl d)
    (r : c.Refinement d) : Nonempty (LeftMates.{u, v} l Ω D hl A B r) := by sorry

end WeilConjectures.ExceptionalRefinement
