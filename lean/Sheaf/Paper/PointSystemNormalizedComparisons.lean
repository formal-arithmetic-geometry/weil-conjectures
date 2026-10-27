/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.Paper.PointSystemInsertionData

/-! # Normalized comparisons for coefficient systems

Source: Stacks Tags 03CB, 0H7J and 0941; the indicated steps of the parent proof.
(blueprint: lem-trf-point-system-normalized-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
attribute [local irreducible] HasDerivedCategory.standard
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PointSystemInsertion
variable (k : Type t) [Field k] (h : Aut (Spec (.of k)))
  (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] G sections

/-- Normalized sheaf and tensor comparisons, before constructing any point insertion.
Source: Stacks 03CB, 0H7J, 03D2, 03EK and 0941; steps 1, 3 and 4 of
`lem-trf-point-system-insertion-composition`.
(blueprint: lem-trf-point-system-normalized-comparisons).

Proof: use the postcomposition site equivalence to reindex every underlying sheaf.
The site compositor is restriction along the equality of the two postcomposed
structure maps. Transport the scalar actions by the inverse coefficient maps.
The assumed coefficient composition identity says exactly that this restriction
is linear; its inverse is the inverse site restriction. This constructs d.
Perform the identical construction on the product of the coefficient index and
site to obtain t. Reindexing preserves the original horizontal maps, including
zero or non-cartesian transitions, so t is a morphism of entire strict systems.
For b, the two actions on a section at level n are obtained from the completed
coefficient projection by the two sides of the assumed projection equation.
They agree; the identity additive map is therefore linear. Naturality and
compatibility with every original transition are identities on underlying maps.
The restriction composition square likewise consists of the same restrictions,
so extensionality on each section proves it.
For j, identify reindexed inverse image with tensor pullback using the normalized
graph insertion. Extension of scalars along the finite coefficient isomorphism
has inverse sending x tensor a to c inverse(a) times x. Thus the graph comparison
is a natural isomorphism with precisely the displayed generator normalization.
The adjunction-normalized tensor compositor sends two unit insertions to one;
uniqueness of the specified pullback comparison identifies it with tensorCompositor.
Finally tensorTransition is conjugation of the original underlying transition
by j. Its value on a unit insertion cancels the inverse j. Semilinearity of the
original transition and compatibility of the coefficient maps with reduction
then give the displayed scalar formula. This argument applies also to a zero
transition, exponent one, and the identity automorphism. The unused fields u and
I can be zero here: this assertion constructs no strict or derived insertion. -/
theorem pointSystemNormalizedComparisons [IsAlgClosed k]
    (_hc : CoefficientLaws k h l E) :
    ∃ P : Maps k h l E,
      SectionLaws k h l E P ∧ RestrictionCompositionLaws k h l E P ∧
        TensorLaws k h l E P ∧ TransitionLaws k h l E P := by sorry

end WeilConjectures.PointSystemInsertion
