/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.CategoryTheory.HomogeneousPolynomialBarModel
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-! # Homogeneous polynomial evaluation and inhomogeneous normalization

Source: latest blueprint, six-functors basics, direct-images proof paragraph (3),
agent-formulated polynomial evaluation sub-obligation
(blueprint: lem-sfb-homogeneous-polynomial-bar-evaluation).

The all-continuous homogeneous evaluation map is an equivariant augmented cochain map.
Its restriction to fully fixed sections, transported by consecutive differences and
prefix sums, is exactly the existing polynomial evaluation specification. No higher
acyclicity, completion or finite-subextension restriction is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Profinite.CondensedAction.HomogeneousPolynomialBar

/-- Homogeneous polynomial evaluation exists over both coefficient fields, preserves the
constant augmentation, and normalizes to inhomogeneous polynomial evaluation on all slices.
The objects and maps in `Data` are fixed by coproducts, actual internal Hom, prescribed
actions, deletion, fixed-section inclusions, differences and prefix evaluation.
Source: latest blueprint, direct-images proof paragraph (3), polynomial evaluation input
(blueprint: lem-sfb-homogeneous-polynomial-bar-evaluation).

Proof:
1. Interpret the finite polynomial substitutions internally using
   def-weil-pbc-mv-polynomial-ring. The coproduct universal property extends them from
   monomial summands. Two successive deletions in the two orders have opposite signs,
   giving delta squared zero. Deletion commutes with translation, and the constant
   augmentation is a cocycle. Use def-sfb-condensed-action-module for equivariance.
2. A monomial determines a homogeneous internal function by its evaluation on every
   profinite slice. Each lattice coordinate embeds continuously in F, so finite products
   of its powers with all continuous section coefficients are continuous. Restriction
   is precomposition and preserves these formulas. Use the actual free-module generators
   and internal Hom of def-sfb-condensed-homogeneous-functions and the natural-family
   interpretation of def-sfb-condensed-equivariant-bar-data. Multiplication by this
   section and the coproduct universal property give the internal linear evaluation.
3. Evaluating after substitution y_a-g agrees on coefficients and variables with
   translating every argument by -g. This proves equivariance on every profinite slice,
   with the trivial coefficient action, rather than only on global points.
4. Evaluation commutes with each deletion, since the two evaluation homomorphisms agree
   on coefficients and variables. Alternating sums give the cochain-map equation.
   Constants evaluate to constants, proving ea=b, including the cocycle augmentations.
5. Apply lem-sfb-homogeneous-polynomial-invariant-coordinates to the same polynomial
   coproducts. Consecutive differences identify P with the fully fixed subcomplex of K;
   the inverse uses prefix sums starting at zero. Invariance includes all base changes.
6. On invariant homogeneous functions, prefix evaluation has inverse precomposition
   with consecutive differences. Differences are translation invariant. Translating a
   tuple by its first entry shows the other composite is the identity on every slice.
   Both maps are internal linear maps by the slice-family description.
7. Deleting the initial prefix sum drops the first increment after translation;
   deleting an interior prefix sum adds adjacent increments; deleting the last drops
   the last increment. With the same signs these are exactly the inhomogeneous bar
   faces of def-sfb-condensed-equivariant-bar-data. Hence prefix evaluation is a
   cochain isomorphism, and evaluation restricts to the displayed fixed-subcomplex map.
8. Consecutive differences of the prefix tuple are exactly its increments. Thus the
   composite sends each coefficient monomial to its prescribed polynomial evaluation
   after every base change, giving `rho` and its normalization equation. In degree zero
   all products are empty and the augmentation is the given constant inclusion. For
   rank zero every term is A and the differential is the alternating sum of identity
   maps, on both sides. All sums used are finite; completeness is never used, and all
   continuous Omega-valued coefficients, including locally finite sheaf sections, remain.
-/
theorem homogeneous_polynomial_bar_evaluation (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] (r : ℕ) :
    Nonempty (Data ell E r) ∧ Nonempty (Data ell Ω r) := by
  sorry

end Profinite.CondensedAction.HomogeneousPolynomialBar
