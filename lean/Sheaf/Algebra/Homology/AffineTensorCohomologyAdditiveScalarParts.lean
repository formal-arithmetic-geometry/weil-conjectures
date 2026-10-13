module

public import Sheaf.Algebra.Homology.RingTensorCohomology

/-! Intermediate additivity part of affine tensor cohomology. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace RingTensorCohomology

/-- Additivity of the two affine tensor cohomology functors.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-additive-parts)

Proof: Stacks Tag 06Y6 computes derived extension on K-flat models and makes
it an exact, hence additive, functor. The resolution augmentation identifies
source cohomology naturally with derived extension from R to B after restriction
from A, followed by homology. Thus additivity transports to source. For target,
ordinary tensor associativity identifies B tensor_R P with
(A tensor_R B) tensor_A P for the A-K-flat resolution P. The maps and inverses
are given on pure tensors, so the identification is natural in P and hence M.
This identifies target cohomology with derived extension from A to A tensor_R B,
followed by restriction to B and homology. These functors are additive, so
additivity transports to target by conjugation with the natural comparison.
The chosen resolution functor need not itself preserve addition. No flatness or
boundedness assumption is needed, and the same comparisons apply to zero rings
and zero complexes. -/
theorem affineTensorCohomology_additive_parts
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (source R A B i).Additive ∧ (target R A B i).Additive := by
  sorry

end RingTensorCohomology
