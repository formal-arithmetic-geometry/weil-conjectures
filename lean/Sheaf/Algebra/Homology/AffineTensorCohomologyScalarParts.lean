module

public import Sheaf.Algebra.Homology.RingTensorCohomology

/-! Intermediate scalar transport part of affine tensor cohomology. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace RingTensorCohomology
/-- The original-base scalar formulas for affine tensor cohomology.
Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-scalar-parts)

Proof: Use the natural K-flat computation of derived extension from R to B
(Stacks Tag 06Y6) to identify source with its cohomology after restriction from A.
Restriction sends algebraMap R A r times identity to r times identity.
The scalar identity of exists_baseDerivedExtension_linear therefore gives the
source formula. For target use ordinary tensor associativity on the A-K-flat
resolution to identify it with cohomology of derived extension from A to
A tensor_R B, restricted to B. The pure-tensor formulas make this comparison
natural. Apply exists_baseDerivedExtension_linear over A to algebraMap R A r.
Balancing in A tensor_R B identifies its image with includeRight
(algebraMap R B r); restriction therefore gives the required B scalar.
For either comparison, naturality for the scalar endomorphism gives a conjugate
of the derived scalar map. Comparison components are B-linear, so cancellation
of their isomorphisms gives precisely the displayed equality for the existing
functor. The argument also covers r = 0, r = 1 and zero coefficient rings. -/
theorem affineTensorCohomology_scalar_parts
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (source R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((source R A B i).obj M)) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (target R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((target R A B i).obj M)) := by
  sorry
end RingTensorCohomology
