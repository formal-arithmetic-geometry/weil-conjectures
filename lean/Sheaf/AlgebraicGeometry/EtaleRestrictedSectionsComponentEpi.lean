module

public import Sheaf.AlgebraicGeometry.EtaleRestrictedSectionsFactors

/-! # Degreewise epimorphism of the restricted sections lift

Source: Stacks Project, Tag 015J, total-complex comparison and column filtration.
(blueprint: lem-weil-pbc-etale-restricted-sections-component-epi).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The restricted sections factor map is epimorphic in every degree.
Source: Stacks Project, Tag 015J, proof remark (3), finite diagonal comparison.
(blueprint: lem-weil-pbc-etale-restricted-sections-component-epi).
Proof: Write J for the full mapped bicomplex after flipping. The second-filtration
step in degree n is the finite supremum of the images of its coprojections at
(n-s,s), q ≤ s ≤ n. For each retained s the stupid-truncation inclusion is an
isomorphism on the resolution complex in degree s. Applying sections and extension
by zero therefore identifies the restricted summand with the full summand.
The total inclusion composed with its restricted coprojection is the full
coprojection under this identification. The full coprojection thus factors through
the total inclusion, so each generating image lies in the image of that inclusion.
Conversely every restricted coprojection maps into one of those generating images:
if s < q or n-s < 0 its source is zero; otherwise q ≤ s ≤ n. The total coproduct
universal property gives the converse image containment. Hence this image is
exactly the finite supremum. The explicit comparison is an isomorphism and does
not change the image on precomposition. T.filtration_formula identifies the image
with the degree-n step. Evaluating factorThru_arrow gives the factorization through
that step, which is therefore epic in AddCommGrpCat. If n < q the supremum and
restricted total are zero. Negative q and zero summands satisfy the same argument. -/
theorem etaleRestrictedSectionsLift_component_epi
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    Epi (((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
      (etaleRestrictedSections_factors X K T q)).f n) := by
  sorry

end AlgebraicGeometry.Etale
