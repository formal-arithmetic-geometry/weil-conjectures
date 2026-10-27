## What changed

Filled the eight construction and functoriality holes in
`Sheaf.Paper.IntegralHeartLocalModel`. Constant scalar sections preserve the unit and
multiplication by the existing sheaf-to-presheaf monoidal comparison equations.
Constant module presheaves are additive pointwise. The constant ring sheafification
unit remains locally injective and surjective after forgetting commutativity, since
the equalizer and image sieves are unchanged.

Scalar-extension identity and composition follow from sectionwise tensor functoriality
and functoriality of sheafification. A proved private helper establishes additivity
of scalar extension using its sectionwise extension/restriction adjunction and exact
module sheafification. Point realization is the composite of additive functors;
scheme realization additionally uses the finite-limit-preserving inverse image.
Added only the private proof import `Mathlib.CategoryTheory.Adjunction.Additive`.
Existing public signatures, definition bodies, public imports and attributes are unchanged.

The original module has nine holes. This is a partial module delivery: the eight
construction lemmas are closed, while the geometric theorem is unchanged. It adds no
intermediate statements with holes and does not claim to have proved that theorem.

## Proved and sorry left

Closed eight original holes, all in namespace `AlgebraicGeometry.ProEtale`:

- `integralHeartScalarSection_one`
- `integralHeartScalarSection_mul`
- `integralHeartConstantPresheaf_additive`
- `integralHeartConstantUnit_isLocallyInjective`
- `integralHeartConstantUnit_isLocallySurjective`
- `integralHeartExtension_laws`
- `integralHeartPointRealization_additive`
- `integralHeartRealization_additive`

The private helper `integralHeartExtension_additive` is also proved.
Added holes: zero. Split-off holes: zero.
The one remaining original hole is
`AlgebraicGeometry.ProEtale.integralHeartLocalModel`, node
`det-lem-int-integral-heart-local-model`, with its original statement, source and
natural-language proof unchanged.

Validation: the completed eight proofs compiled through `lcompile.py`; a final
warning-free compile and delivery preflight validate the final formatting.

## No longer needed

None. No imports, declarations, modules or DAG nodes are withdrawn. The existing
geometric proof-dependency imports are retained for the unchanged remaining theorem;
their necessity cannot be decided from the eight construction proofs alone. The
new proofs use the existing tensor/sheafification and monoidal-comparison APIs and
require no new geometric dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement correction is made. The remaining geometric proof requires explicit
presentation comparisons: `integral_cohomological_adic_criterion` and
`adic_stratified_perfect` use modules over `adicLisseCompletedRing` and slice-site
restrictions; this module uses internal modules over the pulled-back condensed ring,
the canonical small presentation of an arbitrary finite extension, and scheme covers.
Likewise `integral_models` is stated for embedded finite intermediate fields and its
completeness predicate is not definitionally the small-coefficient Roos predicate here.
These are meaningful comparison obligations, not reasons to reject the dependencies
because their proofs are unfinished. No duplicate comparison axiom or repackaged copy
of the local-model theorem is introduced.

Searches through `msearch.py` (Lean Finder, Loogle and grep) and the library found the
sectionwise scalar-extension functoriality/additivity arguments and monoidal comparison
lemmas used above. Lean Finder's local-model search returned generic derived-category
bounded-representative results, not the stated geometric comparison theorem.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
