## What changed

Filled the two remaining proofs in `Sheaf.CategoryTheory.CyclicDerivedHomExactSequence`:
`cyclicDerivedHom_rightDerived_functorial` and
`cyclicDerivedHom_finite_composite_functorial`. All four existing public theorem signatures,
all definitions and all public imports are unchanged. Only this existing Lean module and its
own DAG node are changed; two new theorem modules and their nodes are added. There is no
shared-interface repair and no change record is required.

The private `rightDerived_shifts` lemma extracts unit-compatible shifts and triangulatedness
from the already proved `exists_unique_exactInputDerivedTransformation`, specialized to the
identity exact input. Triangulatedness supplies additivity. The existing additive-transport,
zero-shift forgetting and normalized-presentation calculations then assemble the right-derived
result from two separate steps: commutation with the cyclic action and preservation of a
strict off-diagonal presentation. These are the new public split lemmas below.

For finite composites, proved identity and composition formulas for the specified transport,
including its pasted forgetting comparison and stored composite shifts. Induction on
`Generated` proves additivity, action compatibility and compatibility with the raw boundary
at every pair of derived objects. Presentation uniqueness turns generator presentation
transport into raw-boundary compatibility. The final theorem evaluates normalized boundaries
only at the bounded endpoints. No intermediate boundedness hypothesis is introduced.

The new private helpers are completely proved. The only new proof imports are
`CyclicDerivedRightAction`, `CyclicDerivedRightPresentation`, and
`ExactInputDerivedTransformation`. All existing imports are still used.

Validation: both new theorem modules compiled (3.7 s and 3.3 s); the corrected item
compiled with no warnings or errors in 13.6 s. Dependency traversal confirms that neither
new node nor the exact-input theorem has a path back to the parent. The delivery tool
performs the final compile and axiom/preflight checks.

## Proved and sorry left

This is a decomposition, not a net hole reduction: two existing holes closed and two strictly
smaller holes added. The item now contains zero `sorry`.

Closed:

- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHom_rightDerived_functorial`
  (node `lem-sf-cyclic-derived-hom-exact-sequence`).
- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHom_finite_composite_functorial`
  (the same node).

Added and still `sorry`:

- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedHomTransport_rightDerived_action`,
  in `Sheaf.CategoryTheory.CyclicDerivedRightAction`,
  node `lem-sf-cyclic-derived-right-action`.
- `CategoryTheory.Endofunctor.IsoAlgebra.cyclicDerivedOffDiagonalPresentation_mapRightDerived`,
  in `Sheaf.CategoryTheory.CyclicDerivedRightPresentation`,
  node `lem-sf-cyclic-derived-right-presentation`.

Each is the whole proof of one public theorem, with its source, proof in words and matching
DAG node. Neither theorem mentions a normalized boundary family or states the parent's
four-clause conclusion. The action lemma is one algebraic equality in each degree. The
presentation lemma concerns strict representatives and their canonical SES connecting map.
The parent separately constructs the shift witnesses, proves additivity and forgetting,
evaluates normalized families, and performs the finite-word induction.

The pre-existing boundary-existence and exact-functor proofs are preserved.

## No longer needed

No Lean import was removed, no existing module is withdrawn, and no adopted source-library
declaration is removed or altered.

Removed these direct parent proof dependencies: `def-sp-injective-resolutions`,
`lem-weil-pbc-dplus-injective-representative`, `def-weil-abstract-derived-category`,
`lem-weil-pbc-kinjective-hom-derived`, `lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-complex-ses-triangle`, `lem-sf-exact-functor-derived-triangulated`,
`def-sfb-right-derived-functor`, `lem-pc-right-derived-functor-triangulated`,
`lem-sf-fixed-pair-derived-forget-comparison`, and
`def-weil-endofunctor-fixed-pair-category`. Definitions still needed to state the theorem
remain in `stmt_deps`. Most of these facts remain needed transitively by the data, the
previous presentation lemmas, the new split statements or the exact-input theorem; they
are not claimed globally pruned.

In particular, the lower-bounded injective-model route and its cohomology-long-exact step
are unnecessary for the new composition proof. Unbounded K-injective models with injective
terms, the degreewise split homotopy triangle, and presentation uniqueness replace them.
The ordinary canonical right-derived shift theorem is not directly invoked: the existing
arbitrary-resolution exact-input theorem gives the required universe-polymorphic witnesses.

Removed the parent's seven obsolete `tool_uses` entries, all absent from its new direct
proof dependencies: `lem-sf-fixed-pair-derived-forget-comparison`,
`lem-weil-pbc-dplus-injective-representative`, `lem-weil-pbc-kinjective-hom-derived`,
`lem-weil-pbc-complex-ses-triangle`, `lem-sf-exact-functor-derived-triangulated`,
`lem-pc-right-derived-functor-triangulated`, and
`lem-weil-pbc-complex-ses-homology-long-exact`. No approval was added or reordered.

## Where the brief, the DAG or earlier work was wrong

The old remaining plan used only bounded-below models to handle intermediate images. The
already stated raw off-diagonal presentation calculus has no boundedness requirement. Its
stronger interface permits a direct induction on the generated word, with normalized
boundary families used only at its endpoints. This changes the proof below the unit level;
the unit record has no realized statement or step assigned to this auxiliary node, and
its geometric biduality route is unchanged.

Checked edge cases of the new split statements: the zero morphism, zero objects, arbitrary
positive and negative shifts, and exact functors as a special case are consistent with the
specified transport. An arbitrary shift structure would not suffice; both new lemmas
explicitly retain `hσ`, commutation of the recorded derived unit with shifts. Since that
unit is invertible on K-injective models, it fixes the comparison there. For presentation
transport, the replacement extension can change: it is not asserted that a merely left
exact functor preserves an arbitrary original short exact sequence. Choose K-injective
models with injective terms, use a degreewise split triangular extension, and then invoke
uniqueness of its native boundary.

Mathlib and source searches found ordinary Ext maps, exact localization comparisons and
canonical SES triangles, but no right-derived fixed-pair action or strict-presentation
transport theorem. The public exact-input theorem supplies shifts and triangulatedness;
its private helper was not accessed or duplicated. No false-statement repair is proposed.

## New nodes

`lem-sf-cyclic-derived-right-action`, in the parent's chapter and unit, records commutation
of right-derived transport with conjugation, for the prescribed unit-normalized forgetting
comparison and any unit-compatible underlying shift structure. It has no boundary-family
or boundedness hypothesis. Its proof uses K-injective Hom computation and the equivariant
structure equation.

`lem-sf-cyclic-derived-right-presentation`, in the same chapter and unit, records transport
of the underlying shifted class and native connecting morphism of a strict presentation.
It uses K-injective models with injective terms, the degreewise split triangular extension,
the signed cone formula, and the unit-normalized comparison. It neither assumes nor
concludes the parent's functoriality predicate. Both nodes record this session's searches
and full proof steps; both modules contain one named public theorem and no definitions.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
