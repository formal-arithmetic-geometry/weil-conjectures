## What changed

Proved `CategoryTheory.regularQuotientCompletionUnit_criterion` from the existing
ringed completion reflector and a separate normalized comparison of its singleton
Koszul presentation with the principal negative-cone presentation.

The main module proves the regular cone-to-cokernel quasi-isomorphism, tensors it
using the given K-flatness, and proves that exact products and the cone triangle
preserve this comparison under strict Roos completion. Naturality through the
ordinary-limit inclusion identifies the actual zero-coordinate units. An abstract
reflection argument gives the completeness criterion. The localized mapping-cocone
triangle gives the prescribed quotient projections; conversely, a triangle
comparison extending identities on both product vertices proves completeness of P,
which then makes its specified unit invertible.

Added `PrincipalKoszulRoosReflector`: its proof constructs the singleton generating
sections on slices, constructs the tower derived category in the required universe
using local smallness and K-injective resolutions, applies the existing reflector,
and transports its Hom bijection and completeness through the model comparison.

Added `PrincipalKoszulRoosPresentationComparison`, with the explicit strict principal
Koszul Roos unit and the normalized model-comparison statement. This comparison
isolates the dual finite-Koszul calculation; it has no completeness conclusion and
requires neither a regular section nor K-flat coefficients. Existing public
signatures are unchanged. The quotient-unit body is factored through the same
generic strict tower construction, definitionally equal to its original body. Local product
instances and generic abelian-category helper proofs keep elaboration from
repeatedly unfolding sheaf-module constructions. Local irreducibility settings
reduce the helper check to 17 seconds; the full main file compiled in 34 seconds
with the normal 60-second server limit. Its elaboration heartbeat budget is raised
for the accumulated concrete-tower and derived-product conversions.

Validation: all three delivery modules compile cleanly (14.3, 15.8, and 29.9
seconds). The unchanged `FiniteFreeQuotientCompletion` consumer compiles in 7.7
seconds. A separate `rfl` check against the exact original quotient-unit body
compiles in 26.7 seconds, verifying definitional equality. The consumer copy and
validation-only module are removed from the packet.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.regularQuotientCompletionUnit_criterion` (one of one original holes).
Also proved the new `CategoryTheory.principalKoszulRoos_reflector`.

Added one hole:
`CategoryTheory.principalKoszulRoos_presentation_comparison`, node
`lem-pur-principal-koszul-roos-presentation-comparison`. This is a decomposition,
not a net hole reduction: one original hole closed and one separate model-comparison
hole added. The item's module and the new reflector module have zero holes. No
sorry occurs in any definition or private helper. The comparison's docstring gives
the complete dual-factor, tensor-symmetry, transition, and normalized derived-limit
argument. It includes the zero complex, zero section, and invertible section cases.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.Paper.DerivedCompleteKoszulReconstruction`;
- `Sheaf.CategoryTheory.RingedKoszulCompletionReflector` (now used by the proved
  principal reflector module);
- `Sheaf.CategoryTheory.StrictRoosComparison` (its normalization is confined to the
  separate model-comparison result);
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`.

The item's route no longer needs
`lem-pur-derived-complete-koszul-reconstruction` or
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`. Its quotient comparison is proved
by exact products and the mapping-cone triangle. Its Roos triangle is constructed
directly from the termwise derived product and the mapping-cocone triangle.
These two obsolete tool-use entries are removed from the item node. The ringed
reflector remains needed, through the new principal reflector. The normalized
strict Roos comparison remains needed in the model-comparison node. No existing
module or declaration is withdrawn, and no adopted source-library file is changed.

## Where the brief, the DAG or earlier work was wrong

The regular Koszul reconstruction theorem compares the principal negative-cone
Koszul tower with the quotient tower. The ringed reflector uses the dual of the
positive finite-Koszul tensor diagram. Their augmentation-compatible identification
was implicit in the old plan; it is not a conclusion of the reconstruction theorem.
The new presentation-comparison statement records precisely this remaining step,
without repackaging the completeness criterion.

The existing ringed reflector also needs a tower derived category in universe w,
which is absent from the item's hypotheses. This does not require a statement
change: local smallness follows from the given module derived category, and
K-injective resolutions construct the required localization universe. This is
proved in the new reflector module. No statement was found false. The unit
`sk-def-sf-operations` has no realized proof steps bypassed by this route.

## New nodes

`lem-pur-principal-koszul-roos-presentation-comparison` states the normalized
identification between the two actual strict singleton Koszul presentations, with
their units. Its source is the finite-dual Koszul computation in Stacks Tag 0A0E,
with Tag 0941 for normalized inverse limit. It is strictly a part of the original
argument and applies beyond the regular and K-flat case.

`lem-pur-principal-koszul-roos-reflector` is proved from that comparison and the
existing ringed reflector, including the generating-section and universe glue.
The main node's proof and dependencies follow the Lean proof. Both nodes explicitly
record the existing Grothendieck K-injective resolution instance used for their
derived-category and derived-product constructions. The searches in the
new node records include LeanSearch, LeanFinder, Loogle, Mathlib grep, local-library
search, and a blueprint-wide Koszul search. The definition factorization is recorded in
`coord/changes/B4-regular-quotient-unit-factorization.md`. There are no statement
changes and no forced adaptations.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
