## What changed

Replaced the body of
`WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`
in `Sheaf.Paper.CondensedCompactSupportProjection` by a complete Lean reduction.
The private proved helper `unique_normalized_lift` constructs the unique transpose
as the prescribed open unit followed by the inverse restriction normalization.
It uses the inverse adjunction Hom equivalence for existence and cancellation
followed by injectivity of that equivalence for uniqueness.

The new proof-only import `Sheaf.Paper.CondensedOpenRestrictedCounit` isolates the
geometric input: the original proper counit becomes invertible after restriction
to the distinguished open on an extension-by-zero object. The full restriction
normalization is its composite with the original inverse-image compositor, hence
is invertible. Its existing definition and every selected comparison arrow remain
unchanged, including the choice justified by the unique-existence theorem.

Compiled the new module (14.7 seconds) and the item (53.5 seconds) with lcompile.py.
The delivered changes do not alter any existing signature, definition, instance,
attribute or public import. No consumer adaptation or change record is needed.

## Proved and sorry left

Original holes: 3. Closed: 1. Added: 1. This is a decomposition, with net hole
change zero, not an axiom-free proof of the geometric assertion.

Closed by a complete proof from the split-off lemma:
`WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_existsUnique`
(node `def-pur-condensed-compact-support-projection`). The new private helper
`unique_normalized_lift` is proved with no holes.

Original holes retained unchanged, both at node
`def-pur-condensed-compact-support-projection`:

- `WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`.
- `WeilConjectures.CompactSupportCondensedRealization.fieldRefinement_comp`.

New hole:
`WeilConjectures.CompactSupportCondensedRealization.condensedOpen_restrictedCounit_isIso`
(node `lem-pur-condensed-open-restricted-counit`). It is a named public theorem
with exactly a sorry body in its own module. Its docstring and node contain the
clopen-section proof, source, and empty-open and identity-refinement checks.

## No longer needed

None. No import or original declared dependency is removed. The existing
shift, coefficient-composition, coefficient-identity, refinement-identity and
naturality proofs continue using their original dependencies. The unit route is
unchanged.

Searches found no shorter existing proof in Mathlib or the library. The closest
condensed compactification-independence declarations require Cartesian squares
and the bounded constructible geometric/coefficient setting; they do not supply
the arbitrary-refinement restricted counit here. The existing
`DerivedOpenRestriction` declaration is for bounded-below finite-ring etale
modules; `ProEtaleOpenRestrictionCounit` supplies an ordinary section-module
comparison, with additional internal-module transport and derived support
calculation still needed. Those supply the new node's proof plan rather than a
one-line proof of its statement.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy was found. The existing node explained the geometric
argument in the theorem docstring but did not expose its restricted-counit step
as a separate Lean declaration. This delivery exposes that step and proves the
remaining adjunction assembly. It assumes neither Cartesian refinement squares
nor torsion coefficients. In particular the general torsion proper-base-change
invertibility assertion of Stacks Tag 0F7B is not applied to arbitrary condensed
coefficients: only the calculation after restriction to the clopen section is
used in the new lemma's proof plan.

## New nodes

`lem-pur-condensed-open-restricted-counit`, in
`dag/nodes/sec-smooth-purity/lem-pur-condensed-open-restricted-counit.json`, states
invertibility of the open restriction of the specified proper counit on the
exact extension-by-zero object, for arbitrary unbounded inputs. This is the
geometric substep before the original open Hom bijection, and contains no
existence, uniqueness, choice of lift, or unit-normalization assertion. The item
proves all of that assembly in Lean. The new node names the clopen-section,
ordinary open restriction/counit, exact localized module adjunction, and
internal-module transport declarations for its proof plan. Three Mathlib
searches are recorded and logged. The parent node's proof, proof dependencies
and proof origin now record the actual reduction.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
