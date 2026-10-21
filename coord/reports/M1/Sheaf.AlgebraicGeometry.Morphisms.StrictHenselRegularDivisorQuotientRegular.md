## What changed

Completed the listed zero-hole retirement of
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular`.
The existing upstream theorem proves the same mathematical statement for the
canonically isomorphic full colimit. Withdraw the duplicate using `deleted.txt`
and attach its node to the upstream theorem.

Adapt both direct consumers, StrictHenselRegularDivisorQuotientNoetherian and
StrictHenselRegularDivisorQuotient. Their public theorem signatures, visibility,
definitions and existing docstrings are unchanged. Replace the proof import by
the upstream owner. Use the upstream structural-map public import to avoid the
duplicate cone-equation name from its Sheaf wrapper. Move the existing proved
private comparison helper into both consumers. Compose the base ring map with
the canonical colimit comparison, transfer its nonunit hypothesis, and transfer
regularity (and the domain property where needed) back across the induced
principal-quotient equivalence. No upstream file or target statement changes.

The two adapted consumers compile cleanly in 3.7 and 4.2 seconds. Verification
also compiles all nine downstream modules individually with the item replaced by
an empty module. Search used LeanFinder, Loogle and grep: Loogle found
`IsRegularRing.of_ringEquiv`, LeanFinder found `MulEquiv.isDomain_iff`, and local
source inspection found the complete upstream theorem and canonical comparison.

Change record:
`coord/changes/M1-retire-strict-hensel-regular-divisor-quotient-regular.md`.

## Proved and sorry left

The item originally has zero `sorry`; this is a substantive duplicate retirement,
not a hole closure or decomposition. Holes closed: 0 of 0. Holes added: 0.
No `sorry` remains in any delivered Lean module; no statement is split off.

Preserved complete proofs of
`AlgebraicGeometry.Scheme.strictHenselizationRing_noetherian_of_regular` and
`AlgebraicGeometry.Scheme.strictHenselization_regular_divisor_quotient` against
the retained upstream
`AlgebraicGeometry.Scheme.strictHenselizationRing_regular_divisor_quotient`.
Both new private `comparison_base` occurrences are proved completely.

## No longer needed

Retire only
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular`.
Both direct consumers remove this proof import and import the upstream twin.
They also replace the Sheaf structural-map wrapper public import with its
upstream owner, which provides every notion in their unchanged signatures.

The retired copy's direct component imports RegularPart and DomainPart are now
supplied by the retained upstream conjunction. Both component nodes and their
mathematics remain needed by that theorem. The regularity node is preserved
with both component edges; Noetherian retains its regularity and local-structure
edges. Quotient's proof dependencies now name the Noetherian and regularity
nodes actually used in Lean. Its old direct theory dependencies remain indirect
inputs of those proofs; this packet does not withdraw them or their modules.
No mathematical node or unit step is pruned. No other module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item containing a hole, but this item has
zero holes and a specific retirement row. Its upstream twin already has a
complete proof. The two APIs use different colimit presentations, so replacing
the import alone is insufficient. The canonical colimit and quotient transports
resolve that difference without changing any consumer statement.

The combined Quotient node still described a direct local-ring argument, while
its Lean already applied the Noetherian and regularity/domain declarations.
Its proof metadata now records these actual dependencies and the explicit
transport. The blueprint unit has no realized entry for this helper; its
statement and proof route are preserved. No disputed statement, new node,
new definition, or forced edit of another group's claimed module is introduced.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
