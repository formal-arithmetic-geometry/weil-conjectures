## What changed

Repair of returned delivery `1342efd9745`: explicitly restore the retained proved
module and its node after the batch take-out. The current checkout has no quarantine
copy and no rework row for this item, and V8 already holds its claim. The restoration
record is `coord/changes/V8-scalar-cokernel-return-restoration.md`. Reconcile the
current parent node `lem-coef-normalized-dvr-flat-cokernel` by adding its dependency
on this coefficient comparison, so the restored node remains needed by the target
route. The parent Lean file is untouched.

Proved `WeilConjectures.normalizedDVR_scalar_cokernel_comparison` in
`Sheaf.Paper.NormalizedDVRScalarCokernelComparison`, preserving its statement and public
imports. Added private proved helpers for descending a module action through a surjective
ring map, lifting complexes through fully faithful restriction, and identifying an
adjunction unit with a scalar cokernel. Reused the existing normalized scalar model,
completed projection divisibility, constant quotient surjectivity, and finite scalar
vanishing. The proof-only imports expose these results only within this module.

The cokernel itself is constructed in the completed module category. Its annihilation
by the projection kernel constructs its finite coefficient action, rather than choosing
an arbitrary object from an unproved existence statement. The normalized scalar model
supplies adjunctions, which are determined up to the canonical adjunction isomorphisms
used in the proof. Updated the node's proof and dependencies to describe this route.

## Proved and sorry left

Closed the one existing hole:
`WeilConjectures.normalizedDVR_scalar_cokernel_comparison`
(node `lem-coef-normalized-dvr-scalar-cokernel-comparison`).
There are zero holes left in the item and zero holes added. No statements were split off.
All new private helpers and all data constructions are proved or explicitly constructed.

Before the return, the final file compiled cleanly through `lcompile.py` in 29.6 seconds, without
warnings or profiling options. A direct text comparison verified that the original
public theorem signature and docstring are identical. All Lean lines are within
100 characters, and the node's proof dependencies are exactly the union of its steps.

The repair compiled cleanly against the current published build through `lcompile.py`
in 32.3 seconds, with no warnings and no holes. The restored node statement is checked
against the Lean signature, and both delivered nodes' proof dependencies match the
union of their proof steps.

## No longer needed

No existing node or module is withdrawn. All four originally planned proof dependencies
remain used. No existing public import is removed. The proof directly identifies the
completed cokernel by descent of its action, so it requires no separate tensor-balance
presentation theorem and adds no corresponding proof obligation.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The planned ordinary cokernel
presentation can be implemented directly in completed complexes by the universal
property and quotient-action descent. The unit route and all target statements are
preserved.

The return's quarantine description does not match the current checkout: neither the
archive path nor its row is present. The retained delivered copy supplies the exact
statement and Lean attachment for restoration. No absent path is listed in `deleted.txt`,
no metadata in `coord/rework.tsv` or claims is altered, and no launcher tool is changed.

## New nodes

`lem-coef-normalized-dvr-scalar-cokernel-comparison` is restored at its original path
with its original statement, source, Lean attachment and identity. Since it is absent
on current main, its new-packet author metadata is V8 and the stale batch review fields
are removed; this restoration receives a fresh independent review. Original provenance:
W6 split from `Sheaf.Paper.NormalizedDVRFlatCokernel` on 2026-10-25. The proof now
closes that original hole without replacement obligations. It is absent on
current main after the batch take-out, so the restored packet includes the full node.
The parent proof plan again cites this strictly smaller, now proved coefficient
calculation. There are no new mathematical obligations. Change record:
`coord/changes/V8-scalar-cokernel-return-restoration.md`.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
