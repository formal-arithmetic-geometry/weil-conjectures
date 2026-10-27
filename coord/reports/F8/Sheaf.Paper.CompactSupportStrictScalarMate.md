## What changed

Proved `WeilConjectures.PurStrictScalar.pulledBasis_existsUnique` in the item module.
The construction pulls back the supplied basis, uses the existing canonical
restriction/pullback comparison, and identifies inverse images of regular modules
using Mathlib's `SheafOfModules.pullbackObjUnitToUnit`. A proved private finite-product
transport lemma supplies both the coordinate equation and uniqueness. The inverse-mate
unit equation identifies the specified section formula. Statements, public imports,
and the definition of `pulledBasis` are preserved.

The node's Step 4 records the actual basis-transport argument. No shared dependency
module is changed. The complete item module compiled remotely in 37.8 seconds
(exit code 0), within the 60-second delivery limit.

## Proved and sorry left

Closed 1 of the original 3 holes:
`WeilConjectures.PurStrictScalar.pulledBasis_existsUnique`.

The following original holes remain, both attached to
`lem-pur-compact-support-strict-scalar-mate`:

- `WeilConjectures.PurStrictScalar.proper_biproduct`.
- `WeilConjectures.PurStrictScalar.strictProper_biproduct`.

Added holes: none. Split-off statements: none. Actual remaining direct hole count: 2.
The already written final assembly continues to use the two original coordinate
obligations. This is one direct proof, not a decomposition into new obligations.

## No longer needed

None. No original import, module, node, or unit-route step is pruned. The only new
proof import is Mathlib's module-sheaf free-pullback API. The basis proof uses the
already declared geometric adjunction and restriction/pullback comparison; it needs
no new coefficient construction or independent choice of basis.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. Mathlib already provides the
regular-module pullback isomorphism needed for the basis transport, so that part
requires no new sectionwise construction. The proof applies also to rank zero and
the empty source scheme: it only uses finite-product preservation and invertible
canonical comparisons, with no nonemptiness or positive-rank assumption.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
