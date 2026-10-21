## What changed

Proved `WeilConjectures.IntegralOnSlice.completion_exists` by localization of flat-term
K-flat complexes. Products are exact on the global and slice module categories; termwise
reduction preserves quasi-isomorphisms, so Roos gives a functor that descends uniquely.

Proved the global completed-tensor comparison by the K-flat ordinary total tensor model,
the completion comparison, and a strict comparison of the finite reduction towers.
Added the tensor tower comparison and its quotient-transition compatibility as separate
source lemmas. Their proofs use the existing scalar-extension tensor comparison and
prove compatibility on local pure tensors and the injections of the total coproduct.
Explicit functor associators keep comparison of composite functors from unfolding
the completed coefficient ring and total tensor data. All new helpers in the original module
are private. Existing public signatures,
definition bodies, and public imports are unchanged.

Validation: all three modules compiled through `lcompile.py`; the complete tower
comparison and original module compiled together in dependency order. The single
formatting warning in the latter has been removed. Initial delivery preflight requested
LeanSearch records and a change record for local proof attributes; both are supplied.

## Proved and sorry left

Original holes closed:

- `WeilConjectures.IntegralOnSlice.completion_exists`.
- `WeilConjectures.IntegralOnSlice.completedTensor_global_comparison`.

New proved declarations:

- `WeilConjectures.integralTensorReductionTowerComparison`.
- `WeilConjectures.integralTensorTransitionCompatibility`.

No holes retained or added in the packet. The two new lemmas are proved, not deferred.
The proofs use existing stated dependencies which may themselves still contain holes.

## No longer needed

No original imports were removed, and no existing node or module is withdrawn.
The original node's dependencies remain necessary for its definitions and other theorems.
The new proofs use the existing scalar-extension and K-flat tensor APIs rather than
introducing additional derived-tensor constructions.

## Where the brief, the DAG or earlier work was wrong

The original node did not spell out the localization argument for completion or the
strict quotient-transition compatibility needed by its final tensor comparison.
Its proof record now includes both arguments. No original statement or definition
needed correction, and the unit route is preserved.

## New nodes

`lem-pur-integral-tensor-reduction-tower-comparison` records the natural strict tower
isomorphism obtained by scalar extension of ordinary total tensor products. It is
strictly below the completed-tensor comparison: it involves neither localization
nor Roos completion.

`lem-pur-integral-tensor-transition-compatibility` records compatibility of a
pure-generator-normalized tensor comparison with actual consecutive quotient maps.
It applies to arbitrary pairs of complexes, without flatness or boundedness, and is
proved using sheaf separatedness, tensor generation, and total coproduct injections.
Change record: `coord/changes/B5-integral-derived-proof-attributes.md`. Preflight
requested it for local proof attributes; all existing public statements and definitions
are preserved. No consumer adaptation is needed.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
