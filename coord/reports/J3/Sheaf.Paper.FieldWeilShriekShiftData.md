## What changed

In `Sheaf.Paper.FieldWeilShriekShiftData`, proved the normalized rational pullback
composition comparison and invertibility of both specified finite-stage Frobenius
exchange maps. Existing public declarations, signatures, definitions, instances,
and public imports are unchanged.

The rational compositor proof localizes the existing integral compositor. A private
helper copies the prescribed object actions, checks naturality on pure tensors,
extends it by additivity, and transports the resulting natural isomorphism back.
Its components satisfy the required HEq normalization. Since every rational object
is a wrapped integral object, those components also prove uniqueness.

The exchange proof obtains each Frobenius equivalence from
`semilinearFieldOperationLifts`, specialized to the identity map and an algebraic
closure of the coefficient base. It applies the existing right-mate invertibility
theorem for proper image and its opposite-category argument for the inverse open
mate. This proves invertibility of the maps already defined in the module, with
no replacement of their units, counits, or squares. The identity specialization
requires no separatedness of the structure morphism.

Added private proof imports of `Sheaf.Paper.SemilinearFieldOperationLifts` and
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`. All new helpers are proved.
Updated the existing definition node's proof, proof dependencies, and proof origin
to record these two partial proof routes. No unit statement or route is changed.

## Proved and sorry left

Closed 2 of the 7 original holes:

- `WeilConjectures.fieldRationalPullComp_existsUnique`.
- `WeilConjectures.fieldWeilExchange_isIso`.

Added 0 holes and split off 0 statements. The following 5 original holes remain,
all attached to `def-zl-field-weil-shriek-shift-data` and retaining their source and
natural-language proof docstrings:

- `WeilConjectures.fieldIntegralPullShift_existsUnique`.
- `WeilConjectures.fieldRationalPullShift_existsUnique`.
- `WeilConjectures.fieldCommonPullShift_existsUnique`.
- `WeilConjectures.fieldWeilPull_adjoints`.
- `WeilConjectures.fieldWeilShriek_recorded`.

The two closed proofs use existing library declarations whose own proofs may still
contain holes; this is a proof from recorded dependencies, not a claim of a
transitively sorry-free module. No new module or public theorem is introduced.

## No longer needed

None. No imports or modules are removed. The original node had no proof steps or
proof dependencies, so no previously planned proof dependency is pruned. All
original statement dependencies and public imports remain needed by the existing
interface or by its retained claims. The shorter categorical exchange argument
uses the existing Frobenius equivalences directly and needs no newly stated
inverse-square or mate-pasting lemma.

## Where the brief, the DAG or earlier work was wrong

The definition node had an empty proof plan despite containing seven theorem
holes. Its theorem docstrings provide the individual plans. The two proofs here
use those existing interfaces: integral composition for the rational compositor,
and semilinear transport for the autoequivalences. No false statement or definition
repair was found. In particular, the automorphism equivalence theorem requiring a
separated structure map would not apply to this module's general hypotheses; the
identity specialization of semilinear transport avoids that extra hypothesis.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
