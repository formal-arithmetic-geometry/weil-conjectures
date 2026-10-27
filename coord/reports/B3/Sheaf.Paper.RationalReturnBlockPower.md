## What changed

Proved `WeilConjectures.fdRationalReturn_multiple` and
`WeilConjectures.fdRationalReturn_blockPower` in
`Sheaf.Paper.RationalReturnBlockPower`. A proved private helper, `positivePower_add`,
identifies positive powers at index `a + b + 1` with the composite of the powers
at indices `a` and `b`, directly by induction on the defining recursion.

The multiple-return proof inducts on the block count and pastes the original
return square with the induction hypothesis. The block-power proof uses the same
addition identity and commutativity of addition of natural numbers. These proofs
handle `d = 0` (period one) and `r = 0` (one block), without positivity assumptions
beyond those already encoded by successor indices. They do not use any holed
comparison theorem. All existing signatures, definitions, docstrings and imports
are unchanged.

This is a partial delivery of a module with three original holes. The main
four-clause rational transport theorem is left untouched.

## Proved and sorry left

Closed two of the three original holes, both on node
`lem-fd-rational-return-block-power`:

- `WeilConjectures.fdRationalReturn_multiple`.
- `WeilConjectures.fdRationalReturn_blockPower`.

The private helper `positivePower_add` is also completely proved.

One existing hole remains:
`WeilConjectures.fdRationalReturnBlockPower`
(node `lem-fd-rational-return-block-power`). No holes are added or split off.

## No longer needed

None. No imports, nodes or modules are withdrawn. The two completed helper proofs
use the positive-power recursion directly rather than the holed
`LocalFrobeniusTransport.positivePower_eq`, but its module supplies definitions
used by the rest of this file and remains necessary.

## Where the brief, the DAG or earlier work was wrong

No statement error is asserted. Searches with LeanFinder, Loogle and grep found
ring-Frobenius identities and elementary power identities, rather than a theorem
about these rational derived point transports. The existing private power lemma
in `ClassicalLocalFrobeniusData` does not require importing that much larger
comparison development: direct induction suffices for the completed helpers.

For continuing the main theorem, the endpoint bookkeeping is substantive:
`IteratedReturnTransport.RationalNaturality` uses successive one-step functor
iterations and `powerComparison`, whereas this module uses pullback along the
scheme power and `LocalFrobeniusTransport.rationalPointIterate`. The closed-point
clause also compares the specified-system rational compositor with the compositor
in `LocalFrobeniusTrace`. This delivery does not assert or add any unproved bridge
between those presentations.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
