## What changed

Completed the proof of `AlgebraicGeometry.derivedExchangeUnboundedTransport`.
The proof constructs a bounded-below injective representative, lifts the comparison
isomorphism through the K-injective Hom bijection, applies the bounded comparison
hypothesis, and transports the equation by naturality and cancellation. No imports
were added or removed.

## Proved and sorry left

`AlgebraicGeometry.derivedExchangeUnboundedTransport` is fully proved. No `sorry`
remains in the delivered module.

## No longer needed

None. The module retains its existing import, which supplies the derived-category,
K-injective, and bounded-comparison declarations used by the proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt had three elaboration issues: the boundedness witness needed an
explicit `plus_quotient_obj_iff` application, a redundant simplification step failed,
and the termwise base-change naturality required an explicit composition change.
These are repaired in the proof; the statement and route are unchanged.

## Second reading by G1

1. Compared the delivered module with the repository version. The declaration
   signature and all existing statements are unchanged; only the proof body and its
   transparency option differ.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings.
   The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The proof uses only the permitted library axioms.
3. The item has no split-off statements or new nodes. Its theorem is the existing
   transport statement, and the bounded representative construction proves it
   directly without restating the item.
4. The proof follows the node route: choose the bounded K-injective representative,
   transport the comparison data by naturality, apply bounded comparison, and cancel
   the induced isomorphism. The existing import remains needed and no old dependency
   is unused.
5. The DAG node's statement, proof steps, dependencies, and origin agree with the
   delivered Lean proof; the unit route through bounded comparison is preserved.

Changed only the proof body (and retained the proof-local transparency setting from
the working version); no imports, declarations, or DAG records required repair.
