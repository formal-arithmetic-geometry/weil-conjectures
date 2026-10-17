## What changed

Restored the public declaration `CategoryTheory.BigradedExactCouple.exactFunctor_couple`
with the exact statement recorded by the DAG node.  The declaration compiles in the
sandbox and retains its blueprint and source context.

## Proved and sorry left

The target declaration `exactFunctor_couple` remains as one named public theorem with a
whole-proof `sorry`.  No definitions contain `sorry`; no additional declarations were
added.

## No longer needed

Change record: `coord/changes/exact-functor-couple-restored.md`.

The withdrawn upstream helper route (mapped exact-couple construction, derived-page
comparisons, page inclusions, and filtration comparison) is not imported by the restored
statement.  The corresponding private helper declarations were removed from this module.

## Where the brief, the DAG or earlier work was wrong

The upstream synchronization had commented out the target theorem and left a private
`mapped` definition with a hollow proof.  The module therefore compiled without exposing
the DAG declaration.  This delivery removes that hollow definition and restores the exact
DAG statement; the transport proof remains open for a subsequent worker.

## New nodes

None.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
