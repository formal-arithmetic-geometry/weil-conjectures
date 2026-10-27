## What changed

Proved `WeilConjectures.integralExceptionalSiteDerivedRight_existsUnique`.
Proved private helpers assemble the cochain unit and construct the two universal right-derived
units of the comparison square. Both compute on K-injective complexes; uniqueness
of right derived functors gives the comparison and its uniqueness. Cancelling the
exact realization factorizations gives the required equation on every complex.

The concrete proof transports Grothendieck abelianness along the existing pro-etale
realization equivalence to obtain K-injective resolutions. The original inverse
comparison proof, all public signatures and definitions, and public imports stay
unchanged. Updated the item's node to record the completed direct-image argument.

Validation: the remote compiler accepted the proof in 49.5 seconds with profiling
enabled. Removed the development options and the sole tactic-style warning before
the delivery tool's final compile and axiom checks.

## Proved and sorry left

Closed the sole remaining original hole:
`WeilConjectures.integralExceptionalSiteDerivedRight_existsUnique`
(node `def-pur-adic-derived-site-realization`).

Holes closed: 1. Holes added: 0. Split-off statements: 0.
No `sorry` remains in the item. The inverse comparison was already proved.

## No longer needed

None. No original import, node, module or declaration was removed. The private
ShortExactPullback import supplies the cochain right-derived-unit API; the added
private imports supply K-injective derivability and Grothendieck resolutions.
The unit statement and realized proof steps stay unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing node recorded only the already-proved inverse argument. Added the
remaining direct-image argument and the existing, Lean-closed nodes
`lem-sfb-grothendieck-k-injective` and
`lem-weil-pbc-right-adjoint-preserves-kinjective` as proof dependencies. These supply
the categorical tools used to realize the original docstring's K-injective plan.
No statement or definition correction was needed.

## Second reading by Z8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
