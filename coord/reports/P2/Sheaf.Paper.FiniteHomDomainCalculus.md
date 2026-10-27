## What changed

Completed `WeilConjectures.finiteHomDomain_pullback` in
`Sheaf.Paper.FiniteHomDomainCalculus`, preserving every public signature.
A proved private helper converts between the two existing bounded-constructibility
interfaces. The proof applies source-library pullback stability for bounded
constructibility and the exact Tor interval, then reads the representative equation
from `scalarPullbackIso_existsUnique`.
The lifted-ring instance priority is confined to the pullback compatibility section.
No definitions, public imports, or other library modules were changed.

## Proved and sorry left

Closed one of the four existing holes:

- `WeilConjectures.finiteHomDomain_pullback`.

Three existing holes remain, all attached to
`lem-coef-finite-hom-domain-calculus`:

- `WeilConjectures.finiteHomDomain_monoidal`.
- `WeilConjectures.finiteHomDomain_scalarCoherence`.
- `WeilConjectures.finiteHomDomain_transpose`.

Added holes: zero. Split-off statements: zero. The private helper is proved.
The previously completed flat-model, endpoint, and quotient-identity proofs are retained.

## No longer needed

Removed the private proof import `Sheaf.Paper.ScalarPullbackIsoExistence`:
the chosen comparison's public uniqueness/normalization theorem suffices.
Removed `lem-pur-exact-pullback-signed-comparison` from the node's proof dependencies
and top-level tool approvals; the requested representative equation follows directly
from `scalarPullbackIso_existsUnique`.
No modules are withdrawn and no public imports are removed.
Other planned dependencies remain relevant to the open declarations.

## Where the brief, the DAG or earlier work was wrong

The existing etale derived stability API proves the pullback clause without rebuilding
a pulled-back K-flat model. No statement was found false or weakened.
The empty scheme, identity coefficient quotient, and single-degree Tor interval
require no special cases; no flatness of the coefficient quotient is assumed.

A generic categorical proof of transpose uniqueness and base-change naturality
compiled independently, but its concrete coefficient specialization exceeded the
per-file compile limit. It is not included in this partial delivery; the original
transpose statement and proof plan remain intact.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
