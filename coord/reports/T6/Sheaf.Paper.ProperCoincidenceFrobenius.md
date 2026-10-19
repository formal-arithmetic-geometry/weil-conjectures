## What changed

Proved `WeilConjectures.properFrobeniusCompactification_eq` by destructing the
object over the finite base, reducing its identity compactification, and using
functoriality of geometric base change on the identity arrow. This avoids dependent
rewriting through the finiteness proof fields.

Proved `WeilConjectures.properFrobeniusRationalIso_existsUnique` by localizing the
constructed integral comparison componentwise. The existing
`FrobeniusExchange.localizedTransformation_naturality` proves naturality on all
localized Hom maps. The specified components give uniqueness by isomorphism and
natural-transformation extensionality. Existing signatures and imports are unchanged.

## Proved and sorry left

Closed 2 of the 8 original holes, with no holes added:

- `WeilConjectures.properFrobeniusCompactification_eq`
- `WeilConjectures.properFrobeniusRationalIso_existsUnique`

Six holes remain, all attached to `lem-pod-proper-coincidence-frobenius`:

- `WeilConjectures.properCoincidenceFrobeniusFinite`
- `WeilConjectures.properCoincidenceFrobeniusIntegral`
- `WeilConjectures.properCoincidenceFrobeniusRational`
- `WeilConjectures.properFrobeniusQbarSourceIso_existsUnique`
- `WeilConjectures.properFrobeniusQbarTargetIso_existsUnique`
- `WeilConjectures.properCoincidenceFrobenius`

The two completed proofs compiled together in 17.8 seconds before formatting
cleanup. The latest compile verification failed at the transport level: `lcompile.py`
reported no answer from the compile server within 187 seconds (exit 124, NOT compiled).
Earlier retries also reported no answer within 182 and 200 seconds. This is distinct
from the earlier Lean timeout in the exploratory finite calculation. Work is not delivered.
The exploratory helper is preserved separately in `finite-helper.txt`; it is absent
from the delivery module, which contains exactly the six original remaining holes.

## No longer needed

None. No imports, nodes, modules, or declared proof dependencies were removed.

## Where the brief, the DAG or earlier work was wrong

The retained report incorrectly counted seven original holes and claimed the
compactification equality was proved, although its dependent rewrite did not compile.
There were eight original holes. The two proofs above replace the failed attempt.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
