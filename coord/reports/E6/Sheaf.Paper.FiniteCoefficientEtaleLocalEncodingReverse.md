## What changed

Proved `AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding_reverse`
with its original signature. The proof applies the existing coefficient-sized
finitely presented local-system etale-cover theorem on `V.left`, transports its
charts through the existing site equivalences, and generates a covering sieve
whose pullback works for every `W -> V`.

Three proved private helpers handle concrete etale charts, shrinking a finite
module to universe `t`, and reflecting a supplied constant model through the
ringed slice coordinates. Proof-only `import all` imports reuse the existing,
fully proved private comparison helpers of the local-model comparison, pullback,
finite-reflection and slice-model transport modules. Those modules are unchanged.
The ordinary scalar-extension adjunction identifies the actual completed-adic
constant model; no derived-category comparison is needed. The item's DAG proof
now records these steps and dependencies.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteCoefficient_etaleLocal_encoding_reverse`
(node `lem-weil-pbc-finite-coefficient-etale-local-encoding-reverse`).
Added zero holes. The item and all three new private helpers contain zero
`sorry`. No split-off statement or new module was added. This proves the item
from its imported declarations; it does not assert that all transitive library
obligations are closed.

Validation: the delivered item compiled cleanly in 14.0 seconds, and the
unchanged direct importer `Sheaf.Paper.FiniteCoefficientEtaleLocalEncoding`
compiled against it in 4.1 seconds. A temporary `#print axioms` check on the
reverse theorem reported exactly `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. The temporary importer copy was removed. The original theorem
signature was compared verbatim; all Lean lines are at most 100 characters;
the updated DAG dependencies introduce no cycle.

## No longer needed

Removed `def-sfb-site-derived-constant-module-functor` from the direct DAG proof
dependencies: the argument only uses ordinary module sheaves and the ordinary
scalar-extension unit. No module withdrawal or reduction of the transitive import
closure is claimed. Both original public imports are retained because the
statement uses their definitions. Every added proof import supplies declarations
used by the proof.

## Where the brief, the DAG or earlier work was wrong

The proof plan was mathematically sufficient, but its single transport sentence
hid the universe shrink and the two site-equivalence transports. These are now
explicit Lean proofs. Restricting the one etale covering of `V.left` to arbitrary
members of its pulled-back sieve avoids repeating the etale-descent theorem for
every `W -> V`. No statement, target, definition or unit route was changed.
The empty scheme and the zero ring require no special hypotheses: empty covers
and arbitrary constant modules are accepted by the existing comparison helpers.

The local-model comparison/pullback and finite-reflection modules are used only
for their completed site, constant-sheaf, and cover-reflection helpers. These are
tools for the given unit route, and no unit statement or proof step is bypassed.

The proof-local instance and irreducibility commands are documented in
`coord/changes/E6-finite-coefficient-etale-local-reverse.md`; they do not change
exported attributes or instances.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteCoefficientEtaleLocalEncodingReverse": "321f0a6c247410a6470d662112daeadfffe7e333"}, "results": {"Sheaf.Paper.FiniteCoefficientEtaleLocalEncoding": {"hash": "544045eaaf312a7ac78bcc3221765a4aad17d5f3", "status": "OK"}}, "seconds": 149, "time": "2026-10-27T23:41:57+0800", "transitive": 0, "version": 1}
```

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
