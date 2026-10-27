## What changed

Proved `WeilConjectures.frobeniusCohomologyRationalOperationScalar_existsUnique`
using private tensor-localization lemmas. The component is the localization of the
specified integral scalar comparison, conjugated by the rational functors' object
equalities. Naturality is proved on pure tensors and extended by tensor induction;
uniqueness follows from the component specification. Both ordinary and compact
support models are covered. Every existing signature, definition, and import is
preserved. The node records this additional completed coefficient step.
Local irreducibility attributes prevent repeated residue-field and witness
unfolding during instance search; see
`coord/changes/F6-frobenius-rational-scalar-proof-context.md`.

The starting file was read from the current server version, preserving Z6's
already landed coefficient-tower and stage-embedding proofs.

## Proved and sorry left

Closed 1 of the 4 holes in the current item:
`WeilConjectures.frobeniusCohomologyRationalOperationScalar_existsUnique`.
Added 0 holes; no split-off statements.

The following 3 existing theorem holes remain unchanged, all owned by
`lem-weil-frobenius-cohomology-transport-iso`:

- `WeilConjectures.frobeniusCohomologyQbarFunctor_existsUnique`.
- `WeilConjectures.frobeniusCohomologyTransport_isIso`.
- `WeilConjectures.frobeniusCohomologyTransport_natural`.

## No longer needed

None. No existing import, declaration, node, module, or unit step is removed.
The remaining parent proof obligations retain their stated dependency route.

## Where the brief, the DAG or earlier work was wrong

The local shared Lean source still contained the two holes already closed by Z6
in the current server version. This delivery starts from that current version,
with four holes, and preserves both prior proofs. No mathematical statement or
construction was repaired or weakened.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
