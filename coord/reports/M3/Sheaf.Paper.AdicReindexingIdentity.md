## What changed

The item now constructs a finite-stage identity certificate from the sectionwise module
identity and integral normalization hypotheses, then applies a separate assembly theorem
which extends that certificate through the directed coefficient system and the source-unit
equation.  The two intermediate statements are in
`AdicReindexingIdentityFiniteData`, `AdicReindexingIdentityFiniteCertificate`, and
`AdicReindexingIdentityAssembly`; the change record is
`coord/changes/normalized-reindexing-identity-decomposition.md`. the item imports the latter two proof modules.

## Proved and sorry left

The parent declaration `normalized_reindexing_identity` is reduced to the two named
intermediate theorems and compiles.  The finite-stage cancellation remains as
`normalized_reindexing_identity_finite` (node
`new-lem-sf-adic-reindexing-identity-finite-certificate`), and the directed-stage assembly
remains as `normalized_reindexing_identity_from_finite` (node
`new-lem-sf-adic-reindexing-identity-assembly`).  The finite certificate structure has no
proof hole.

## No longer needed

No proof-dependency imports or DAG dependencies were pruned.  The original integral and
inverse-image comparison dependencies are retained by the finite-stage node.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan hides two independent arguments: the coefficient-level
finite-stage cancellation and the extension from finite representatives to arbitrary
common-stage objects.  They are recorded as separate new nodes so each remaining hole is
a strictly smaller part of the stated proof.

## New nodes

`new-lem-sf-adic-reindexing-identity-finite-data` records the finite-stage certificate
data structure. `new-lem-sf-adic-reindexing-identity-finite-certificate` records the
finite cancellation. `new-lem-sf-adic-reindexing-identity-assembly` records the directed
stage extension.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingIdentity": "03bd91e8c6a427f7cabb2925ed8b4bcb429498f5", "Sheaf.Paper.AdicReindexingIdentityAssembly": "fb551967c0b8b5c5a17d870ee6841513b8f405b1", "Sheaf.Paper.AdicReindexingIdentityFiniteCertificate": "c44ef6432c193afcb6ad91bacbc3df60136e4666", "Sheaf.Paper.AdicReindexingIdentityFiniteData": "2999694165702867ab40882cf080c3352e9faf9f"}, "results": {"Sheaf.Paper.AdicReindexingFunctoriality": {"hash": "bf857425a90d47854bbe0ca74d81cdad54f17e62", "status": "OK"}}, "seconds": 12, "time": "2026-10-28T07:35:24+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
