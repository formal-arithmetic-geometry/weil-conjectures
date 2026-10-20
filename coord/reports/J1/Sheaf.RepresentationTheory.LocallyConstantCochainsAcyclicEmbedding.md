## What changed

Retired `Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`, as listed in
`coord/retire-items.tsv` and the human-approved retirement record of 2026-10-20. Its main
statement already has a complete proof in
`WeilConjectures.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`. The theorem
signatures match verbatim. Redirected the existing acyclic-embedding node's Lean attachment
to that canonical upstream declaration and listed the old file in `deleted.txt`.

The only current direct importer is the unclaimed
`Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`. It uses the old copy's public
`Rep.contract_insert_zero` and `Rep.contract_insert_succ`; upstream keeps both private.
Removed that proof-only import and proved the two required instances locally in
`Rep.coinduced_homotopy_identity`, using function extensionality, `Fin.cases`, and
`simp [Fin.contractNth]`. Its construction and cancellation argument otherwise stay the
same. Updated its node's proof, proof dependencies, and proof origin accordingly.
No public consumer signature, public import, definition, upstream file, or target changes.

Change record: `coord/changes/retire-locally-constant-cochains-acyclic-embedding.md`.
It lists all nine transitive users and their checked claim status.

The adapted consumer compiled cleanly through `lcompile.py` in 2.3 seconds. A probe of
`Rep.locallyConstantCochains_acyclic_embedding` in the canonical upstream module compiled
and printed exactly `propext`, `Classical.choice`, and `Quot.sound`. A source import-closure
check finds no remaining retired import and no pair of Sheaf/upstream twins in either the
adapted consumer's environment or the canonical theorem's environment. The consumer's
project-module closure decreases from five to three modules. Delivery runs the required
all-declaration axiom probes and preflight. The immediate downstream consumer
`Sheaf.RepresentationTheory.CoinducedContinuousAcyclic` also compiled against the
adapted module in 2.2 seconds; its unchanged source is not included in the delivery.
An axiom probe of the adapted `Rep.coinduced_homotopy_identity` reports exactly the
same three allowed axioms.

## Proved and sorry left

This is a retirement with zero original holes: closed 0, added 0, split off 0, left 0.
There is no remaining `sorry` in the adapted module. The two local tuple equalities are
proved, including the zero-index and successor-index cases. The consumer theorem
`Rep.coinduced_homotopy_identity` retains its complete proof and exact public signature.
The canonical `Rep.locallyConstantCochains_acyclic_embedding` was already proved upstream;
this delivery does not count that existing proof as a newly closed hole.

## No longer needed

Withdrawn module:
`Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`.
Removed its proof-only import from
`Sheaf.RepresentationTheory.CoinducedHomotopyIdentity`.
The public helper declarations `Rep.contract_insert_zero` and `Rep.contract_insert_succ`
from the withdrawn copy have no remaining callers; the only required instances are local
proof facts. No new module or public replacement helper is necessary.

Removed `lem-sc-locally-constant-cochains-acyclic-embedding` from the homotopy-identity
node's `proof_deps` and final proof step. That integer-coefficient acyclic embedding is
unnecessary for the finite-ring homotopy calculation. The existing acyclic-embedding
node itself remains attached to the canonical upstream theorem, which is still used
by the upstream effaceability theorem. Its stabilizer dependency remains needed by
that proof and is not claimed as globally pruned.

The old copy's public and private imports disappear with its declarations; their upstream
counterparts stay unchanged in the canonical proof. No other nodes or modules are pruned.
No unit realization is bypassed: `sk-thm-br` has empty realized attachments for this node.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with an outstanding proof obligation. The
current queue instead marks this item `retire`; its copy and canonical upstream theorem
are already sorry-free. This packet completes that listed retirement with its actual
zero-hole count.

The retirement table still lists `Sheaf.RepresentationTheory.LocallyConstantCochainsEffaceable`
as a second consumer, but that copy is already absent from this checkout. Its upstream
twin imports the upstream acyclic-embedding module. A full current import search finds
only `CoinducedHomotopyIdentity` importing the retired module.

The table calls the APIs the same, but the two tuple lemmas are public only in the Sheaf
copy. Compiling the original consumer after changing only its import to the upstream twin
fails at original line 184 with `Unknown identifier contract_insert_zero` and
`Unknown identifier contract_insert_succ`. The delivered local calculations repair that
failure without changing upstream visibility or adding another public copy of the helpers.

LeanFinder and Loogle searches for `Fin.contractNth` found its definition and pointwise
comparison lemmas, but no matching insertion/contracting identities. The logged Mathlib
grep returned no matching insertion lemmas. The local proof checks these elementary
instances directly. The previous consumer node's claim that it reused public helpers
from the acyclic-embedding node is updated to match the actual proof.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
