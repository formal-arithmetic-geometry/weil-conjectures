## What changed

Completed all three theorem proofs in `Sheaf.Paper.AdicPurityObjects`, without changing
any declaration signature or definition. The global-section unit proof derives the
characteristic of the finite base field from its cardinality, uses distinctness of the
coefficient prime, and maps the resulting unit along the composite structure map.
The residue-field proof maps this unit by global evaluation. The finite-Tor proof
extracts the chosen constructible reduction and the uniform Tor interval from the
integral hypothesis. This works at n = 0 (exponent 1) and for the empty scheme.

Removed two unused direct imports. The import-pruning consumer check passes.
Change record: `coord/changes/W9-adic-purity-object-imports.md`.
Single-file compilation and axiom checks were run through the authorized remote compiler.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to `def-pur-adic-purity-objects`:

- `WeilConjectures.purAdicCoefficientUnit`.
- `WeilConjectures.purAdicResidueUnit`.
- `WeilConjectures.purAdicReductionFiniteTor`.

Holes added: 0. Holes left in the item: 0. No decomposition or new intermediate theorem.
The first two theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
`purAdicReductionFiniteTor` still has a transitive `sorryAx` dependency through the
existing reduction/Tor predicates; its own proof is a complete projection of the
integral hypothesis, with no new admitted fact.

## No longer needed

Removed direct imports `Sheaf.Paper.IntegralOperationsPreserveConstructible` and
`Sheaf.Paper.NormalizedDVREffectivity`. The former remains available through the
retained public imports; neither direct import is needed to compile this module.
The consumer import-pruning check accepts both removals. No claim is made that these
modules become unreachable from the other project targets. There were no stated
proof dependencies to prune: the item's definition node has an empty `proof_deps` list.
The definition dependencies and the blueprint unit route remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface repair was required. The three existing theorem docstrings
already describe direct proofs, and those proofs suffice without new nodes or imports.
The node `def-weil-finite-tor-amplitude` currently records the ordinary-etale presentation,
whereas this module correctly uses the existing pro-etale and integral predicates in
`Sheaf.Paper.FiniteTorAmplitude`; their definitions provide the required projections.

## Second reading by W9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
