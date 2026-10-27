## What changed

Filled all five proofs in `Sheaf.AlgebraicTopology.WeakPosetChainNormalization`.
All existing public signatures, definitions, docstrings and public imports are unchanged.
Added proved private helpers and private proof imports of `Mathlib.Data.List.InsertIdx`
and `Mathlib.Data.List.Nodup`.

The signed deletion sum satisfies a head/tail recurrence. Induction proves its square is
zero, including empty lists. An adjacent repeated pair cancels under every bracket that
kills repeated lists. An explicit linear section sends a strict tuple to its identical weak
tuple; its two projection identities prove surjectivity and identify the repeated span as
the kernel. These calculations prove the boundary laws and the induced quotient laws.
The bijective quotient lift gives the canonical complex isomorphism. Entrywise monotone
image commutes with deletion, preserves repetitions, and satisfies identity/composition.
The final quotient-generator formula follows directly from these bracket calculations.
The node proof records this implementation of the existing six-step argument.

## Proved and sorry left

Closed 5 of 5 original holes, all attached to
`lem-sfb-poset-weak-chain-normalization`:

- `AlgebraicTopology.WeakPosetChains.boundary_laws`
- `AlgebraicTopology.WeakPosetChains.map_laws`
- `AlgebraicTopology.WeakPosetChains.quotient_boundary_laws`
- `AlgebraicTopology.WeakPosetChains.quotient_map_comm`
- `AlgebraicTopology.WeakPosetChains.normalization`

No `sorry` remains in the delivered module. Added holes: 0. Split-off theorems: 0.
The existing imported strict-chain complex and its proof obligations are untouched.
The proofs quantify over every integer degree, arbitrary commutative rings (including the
zero ring), and empty finite posets; no nonemptiness or nontriviality assumption is used.

## No longer needed

None. No import, node or module is pruned. Both declared proof dependencies remain in use:
`def-weil-pbc-module-chain-complex-homology` and `def-sfb-augmented-poset-chains`.
There are no unused proof-dependency imports and no new mathematical dependencies.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The original double-deletion argument is
implemented by the equivalent list head/tail recurrence, which avoids a two-index sum
reindexing. The kernel is computed before boundary compatibility so that deriving
preservation of the repeated span from that kernel is noncircular. The unit route is kept.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
