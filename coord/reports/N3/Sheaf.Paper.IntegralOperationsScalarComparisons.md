## What changed

Replaced the hole in `WeilConjectures.scalarTensorOrdinary_existsUnique` by
`normalizedIntegralScalarTensorComparison`. The existing item changes only that
proof and adds one proof import. All existing statements, definitions, visibility,
public imports and completed proofs remain unchanged.

The proof specializes `scalarRoosTransformation` to the specified tensor tower
map, proving chain naturality. On good pairs the new chain quasi-isomorphism
statement makes its Q-image invertible. The uniquely normalized representative
natural isomorphism then descends through the product good localization using
`functorSquareRepresentativeDescent`. Its component square is exactly the original
normalization, and full faithfulness proves the required uniqueness.

The good-comparison construction is selected from a completely proved uniqueness
theorem fixing every hom component to Q.map of the specified chain map. Those
components determine the whole natural isomorphism. The only unproved property
used in that construction is invertibility of that fixed map, which determines
its inverse uniquely. No arbitrary witness or data sorry is introduced.

Profiling identified expensive reassociation of the existing tensor representative
comparison. A new concrete alias and its component equation compile this conversion
once, then reuse it at both coefficient fields. The chain naturality, representative
assembly, conditional descent, and final normalization are separate modules so
each checks within the per-file limit. No other existing Lean module changes.

Validation: remote `lcompile.py --all` succeeded for all eight sandbox modules,
including the original item (result `f16aae9979a3a551d463acf4`, exit code 0).
Profiler options were then removed and the isolated-dot style warning was fixed.
The required delivery tool recompiles and preflights these final files.

## Proved and sorry left

Original holes: two. One upper hole is closed by a **decomposition**:
`WeilConjectures.scalarTensorOrdinary_existsUnique` now has a complete Lean proof
from the strictly lower representative quasi-isomorphism statement. The proof
includes naturality, descent, normalization, and uniqueness.

One original hole remains untouched:
`WeilConjectures.scalarOperationsOrdinary_tower`, attached to
`lem-pur-integral-operations-scalar-extension`.

One hole is added:
`WeilConjectures.scalarTensorChainQuasiIso`, in
`Sheaf.Paper.IntegralScalarTensorChainQuasiIso`, attached to
`lem-pur-integral-scalar-tensor-chain-quasi-iso`.
It asserts only that the specified chain map is a quasi-isomorphism on good pairs,
without the derived comparison, naturality, normalization, or uniqueness clauses.
Its docstring and node give the balanced tensor, finite-free product, cofinal
filtration, and coordinate-identification argument. Identity extensions, zero
factors, empty sites, and unbounded good pairs were checked in that argument.

Holes closed: one. Holes added: one. Net reduction: zero. Actual holes left in the
packet: two. Every other new declaration is fully proved or a real construction.
No new axiom declaration or hollow definition is introduced.

## No longer needed

None. No original imports, declarations, modules, nodes, or unit steps are removed.
The remaining tower-coherence plan is retained. The new route uses the specified
finite tensor models and strict Roos map, the lower chain quasi-isomorphism, and
the existing generic localization descent theorem.

## Where the brief, the DAG or earlier work was wrong

The current item contains two holes. The three nodes ending
`scalar-extension-pullback-clause`, `scalar-extension-tensor-clause`, and
`scalar-extension-hom-clause` still attach the names
`scalarOperationsOrdinary_tower_pullback`, `_tensor`, and `_hom` to this module,
but those declarations and their clause predicates are absent from the current
source. The pending change record `integral-operations-scalar-comparisons.md`
describes that old decomposition. This delivery neither relies on it nor changes
those other nodes; the actual tower conjunction and its hole remain unchanged.

There was no existing tensor analogue of `scalarPullbackChainQuasiIso` for the
prescribed tensor map. The required searches found no direct theorem, so only
the missing chain quasi-isomorphism is split off. In its cofinal-filtration proof,
the specified quotient map goes from the ramified subsequence to the original
tower, opposite to arithmetic restriction. The node records the reverse-map
homotopy argument, including both Roos coordinates.

## New nodes

- `lem-pur-integral-scalar-tensor-chain-quasi-iso`: the sole new hole,
  `scalarTensorChainQuasiIso`, with source and full proof in words.
- `lem-pur-integral-scalar-tensor-chain-naturality`: the proved
  `scalarTensorChain_naturality`, specialized from the generic Roos transformation.
- `lem-pur-integral-scalar-tensor-good-comparison`: the proved unique representative
  comparison `integralScalarTensorGoodComparison`.
- `def-pur-integral-scalar-tensor-good-iso`: its determined construction
  `integralScalarTensorGoodIso` and proved hom-component equation.
- `def-pur-integral-tensor-representative-reassociate`: the real construction
  `integralTensorRepresentativeReassociate`, exactly the existing comparison with
  the target functor reassociated, and its proved component formula.
- `lem-pur-integral-scalar-tensor-representative-descent`: the fully proved
  `integralScalarTensorRepresentativeDescent`, taking an arbitrary representative
  natural isomorphism and descending it with its normalized square and uniqueness.
- `lem-pur-normalized-integral-scalar-tensor-descent`: the fully proved
  `normalizedIntegralScalarTensorComparison`, specializing that descent and
  rewriting the specified chain component formula.

Each node has its own new module, sources, proof steps, dependencies, searches,
and Lean attachment. The original node's proof and proof dependencies now record
this route. No existing interface was changed, so no change record or forced
adaptation is required.

The first delivery run passed compilation of the cleaned sources and reached
server preflight. Its static signature check found four node records stale after
the compile-time extractions. Those records were updated to the exact source
signatures; the Lean files are unchanged. The delivery is rerun with this metadata
repair.

The search-kind advisory was also resolved by running LeanSearch explicitly
(in addition to LeanFinder, Loogle and grep) and recording its eight algebraic
scalar/adic-completion hits. None supplies this specified sheaf Roos comparison.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
