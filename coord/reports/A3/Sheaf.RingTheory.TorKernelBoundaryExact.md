## What changed

Proved `CategoryTheory.exists_tor_kernel_boundary_exact` by applying the existing
low-degree Tor exact sequence to the kernel inclusion and the given surjection.

## Proved and sorry left

Closed `exists_tor_kernel_boundary_exact`; no sorries added.

## No longer needed

No imports removed; the proof uses `Sheaf.Paper.TorLongExactFirstVariable`.

## Where the brief, the DAG or earlier work was wrong

The planned construction is subsumed directly by the already proved low-degree Tor
exact sequence theorem.

## Second reading by A3

1. The theorem signature is byte for byte unchanged from `sheaf-dag`; it has the same
commutative ring, module, arbitrary linear map, surjectivity hypothesis, chosen boundary
map, and two exactness conclusions. The proof specializes the existing low-degree Tor
sequence to the kernel subtype and quotient map.

2. The proof compiles without errors or warnings. The axiom probe reports only
`propext`, `Classical.choice`, and `Quot.sound`; there are no `sorry`, axioms, unsafe,
opaque, extern, or implemented-by declarations.

3. The proof uses the already proved `tor_long_exact_first_variable`; its hypotheses are
provided by `Submodule.subtype_injective`, surjectivity of `q`, and
`LinearMap.exact_iff` with `Submodule.range_subtype`. The extracted first and second
exactness clauses match the target after unfolding the chosen maps. No new statement was
added.

4. The proof follows the shortest available route and keeps the kernel short exact
sequence specialization. The old naturality node was not used and is removed from the
node's `proof_deps`; no imports were removable because the existing theorem and module
category notation require them.

5. The unit route is preserved through the existing low-degree Tor theorem. The DAG node
now records the actual proof dependency, proof text, and proof origin.

Changed during second reading: restored the original theorem docstring, updated the node
proof metadata from the obsolete naturality dependency to
`lem-weil-pbc-tor-long-exact-first-variable`, and recorded this review.
