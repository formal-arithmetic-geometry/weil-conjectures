## What changed

Completed the seven theorem proofs in `Sheaf.Paper.AffineLinePuritySource`.
The five coordinate identities unfold only their cached object definitions.
For `etaleSource_plus`, the existing ordinary etale pullback stability theorem supplies
finite Tor amplitude [a,b]; exact chart pullback bounds the shifted Tate coefficient
below by -2; `DerivedCategory.isGE_tensor_of_torAmplitudeIn` gives the bound a-2.
For `source_plus`, exact comparison preserves that bound, and the already constructed
canonical `sourceComparison` transfers it to the literal pro-etale source.
Added the private proof import `WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic`.
Updated the source node's proof, proof dependencies and proof origin to describe this proof.
All existing signatures, definitions, attributes, docstrings and public imports are retained.
The unit route is unchanged. Edge cases require no extra hypotheses: empty Y, Ke=0,
arbitrary positive coefficient level and every annihilating exponent are covered by
the general exact-pullback and finite-Tor tensor estimates.

## Proved and sorry left

Closed all seven original holes, in namespace
`AlgebraicGeometry.ProEtale.AffineLinePurity`:

- `coefficient_comparison_eq`
- `etaleCoefficient_eq`
- `source_eq`
- `etaleSource_eq`
- `source_coordinate_eq`
- `etaleSource_plus`
- `source_plus`

Node: `def-pur-affine-line-purity-source`.
No sorry remains in the delivered module; no holes or new declarations are added.
This is seven holes closed, zero holes added, and zero split off.
The server compiled the complete proof version in 22.2 seconds; delivery validates
the final version with the shorter tensor API and its axiom probe.

## No longer needed

No existing imports, nodes or modules are withdrawn. The original node had no proof
steps or proof dependencies to prune. All original public imports are retained.
The exploratory proof import `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeGE`
is omitted from the final packet: the stronger finite-interval tensor estimate is already
available through `Stability.Basic`. No local-freeness theorem or unit-prime assumption
is needed for boundedness: the finite Tor bound belongs to the other tensor factor.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The source node had an empty proof plan, despite
the theorem docstrings containing the required argument; it now records the Lean proof.
The current blueprint paragraph is shorter than the older expanded source description,
but its specified pullback/tensor source and finite-coefficient route are preserved.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
