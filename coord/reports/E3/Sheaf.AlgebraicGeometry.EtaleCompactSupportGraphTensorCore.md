## What changed

Proved `AlgebraicGeometry.Etale.compactSupportGraph_tensor_evaluation_core` in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportGraphTensorCore`, preserving its complete statement
and all public imports. Only this existing Lean module and its own DAG node are delivered.

The proof reuses `sfEtaleGraphProjectionArbitraryBase`. Three proved private helpers identify
the two graph constructions, identify the normalization's inverse with that canonical graph
comparison, and identify the two explicitly transported exact-pullback tensor comparisons.
The given unit equation then identifies `q` with the existing sum tensor mate. Postcomposing
the existing graph projection square with the projection isomorphism proves the required
mate equation by inverse cancellation.

Added proof-only imports of `SfEtaleGraphProjectionArbitraryBase`, and `import all` of
`EtaleCompactSupportGraphGeometricBaseChange` and `UnboundedProperOpenComposition`. These
reuse the already proved private graph-normalization calculation and open-comparison monicity
lemma. No imported module is changed and no private constant occurs in the public statement.
The unchanged, unused `adj` let in the original statement has its unused-variable linter
suppressed locally for this theorem. The node's proof, proof dependencies, and proof origin
now describe the implemented route. The blueprint unit route is preserved.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.compactSupportGraph_tensor_evaluation_core`, node
`lem-pur-compact-support-graph-tensor-evaluation-core`.

Zero holes remain in the item; zero holes are added; zero obligations are split off.
The private helpers `graphComparison_eq_source`, `normalizedComparison_eq_source`, and
`tensorComparison_eq` are all proved. Remote single-file compilation checked the proof;
the delivery tool runs the final compilation and axiom/preflight checks.

## No longer needed

No existing imports were removed and no library files are withdrawn. The following planned
proof dependencies are no longer needed for this item's route, and their modules are absent
from its new import closure:

- `lem-pur-etale-sheaf-projection-map`, module
  `Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap`.
- `lem-pur-etale-sum-flat-kflat`, module
  `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`.
- `lem-pur-etale-sum-tensor-totalization`, module
  `Sheaf.Paper.EtaleSumTensorTotalization`.

The explicit local-generator/K-flat/totalization argument is replaced by reuse of the proved
canonical graph tensor square. This removes those direct DAG obligations from this item;
it does not claim that other parents no longer need them. The old direct dependencies
`lem-pur-etale-open-derived-tensor` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` remain used transitively by the existing
graph projection theorem and canonical comparison constructions, so their library modules
are retained. No adopted source-library declaration, signature, public import, or proof is
removed or modified.

## Where the brief, the DAG or earlier work was wrong

The stated theorem is unchanged and is true. The planned fresh sheaf-generator and derived
descent calculation was unnecessary: the library already proves the canonical graph
projection square. The only missing glue was identifying the normalization with the graph
comparison, which follows from monicity, homotopy localization, the existing normalization
calculation, and uniqueness of a clopen adjunction with specified counit. This closes the
previously split obligation without another split or any new mathematical assumption.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
