## What changed

Replaced the proof of `AlgebraicGeometry.geometricallyIrreducible_iff_genericResidueField`
by a topological argument using only Mathlib. The private helper
`irreducibleSpace_iff_genericFiber` proves the required criterion for open surjective
morphisms. Pullback symmetry and pasting identify its generic fibre with the field base
change of the generic residue field. The existing theorem signature and public imports
are unchanged. The node proof follows this shorter route below the unit level; the unit
has no realized step attached to this node.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.geometricallyIrreducible_iff_genericResidueField`
(node `lem-zl-generic-point-geometric-irreducibility`). The private helper
`AlgebraicGeometry.irreducibleSpace_iff_genericFiber` is also fully proved.
Holes closed: 1. Holes added: 0. Sorries left: none. No split statements.

The resumed session's required `deliver3.py --no-push` passed: the module compiles,
the axiom probe accepts every declaration, and the preflight reports
`CODEX: changes a node file`. The theorem signature is unchanged, every Lean line
is within 100 characters, and the node's proof_deps is the union of its proof steps'
uses. All remaining dependencies are Mathlib declarations. No new nodes,
definitions, public declarations, or change records are needed.

## No longer needed

Removed proof-only imports:

- `WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`
- `Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso`
- `Mathlib.AlgebraicGeometry.FunctionField`
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`
- `Sheaf.AlgebraicGeometry.GeometricIrreducibilityAffineLocal`
- `Sheaf.AlgebraicGeometry.GeometricallyIrreducibleAlgebraClosure`

The proof no longer needs nodes
`lem-weil-pbc-reduction-universal-homeomorphism`,
`lem-weil-pbc-closed-immersion-residue-field-iso`, `def-pc-integral-scheme`,
`lem-sc-integral-function-field-affine-fraction`, `def-weil-pbc-module-stalk`,
`def-pc-scheme`, `lem-zl-geometric-irreducibility-affine-local`, and
`lem-zl-geometric-irreducibility-subalgebra-colimit`.
The two obsolete reduction and closed-immersion tool approvals are withdrawn.
The statements' public imports remain needed. No claim is made that the pruned modules
are unused by other parents.

## Where the brief, the DAG or earlier work was wrong

The original route is mathematically valid but unnecessary. Mathlib already proves
universal openness of all morphisms to a field spectrum, and its open-map criterion
for a dense set of irreducible fibres replaces the reduction and algebra-colimit
argument. This handles nonreduced schemes directly without changing the statement.
The singleton-spectrum cases and nonempty generic fibres are explicit in the proof.
The prior attempt's compile-server connection failure did not recur in the
successful dry run of this resumed session. The retained proof compiles unchanged
after comparison with current sources.
Searches: msearch leanfinder and loogle found no exact theorem; local rg found the
open-map fibre criterion and universal-openness instance. No new statements or nodes.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
