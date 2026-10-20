## What changed

Retired Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent,
a kind-retire item in coord/retire-items.tsv. The existing official module
WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent
has the exact same three public theorem signatures and complete proofs.
Redirected the lean records of the parent, section and open nodes to that module.
The proof plans, mathematical statements and dependencies are unchanged.
No current Lean module imports the retired copy, so no consumer requires editing.

Change record: coord/changes/R5-retire-affine-torsor-single-stabilizer-component.md.
The sandbox deleted.txt withdraws only the Sheaf copy; no upstream file is edited.

## Proved and sorry left

Holes closed: 0 of 0. Holes added: 0. Split off: 0. No sorry remains in the item.
The three already proved declarations are preserved in the official twin:

- AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component_section
  (lem-sbc-affine-torsor-single-stabilizer-component-section).
- AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component_open
  (lem-sbc-affine-torsor-single-stabilizer-component-open).
- AlgebraicGeometry.Scheme.affine_torsor_single_stabilizer_component
  (lem-sbc-affine-torsor-single-stabilizer-component).

The original copy compiled in 4.3 seconds. A scratch module with only the official
twin import proved examples with all three original signatures and compiled in
2.1 seconds. Each official theorem's printed axioms are exactly propext,
Classical.choice and Quot.sound. The module comparison confirms the signatures
are textually identical, without a change of hypotheses, universes or conclusions.
This delivery completes a retirement, not a newly closed proof hole.

## No longer needed

Pruned the duplicate module
Sheaf.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent.
Its three nodes remain and now attach to the official declarations. No mathematical
node is pruned. All of the old copy's imports disappear with its withdrawal:

- Mathlib.AlgebraicGeometry.Morphisms.Etale
- Mathlib.AlgebraicGeometry.Morphisms.Finite
- Mathlib.Algebra.Algebra.Subalgebra.Lattice
- WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction
- WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorStabilizerSectionOpen
- WeilConjectures.AlgebraicGeometry.Morphisms.AffineInvariantBasicOpenDescent
- Mathlib.Topology.Connected.Clopen
- Mathlib.AlgebraicGeometry.Properties

The official twin still needs these imports. This retires duplicate declarations;
it does not claim to eliminate their genuine proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes proving sorries, but this assignment is an
explicit kind-retire entry in coord/retire-items.tsv, with zero original holes.
The earlier retirement inventory lists a historical Sheaf consumer that is now
absent. Current full-source import scans find no importer of the copy. The
DIFFERENT label reflects comments, copyright and linter-option scope, rather than
a mathematical API difference; all three public signatures match verbatim.
The stale STATEMENT-DISPUTED comment describes an already repaired former section
statement. The current section statement and its official twin are already proved.
The DAG's old lean attachments were the remaining references needing redirection.
No new nodes, statement corrections or forced consumer adaptations are needed.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
