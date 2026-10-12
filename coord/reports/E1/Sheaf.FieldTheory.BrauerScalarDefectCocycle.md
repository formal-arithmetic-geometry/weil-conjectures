## What changed

The existing `Field.exists_brauerScalarDefect_cocycle` now combines scalar extraction
with homogeneous realization. Its signature and all existing definitions are unchanged.
Two new theorem modules are imported privately for the proof. Scalar extraction now
supplies joint local constancy, which is passed to homogeneous realization.

## Proved and sorry left

Hole closed: `Field.exists_brauerScalarDefect_cocycle` (one of one original holes).
Holes added and still open:

- `Field.exists_brauerScalarDefect_scalar_data`, node
  `lem-sc-brauer-scalar-defect-scalar-data`;
- `Field.exists_galoisUnits_cocycle_of_scalar_cocycle`, node
  `lem-sc-brauer-scalar-defect-cocycle-realization`.

This is a decomposition, not a completed proof: one hole closed, two added, net -1.
The first component constructs the scalar function and its properties without
homogeneous cohomology. The second concerns cochain conversion without matrices,
central simple algebras or descent lifts. Neither restates the full target.
No data definition chooses an arbitrary witness from an unproved existence theorem.

## No longer needed

Removed the redundant private import `Sheaf.FieldTheory.GaloisUnitsCohomology`;
its definitions are already exposed by BrauerScalarDefect. No library module
is pruned. The old direct
proof dependencies `def-sc-brauer-scalar-defect` and `def-sc-galois-units-cohomology`
are replaced by the two intermediate nodes in the target's `proof_deps`; both
remain statement dependencies and are used by the new intermediate statements.
Unchanged sandbox copies of BrauerScalarDefect and GaloisUnitsCohomology were excluded
from the delivery set. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The realization statement omitted continuity, although its prose described a
continuous cocycle. The algebraic cocycle equation does not supply this missing
hypothesis. Scalar extraction also omitted the local constancy needed downstream.
The second reader repaired both new signatures and their nodes, preserving the
existing target. The target node also needed updated proof dependencies; the new
proof docstrings were incomplete and the scalar-data node was not self-contained.

The blueprint ancestor helper returns None for this module-created item; the new
nodes instead extend the existing target's recorded ancestor path to lem-sc-brauer-zero.

## Earlier second reading (a previous round; superseded)

The previous report contained a pending second-reading placeholder.

## New nodes

`lem-sc-brauer-scalar-defect-scalar-data`: scalar extraction, the multiplicative
cocycle identity and joint local constancy, with a complete proof in words.
`lem-sc-brauer-scalar-defect-cocycle-realization`: conversion of a jointly locally
constant scalar cocycle to a homogeneous cycle with the exact evaluation formula.
No change record is required: these are new declarations, and no existing interface
was changed.

## Second reading by E1

1. PASS after repair. Diffed all existing sandbox modules against the repository.
   Only the target proof and private proof imports change. The existing target
   signature and docstring are byte-for-byte unchanged. Two other existing files
   were identical copies and were excluded. No definition or target type changes.
2. PASS. All three delivered modules compile in import order. Exactly two named
   whole-theorem sorries remain, listed above. No prohibited declaration, hollow
   definition or hidden hole occurs. Explicit axiom probes and the delivery tool's
   complete probe check ordinary axioms and the reported sorryAx dependencies.
   The target remains conditional on the two open intermediate theorems.
3. PASS after repair. Added joint local constancy on both sides of the reduction.
   Checked n=1 (the ordinary scalar coboundary), algebraically closed K (trivial
   Galois group), c=1, and unnormalized constant scalar lifts. n=0 is excluded by
   the unchanged hypothesis; no normalization is introduced. Each new theorem
   has a self-contained node and a full proof docstring. Independent LeanFinder,
   Loogle, grep and repository searches found matrix-center results for a proper
   substep, but no exact extraction-plus-topology result. The existing nonempty
   homogeneous-cocycle equivalence has no evaluation compatibility formula and
   therefore cannot justify the required equality.
4. PASS. The reduction retains the scalar-defect route; both new private imports
   supply precisely the lemmas used. Existing public imports provide the unchanged
   target's types and definitions. Read dag/units/sk-thm-br.json: its realized
   statement and step lists are empty, and no realized unit node is bypassed.
   No library module is claimed to be pruned.
5. PASS after repair. Updated target proof, proof_deps and proof_origin to the actual
   Lean reduction. Updated both new lean.statement records, TeX statements, proof
   sketches, dependency unions, ancestor paths and audit fields.

Changed in this reading: repaired missing local constancy, expanded the new proof
plans, synchronized all three DAG records, excluded unchanged module copies, and
removed a redundant private import, and corrected the accounting to decomposition (net -1).

Sources checked: Stacks Project [03R6](https://stacks.math.columbia.edu/tag/03R6),
[03R7](https://stacks.math.columbia.edu/tag/03R7), and the continuous cochain
complex in [0DVG](https://stacks.math.columbia.edu/tag/0DVG). The homogeneous
conversion in the docstring is the explicit agent-written argument for Mathlib's model.
