## What changed

Added the strictly smaller single-stage theorem
`AlgebraicGeometry.perfect_overlap_object_realization_core_data_at` as the remaining
geometric construction split. The family theorem is now proved by choosing that
single-stage data independently for every `k ≥ j` and pairing the family with `Unit`.
The three redundant proof imports were removed because retained imports provide all
used declarations transitively.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.perfect_overlap_object_realization_core_data_family`
(1 of 2 original holes). This is a decomposition: the family is assembled by a real
dependent-choice proof from the strictly smaller pointwise statement below.

Sorry left:

- `AlgebraicGeometry.perfect_overlap_object_realization_core_data_at`, node
  `lem-pc-perfect-overlap-object-realization-core-data-at`;
- `AlgebraicGeometry.perfect_overlap_object_realization_core_of_data`, node
  `lem-pc-perfect-overlap-object-realization-core-of-data`.

The item theorem remains proved from the family and core-of-data statements. The
delivery adds one strictly smaller split-off hole and leaves the other original hole
unchanged; the net hole count is zero.

## No longer needed

Removed imports: `Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps`,
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition`, and
`Sheaf.AlgebraicGeometry.TwoOpenComparisonDiagram`; all are available through retained
imports and are not needed directly by the module.

## Where the brief, the DAG or earlier work was wrong

The family theorem does not require a global Hom-continuity import (which would create a
cycle through object realization). It only needs independent pointwise stage data. The
new node records that geometric construction, and the family proof performs the valid
dependent-choice packaging.

## New nodes

`lem-pc-perfect-overlap-object-realization-core-data-at` isolates the one-stage
restriction and pullback comparison required to construct a family.

## Second reading by S4

1. **Interface comparison.** Compared the delivered module with the repository version. Existing declaration signatures and definitions are unchanged byte for byte; the only interface addition is the declared pointwise split theorem, with its matching DAG node. Verdict: pass.

2. **Proof and compilation.** Compiled the module with `lcompile.py` and compiled the sandbox import closure successfully. The family theorem is proved by dependent choice from the strictly smaller pointwise theorem. The two geometric construction holes are explicitly named, documented, and matched by DAG nodes; no hollow definition or forbidden declaration was added. Verdict: pass.

3. **Statements and nodes.** Checked the pointwise statement against the prescribed comparison-data type and its source dependencies. It is strictly smaller than the family statement (one fixed stage), true as the required construction step, and not a duplicate of an existing library declaration. The family node proof and dependencies now follow the Lean proof. Verdict: pass.

4. **Pruning and route.** The three removed imports are unused by the compiled proof and remain available transitively through retained imports. The family construction keeps the unit route by using the pointwise stage construction; no unit-level step is bypassed. Verdict: pass.

5. **Axioms and delivery metadata.** The changed files contain no new axioms, unsafe declarations, or untracked sorry outside the named split theorems. The report, pointwise node, and family node consistently describe the decomposition and proof dependencies. Verdict: pass.

Changed during second reading: appended this review section only; no Lean proof or statement repair was necessary.
