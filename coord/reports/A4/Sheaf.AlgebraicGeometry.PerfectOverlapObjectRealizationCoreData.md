## What changed

The core theorem now obtains a stagewise comparison-data family and packages it with
the fixed overlap equivalences.  The two nontrivial construction steps are isolated as
named intermediate theorems: `perfect_overlap_object_realization_core_data_family`
provides the family, and `perfect_overlap_object_realization_core_of_data` assembles
the transition, base comparison, natural comparison, and object pins.  Both are
explicit stage-3 split nodes with source and proof plans in the DAG.  The proof-only
imports remain limited to the fixed overlap APIs; unused direct imports of
`Mathlib.CategoryTheory.HomCongr` and
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` were removed.

## Proved and sorry left

Proved: `AlgebraicGeometry.perfect_overlap_object_realization_core_data`, by combining
the two strictly lower intermediate statements.

Sorry left:

- `AlgebraicGeometry.perfect_overlap_object_realization_core_data_family`, node
  `lem-pc-perfect-overlap-object-realization-core-data-family`;
- `AlgebraicGeometry.perfect_overlap_object_realization_core_of_data`, node
  `lem-pc-perfect-overlap-object-realization-core-of-data`.

## No longer needed

Removed the direct imports `Mathlib.CategoryTheory.HomCongr` and
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`.  No other imports or
DAG nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG treats both the simultaneous stagewise data and the final cartesian
transition/object-pin assembly as informal construction steps, but the current Lean
interfaces expose no theorem for either construction.  They are therefore represented
as two strictly lower named statements, while the target theorem is proved by a real
combination of those statements.

## New nodes

`lem-pc-perfect-overlap-object-realization-core-data-family` records the stagewise
comparison-data existence step.

`lem-pc-perfect-overlap-object-realization-core-of-data` records the cartesian
transition/base-comparison/object-pin assembly once the family is supplied.  Both
nodes are stated in the item module and have complete source, proof-plan, and search
records.

## Earlier second reading (a previous round; superseded)

The target theorem is unchanged and compiles.  The two new statements are strict
substeps: one supplies only the stagewise data family and the other assembles only the
core package from that family.  The unit route remains through the fixed overlap
equivalences and comparison-data interfaces.

Change records: `coord/changes/perfect_overlap_object_realization_core_data_family.md`,
`coord/changes/perfect_overlap_object_realization_core_of_data.md`, and
`coord/changes/perfect_overlap_object_realization_core_data_imports.md`.

## Second reading by A4

1. **Interface comparison.** I compared the delivered module with the repository
   version.  The signatures of the existing structure, statement definition, and
   target theorem are unchanged byte for byte.  The only interface changes are the
   declared proof-only import pruning and the two named split statements recorded
   above.  Verdict: pass.

2. **Proof and axioms.** I compiled the module with `lcompile.py`; it succeeds with
   no errors.  The only remaining `sorry`s are the two named split theorems, each
   public and documented with its source and proof plan.  There are no axioms,
   unsafe declarations, hollow definitions, or hidden `sorry`s.  Verdict: pass.

3. **Statements and split nodes.** The family theorem supplies only the simultaneous
   stagewise comparison data.  The core-of-data theorem supplies only the assembly
   of the core after that family is given.  Both are strictly simpler than the target
   existential package, use unchanged hypotheses, and have matching DAG nodes with
   source, dependencies, proof plans, and search records.  Verdict: pass.

4. **Pruning and route.** Direct uses of `Mathlib.CategoryTheory.HomCongr` and
   `Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses` are absent from
   the delivered proof, so their direct imports were removed and recorded.  The
   remaining route still uses the fixed stage/apex equivalences and comparison-data
   APIs required by the unit.  Verdict: pass.

5. **DAG agreement.** The target node records the two split declarations in its
   `proof` and `proof_deps`; each split node records the declaration and the exact
   Lean module.  The target statement and the unit route are unchanged.  Verdict:
   pass.

The second reading made no further code or DAG changes.
