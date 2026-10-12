## What changed

Added the proof-only module `Sheaf.RingTheory.PopescuDelocalizeHeightZeroData`.
It states the construction's concrete finite-presentation factorization data; the
assigned theorem combines that data into `CanBePopescuResolved` by unfolding its
definition. The original theorem signature is unchanged.

## Proved and sorry left

The original theorem `Algebra.canBePopescuResolved_of_local_height_zero` is reduced
by a complete Lean proof to the concrete data theorem. One new sorry remains:
`Algebra.exists_popescu_resolution_data_of_local_height_zero`, in node
`lem-weil-pbc-popescu-delocalize-height-zero-data`. Its docstring records the
Stacks 07FA construction and all required properties.

## No longer needed

No imports were removed. The concrete data theorem is the only new dependency;
all existing imports remain available for the construction proof.

## Where the brief, the DAG or earlier work was wrong

No statement or definition was changed. The full Stacks construction is still the
remaining intermediate proof obligation.

## New nodes

`lem-weil-pbc-popescu-delocalize-height-zero-data`: concrete finite-presentation
factorization data for the height-zero delocalization construction.

## Earlier second reading (a previous round; superseded)

The combining proof compiles and preserves the assigned theorem signature. The new
statement is the concrete factorization data required by the definition and is
strictly used as an input to the final constructor.

## Second reading by W3

1. **Repository diff and statements.** Compared both delivered Lean modules with the
repository versions. The existing target theorem has the same signature byte for byte;
the only change is its proof. The added theorem is in a new proof-only module and does
not alter an existing declaration.

2. **Compilation and axioms.** Compiled both modules with `lcompile.py --all`; they
compile without errors. The target proof contains no `sorry`, while the single remaining
`sorry` is the named split theorem
`Algebra.exists_popescu_resolution_data_of_local_height_zero`. No definitions contain
`sorry`, and no forbidden declarations were added.

3. **New statement.** Checked the split theorem against `CanBePopescuResolved`: it is
the explicit existential factorization data obtained by unfolding the target predicate,
with exactly its finite-presentation, composition, singular-ideal containment, and
noncontainment fields. It is used directly to construct the target witness and has the
Stacks 07FA construction and source recorded in its docstring and DAG node. Searches
found no existing declaration with this statement.

4. **Route and pruning.** The target proof follows the shortest available route: obtain
the explicit data theorem and package it into `CanBePopescuResolved`; no unit-level route
is bypassed. Existing imports were retained because they are part of the module's prior
public interface or support the open construction theorem; the new data import is plain
`import`, since it is proof-only.

5. **DAG agreement.** The target node records the data theorem as its proof dependency,
and the new node records the exact Lean declaration, source, proof split, and dependency
on the Stacks construction. The unit assignment remains unchanged.

I changed only the proof of the target theorem, added the explicit data theorem/module
and matching node, and documented this second reading.
