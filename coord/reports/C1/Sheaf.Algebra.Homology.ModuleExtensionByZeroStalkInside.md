## What changed

Retired `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside` through `deleted.txt`.
The node `lem-sc-module-extension-by-zero-stalk-maps-inside` now points to the existing
`AlgebraicGeometry.moduleExtensionByZero_stalk_inside` in
`WeilConjectures.Algebra.Homology.ModuleExtensionByZeroStalkInside`. The full statement is
identical except for its name. All upstream declarations, signatures, attributes, imports
and proofs are preserved. The node's proof and dependencies remain accurate for the
source proof. No new lemma, definition or module is introduced.

Change record: `coord/changes/retire-module-extension-by-zero-stalk-inside.md`.

## Proved and sorry left

This is a duplicate-retirement repair with zero holes initially and zero holes finally.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
The already proved duplicate `AlgebraicGeometry.ModuleExtensionByZeroStalkInside` is removed;
its exact replacement is the existing `AlgebraicGeometry.moduleExtensionByZero_stalk_inside`.
No `sorry` is left in a delivered Lean file.

Validation: a sandbox scratch module states the duplicate's full original signature and proves
it with `exact moduleExtensionByZero_stalk_inside X`; this checks every binder and the entire
germ identity, including the chosen unit, against the upstream theorem. The scratch file is
not part of the delivery. This compiled cleanly in 2.2 seconds through `lcompile.py`.
Both axiom lists contain exactly `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

Pruned module: `Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkInside`.
Its duplicate declaration `AlgebraicGeometry.ModuleExtensionByZeroStalkInside` is unnecessary.
The current source tree has no importer or caller of that duplicate, as verified by
`tools/downstream.py` and full import/identifier searches. The historical consumer has
already moved to the source tree, where it imports the upstream module and uses the upstream
name. No consumer adaptations are needed.

The withdrawn module's three public imports were
`WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact`,
`WeilConjectures.Algebra.Homology.ModuleStalkFunctor` and `Mathlib.Topology.Sheaves.Module`.
Its three private proof imports were
`Sheaf.Algebra.Homology.ModuleExtensionByZeroStalkMorphism`,
`WeilConjectures.Algebra.Homology.ModuleExtensionByZeroUnitIsIso` and
`Mathlib.Geometry.RingedSpace.Stalks`. They disappear with this duplicate file only; the
upstream proof retains its own imports. No dependency theorem or node is declared globally
unnecessary. In particular, the linear stalk morphism and invertible-unit lemmas remain
needed by the source proof. The inside-stalk node itself remains, attached to the source.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but the queue marks this item `retire`:
the duplicate is already proved and has zero holes. The node previously named the upstream
declaration while locating it in the duplicate Sheaf module. This delivery corrects that
attachment. The 2026-10-20 retirement census mentioned an old Sheaf consumer; that consumer
is now absent and its adopted source counterpart already uses the upstream theorem.
The unit route and the mathematical statement are unchanged. Source checked:
`literature/stacks-project/sheaves.tex`, `lemma-j-shriek-modules`, clauses (2)-(4).

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
