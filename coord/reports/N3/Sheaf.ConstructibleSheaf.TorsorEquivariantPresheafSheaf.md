## What changed

The duplicate-removal repair is already present in the repository: this module now remains a
public compatibility import of `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`, where
the canonical restricted-scalars theorem is defined once. I clarified the module docstring to
state that this file re-exports the historical entry point and intentionally declares nothing.
No theorem signature or mathematical statement changed.

## Proved and sorry left

There are no declarations or `sorry`s in the assigned module. No new theorem or intermediate
statement was added. The canonical theorem imported from `TorsorEquivariantModuleIsSheaf` also
contains no `sorry`.

Holes closed by this delivery: none (0 of 0 in the assigned module).
Holes added or split off by this delivery: none. This is documentation of an already
landed repair, not new proof progress.

## No longer needed

The duplicate theorem declaration, its private function-sheaf construction, equivariance
subfunctor proof, and copied gluing argument are no longer needed in this compatibility module;
they were removed by the landed duplicate-removal repair. No additional imports or nodes are
needed for the declaration-free compatibility entry point.

Pruned by this delivery: none. The removals described above belong to the earlier repair.

## Where the brief, the DAG or earlier work was wrong

The repair brief describes a duplicate theorem in this module, but the duplicate-removal repair
is already on the repository base. The current module is intentionally declaration-free and
re-exports the retained theorem from `TorsorEquivariantModuleIsSheaf`. The stale queue entry
therefore has no remaining proof hole to close. This delivery records the compatibility module's
current repaired interface and a documentation clarification so the assigned source is changed.

The canonical implementation remains `AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf`
in `Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf`; callers retain that theorem through
this public compatibility import.

## Second reading by N3

1. PASS: Compared the delivered module with the repository using `diff -u`. Only four
   module-docstring lines differ. The public import, module commands and visibility are
   byte-for-byte unchanged. Neither version declares a theorem or definition; there is
   no signature change or change record needed.
2. PASS: Compiled the delivered module locally through `lcompile.py`, with no errors or
   warnings. It has no `sorry`, forbidden declaration or data construction. A scratch
   copy with `#print axioms
   AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf` compiled and
   reported exactly `propext`, `Classical.choice` and `Quot.sound`. Read the canonical
   implementation: the continuous-function sheaf, local equivariance subfunctor and
   discrete locally constant comparison prove the retained restricted-scalars statement.
3. PASS (not applicable): No statement is split off or added. There are no new statements
   requiring edge-case tests, source proofs, nodes or duplicate searches.
4. PASS: The shortest route for this compatibility entry point is its existing public
   import of the canonical implementation. Making it a proof-only import would break
   its re-export purpose. There are no other imports to prune. Checked the node's old
   proof dependencies and `dag/units/sk-thm-p1.json` (`realized`); neither the canonical
   route nor any unit realization changes. No nodes or modules are pruned by this delivery.
5. PASS: The existing node `lem-weil-pbc-torsor-equivariant-presheaf-sheaf` already names
   the retained declaration in `TorsorEquivariantModuleIsSheaf`. Its proof, proof_deps and
   proof_origin describe that actual continuous-function/subfunctor argument. Read the
   landed duplicate-removal and transparency change records. No node update is needed
   for this declaration-free documentation edit.

Second reading changed only this report: made the zero holes closed, zero holes added
and zero modules pruned explicit, and recorded the independent checks. No Lean repair
was necessary. The assigned module remains listed as a duplicate-removal repair, which
permits a delivery with no remaining proof holes.
