## What changed

Repair C-ed57b by restoring the actual original theorem in
`Sheaf.AlgebraicGeometry.StrictLocalMateContinuityPresentation`, on
`Scheme.strictHenselizationScheme s` and `Scheme.strictHenselizationStructuralMap s`.
Restore its node's Sheaf module/file, `existing: false`, and original statement.
The module contains the complete original assembly argument, not a re-export shell.

The duplicate root definitions have already been removed by the reviewed W4 landing
`9c024ef6813f3086cb759e63324375d6ccd29569`; its upstream-extension reuse and user census
are recorded in `coord/changes/W4-strict-henselization-retirement.md`.
This packet retains that fix and every quarantine archive.

The upstream proof helpers now use the other strict-local scheme. Restore 24 proved
counterparts under `Sheaf.AlgebraicGeometry.StrictLocalSmallModel`, following those
upstream proofs and retaining the DAG's geometry, germ-colimit and injective-representative
route. These are the already separate results of the original DAG, each fully proved.
Reuse the existing original-model scheme, structural map, restriction, germs,
projection data, termwise sections and base-change cone. Distinct helper names use the
prefix `smallModel_`; upstream declarations and files stay unchanged.
Existing nodes are attached to these realizations; no new mathematical statement or node
is introduced. The change record lists the exact substitutions and consumer effect:
`coord/changes/E3-strict-local-mate-presentation-upstream.md`.

## Proved and sorry left

This is a zero-hole repair. The archived item had 0 sorries, the returned shell had 0,
and the restored theorem has 0. Holes closed: none (0). Holes added: none (0).
Split off: none (0). Every one of the 24 helper modules is fully proved, with 0 sorries.
No existing proof is replaced by a hole and no definition chooses arbitrary unproved data.

Restored theorem: `AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation`.
Its proof obtains the geometry and projection data, obtains the canonical source colimit,
and fills every field of `GlobalCohomologyContinuityPresentation`.

Validation through `lcompile.py`:

- All 24 helper modules and the restored item compile. The initial batch's four
  line-length warnings have been corrected.
- The exact archived `StrictLocalBaseChangeGlobalHomology` source, with its original
  declaration name, imports, statement and proof, compiles unchanged (3.2 seconds).
  The excluded `__probe.lean` file only appends the axiom query; it is not delivered.
- `#print axioms AlgebraicGeometry.Etale.nonempty_strictLocalBaseChange_continuityPresentation`
  lists exactly `propext`, `Classical.choice` and `Quot.sound`.
- No delivered Lean line exceeds 100 characters; no `sorry`, `axiom`, `unsafe`,
  `opaque`, `implemented_by` or `extern` is introduced.

## No longer needed

Remove the returned packet's public import of
`WeilConjectures.AlgebraicGeometry.StrictLocalMateContinuityPresentation`.
Replace the canonical-model proof imports
`WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence`,
`WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit`, and
`WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas`
by their original-model realizations.

The canonical implementations stay intact in the adopted source library. No mathematical
node, module or DAG dependency is claimed pruned. The helper nodes' source proof routes
are retained, as are the item node's proof dependencies and the parent dependency.
New helper imports are limited to their statement interfaces and proof dependencies;
redundant imports of the original germs, projection data, geometry and termwise sections
are removed when the same public interfaces are already supplied transitively.

## Where the brief, the DAG or earlier work was wrong

The earlier packet changed the Lean model and checked a canonical-model consumer instead
of the original consumer. It did not repair the assigned statement or its importer.
This repair restores both without claiming definitional equality between the two models.

The root duplicate merge requested by the return has independently landed in W4's repair.
After that merge, importing canonical-model helpers together with the original Sheaf
interfaces still reproduces a second, distinct collision at
`AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq`. The restored small-model
helper chain avoids that collision and proves the required original statement.

Searches found the fully proved canonical-model argument and generic mate-pasting lemmas,
but no theorem directly supplying this presentation on the original small spectrum.
The restored proof follows the already-stated DAG rather than treating the two models
as definitionally identical or substituting the canonical statement. The unit record
`sk-prop-h2` has empty realized lists; none is changed or bypassed.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
