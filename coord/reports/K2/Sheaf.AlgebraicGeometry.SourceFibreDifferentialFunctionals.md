## What changed

Proved `AlgebraicGeometry.exists_source_fibre_differential_functional` in
`Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals`, with its statement and
existing public imports unchanged. Added proved private helpers for residue-field section
evaluation, sectionwise stalk functionals, the normalized pullback adjunction, base change,
and transport through pullback symmetry. The construction uses actual germs and sections,
including zero sections on empty inverse images; no arbitrary witness supplies definition data.

Added proof imports of `Sheaf.AlgebraicGeometry.RelativeDifferentialSheafBaseChange`,
`WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections`, and
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk`. Updated the item's proof plan
and proof dependencies to describe this implementation. No other existing module changes.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_source_fibre_differential_functional`
(node `lem-zl-source-fibre-differential-functionals`).

Item holes: 1 before, 0 after. Holes added: 0. Split-off statements: 0.
Every private helper is proved. The proof uses the existing differential base-change theorem
and normalized pullback adjunction. The final single-file compile passed without warnings
in 28.5 seconds through `lcompile.py`; delivery also checks the dependency axioms.

## No longer needed

No original import was removed and no module was withdrawn. This proof does not require these
three previously planned dependencies, so they were removed from the item's `proof_deps`:

- `lem-weil-pbc-module-skyscraper-stalk-adjunction`
  (`Sheaf.AlgebraicGeometry.Modules.ModuleSkyscraperStalkAdjunction`): the germ-evaluation
  construction is written and proved directly.
- `lem-weil-pbc-module-stalk-pullback`
  (`WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk`): only the normalized
  Hom adjunction on sections is needed, with no identification of pullback stalks.
- `lem-weil-pbc-module-pullback-structure-sheaf`
  (`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`): the constructed
  sheaf morphisms already take values in the actual structure sheaf of T.

These are proof-dependency removals, not claims that those modules are globally unused.
The unit's statement and realized steps remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature repair was needed. The existing ingredients suffice to close
the obligation without another split. The old plan used stalk-pullback and structure-sheaf
comparison isomorphisms that the direct sectionwise construction avoids. Pullback symmetry
accounts explicitly for the opposite factor order in the base-change theorem's interface.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
