## What changed

Restored `lean/Sheaf/AlgebraicGeometry/RawModuleScalarHomCompositeFormula.lean`
from its recorded quarantine archive. Preserved its theorem signature verbatim,
its public imports, visibility, docstrings, original proved helper and factor
constructions. Removed the private proof import of
`WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula`, which
loaded conflicting upstream copies of the Sheaf source/coefficient definitions.

The proof evaluates `rawModuleAbelianHomMap`, applies the proved generic
`map_three_factors` calculation, and identifies the raw module pullback factors by
the new proved private generic `raw_triangle_whisker` lemma and definitional
equality. The private lemma unfolds abstract raw triangle/whiskering data and
uses `Category.assoc`. It adds no public statement or remaining obligation. The item node now records this direct calculation and its existing
definition dependencies. No prerequisite or source-library module is edited.

Change record: `coord/changes/G2-raw-module-scalar-hom-composite-restore.md`.
The archive and repaired theorem signatures were compared textually, and all
Lean lines have at most 100 characters. Single-file server compilation passed
with the generic raw-triangle calculation (51.6 seconds). The axiom audit of
`AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula` reports only
`propext`, `Classical.choice` and `Quot.sound`. The final canonical item module then compiled in 50.8 seconds, and the
unchanged quarantined parent `rawModuleAbelianHomMap_source_formula` compiled
against that sandbox artifact in 27.4 seconds. Its axiom audit also reports only
the same three permitted axioms. All diagnostic probes were removed.

## Proved and sorry left

`AlgebraicGeometry.Etale.rawModuleScalar_hom_composite_formula` has a complete
proof. Its private helpers `map_three_factors` and `raw_triangle_whisker` are also proved. This assigned repair
had zero textual holes in the archived source and has zero holes after repair:
0 holes closed, 0 holes added, 0 split off, no sorry left in the delivery.
The repaired defect is the duplicate-declaration import failure, not a new proof
hole. The statement continues to cover zero classes, degree zero, identity
arrows and zero coefficient sheaves without additional hypotheses.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackModuleFormula` and
this node's proof dependency on
`lem-sbc-raw-scalar-pullback-module-formula`: its elementary reassociation is now
performed directly with the original Sheaf factor definitions. The upstream
module and all its declarations remain intact for their other consumers.

The coefficient-square theorem and scalar source-square theorem are unused by
this proof. The existing public coefficient-square import stays because the
statement needs `scalarCoefficientFactor` defined there. No module or DAG node
is withdrawn, and the unit route and quarantined parent dependency are retained.

## Where the brief, the DAG or earlier work was wrong

This is the recorded 2026-10-20 quarantine repair. The archived module already
contained a proof with zero sorry, but its upstream module-formula proof import
brought in different declarations with the same fully qualified names as the
retained Sheaf factors. The route note's shared-factor repairs are already
present in the adopted upstream constructions; importing their formula module
across the retained Sheaf interface causes the current failure. The existing
private functor-composition helper and a generic whiskered raw-triangle
calculation suffice to repair it
without another split, a changed definition or a broader interface migration.

`tools/downstream.py` reports no active library importers because the parent is
also quarantined. Searching the quarantine and DAG finds the still-required
`Sheaf.AlgebraicGeometry.RawModuleAbelianHomSourceFormula` parent; this delivery
preserves that parent's source and dependency rather than treating the absence
of active importers as authorization to withdraw the item.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
