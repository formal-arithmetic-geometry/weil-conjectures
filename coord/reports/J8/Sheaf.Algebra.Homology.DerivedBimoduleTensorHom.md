## What changed

Restored `lean/Sheaf/Algebra/Homology/DerivedBimoduleTensorHom.lean` from the exact archive
named in `coord/rework.tsv`. Repaired `ModuleCat.derivedBimoduleAdjunction`,
`ModuleCat.derivedBimoduleEvaluation`, and `ModuleCat.bimoduleClosedCurry` by selecting
`DerivedCategory.braidedCategory' (ModuleCat B)` with a body-local `letI` in each.
The upstream braiding is now an explicit definition. Every declaration, signature,
import, docstring, and the existing theorem proof is otherwise preserved. No upstream
source file or quarantine archive is changed. No global instance is introduced.

Change record: `coord/changes/j8-derived-bimodule-canonical-braiding.md`.

Validation: the archived original fails at lines 67, 77, and 98 with the missing
`BraidedCategory (DerivedCategory (ModuleCat B))` instance. The repaired module compiles
through `lcompile.py` in 26.1 seconds. The repaired item also compiled in the two-file check (37.5 seconds), followed by
the byte-identical quarantined consumer
`Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison` (54.1 seconds).
The temporary unchanged consumer copy was removed before delivery; its archive stays
unchanged, and no consumer edit is included.

## Proved and sorry left

Definition repair, not a proof delivery: 0 holes closed, 0 holes added, 0 split off.
The one pre-existing hole remains `ModuleCat.derived_bimodule_tensor_hom`
(blueprint node `lem-trf-derived-bimodule-tensor-hom`), with its original full statement,
source and proof docstring. All eleven existing definitions have concrete bodies.
The assigned missing-instance defect is fixed in all three affected definitions.

## No longer needed

None. No imports, declarations, nodes, or modules are removed or withdrawn. The DAG
attachment and proof route remain intact, including the unfinished parents' dependencies.
The source-library boundary is respected.

## Where the brief, the DAG or earlier work was wrong

The recorded rework is an upstream interface repair: the canonical derived braiding is
no longer a global instance. Relying on implicit instance synthesis in the three bodies
was the compiler defect. The current DAG proof refers to three recently split model
nodes without Lean attachments, unlike the brief's generic proof-readiness description;
this does not prevent the independently assigned definition repair. Their statements and
the original theorem are retained. No new nodes or statement changes are needed.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
