## What changed

Completed the assigned retirement of the declaration-free
Sheaf.AlgebraicGeometry.RawModuleScalarSourcePrefix shim. Its only remaining importer,
Sheaf.AlgebraicGeometry.RawModuleScalarSourceClassFormula, now publicly imports
WeilConjectures.AlgebraicGeometry.RawModuleScalarSourcePrefix directly and keeps its
explicit RawModuleScalarDerivedPullbackIso compatibility import. The definition node
already attaches to the canonical upstream declaration; only its lean.note is extended.
Change record: coord/changes/H9-retire-raw-module-scalar-source-prefix.md.

Validation: the adapted consumer compiles through lcompile.py --all (exit 0, no
diagnostics, reported Lean time 8.8 seconds). Both the full import closure and
public-import closure lose exactly the declaration-free shim and gain no module.
The delivered node differs only in lean.note, and a live/quarantine scan confirms
no other import of the withdrawn path.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off, and zero
holes left in the delivered modules. The item and adapted consumer have no declarations
or sorry proofs. This is a completed retirement repair, not a theorem proof or a
renaming/decomposition of a hole. AlgebraicGeometry.Etale.rawModuleScalarSourcePrefix
remains the unchanged concrete upstream definition. No adopted source file is edited.

## No longer needed

Retire lean/Sheaf/AlgebraicGeometry/RawModuleScalarSourcePrefix.lean and remove its
public import from RawModuleScalarSourceClassFormula, replacing it by the canonical
upstream import. The former shim's other public import,
Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso, is already explicit in the
consumer and stays there. No mathematical node, dependency, definition or unit step
is pruned. All four mathematical parents still use the same canonical prefix node.
There are no remaining live or preserved-quarantine imports of the withdrawn path
after this adaptation.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 proof brief describes a deep split chain, but the actual queue
assignment is kind retire and the current item has zero declarations and zero holes.
The old retire-items.tsv DIFFERENT classification and three-consumer list predate
P2's reexport migration, G2's formula retirements and K4's source-factor retirement.
The current source has one remaining importer. Its migration preserves exactly the
same public declarations and data, including the historical scalar API. The DAG's
canonical definition attachment and all mathematical dependencies remain correct.

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
