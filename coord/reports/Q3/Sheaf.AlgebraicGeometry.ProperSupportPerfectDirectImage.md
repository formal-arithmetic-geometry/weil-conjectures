## What changed

Restored Sheaf.AlgebraicGeometry.ProperSupportPerfectDirectImage from its current
quarantine archive. Replaced the two withdrawn public Sheaf imports with the public
WeilConjectures owners of derivedPullback and the single-complex tensor-pullback
Additive instance. Redirected the private relatively-flat base-change proof import
to its recorded WeilConjectures owner. The theorem signature and docstring remain byte-identical to the archive.
The final restriction functor in the proof receives the explicit universe annotation
`SheafOfModules.overFunctor.{u}` to resolve an inference error. This is the assigned import repair,
not an additional proof or a rebase.

Change record: coord/changes/Q3-ProperSupportPerfectDirectImage-restoration.md.

Read Stacks perfect.tex, lemma-base-change-tensor-perfect (Tag 0A1H), the item's
node, all six proof dependencies and their Lean signatures, and the unit record.
The existing proof implements precisely its recorded base-change and local
Noetherian-model argument. Searches with msearch leanfinder and loogle produced
no shorter direct-image theorem; msearch grep had no matches. Direct rg found
the archived theorem and its two archived callers.

## Proved and sorry left

AlgebraicGeometry.properSupport_perfect_directImage has a complete existing proof.
This repair closes 0 of 0 sorries, adds 0 sorries, and splits off 0 statements.
No sorry remains in the delivered module. No new proof credit is claimed.

Validation: the restored module compiled cleanly through lcompile.py in 13.6 seconds.
All three replacement import directions are acyclic according to import_direction.py.
Archived theorem comparison confirms only the explicit universe annotation changed
below the imports; there are zero literal sorry tokens and every Lean line is at most
100 characters.

## No longer needed

Removed the empty public imports Sheaf.AlgebraicGeometry.DerivedPullback and
Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition in favor of their
current definition owners. Removed the private compatibility re-export import
Sheaf.AlgebraicGeometry.RelativelyFlatTensorBaseChangeIso in favor of its current
owner. These are import-path repairs; no mathematical node or module is pruned.
All six existing proof dependencies and the item's Lean attachment are retained.
No quarantine archive is removed and deleted.txt is not used.

## Where the brief, the DAG or earlier work was wrong

The item is a zero-hole quarantine repair. Its archived imports still point to
withdrawn Sheaf modules, causing the public-signature visibility failure recorded
in coord/rework.tsv. After fixing those imports, compilation found a universe
constraint at the restriction transport; the explicit universe annotation repairs it. The restored theorem continues to use ordinary termwise
pullback of G, as Stacks 0A1D and the existing statement require. No mathematical
statement or definition was corrected and no consumer adaptation is necessary.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
