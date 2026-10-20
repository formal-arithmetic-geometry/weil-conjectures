## What changed

Restored lean/Sheaf/AlgebraicGeometry/UniversalLowestFiberRanks.lean from its
quarantine archive. Replaced the retired Sheaf.AlgebraicGeometry.DerivedPullbackComposition
proof import by WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition, the module
now recorded by lem-pc-ringed-spaces-derived-pullback-composition. Fixed the resulting
zero-object transport universe inference by annotating ModuleCat.restrictScalars and
SheafOfModules.evaluation with the existing coefficient universe u.

All declarations and public imports match the archive. The existing bounded-flat-model,
termwise residue pullback, rank-of-sections and fibre base-change argument is preserved.
The compiler passed without warnings in 17.8 seconds. The import-direction check passed.
Change record: coord/changes/T3-universal-lowest-fiber-ranks-restoration.md.

The only textual consumer is the quarantined PerfectUniversalLowestZeroModel. Its call
at line 79 matches the unchanged signature; no adaptation is forced by this repair.
The original node attachment and unit route are retained, with no node changes.

## Proved and sorry left

This is a zero-hole rework restoration. The archive had zero direct sorry holes;
zero closed, zero added, zero split off, zero left. The complete proof of
AlgebraicGeometry.Scheme.universalLowest_fiber_ranks is restored and compiles
(node lem-sc-universal-lowest-fiber-ranks). Its two private helpers,
tensor_single_vanishes and finrank_sections_of_rank, also remain completely proved.
This repair makes no claim to newly discharge holes in its imported dependencies.

## No longer needed

Removed the obsolete proof import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
and replaced it with its adopted source counterpart. No mathematical dependency,
DAG node or module is pruned: every existing proof dependency is still used.
No source-library declaration is removed. All other imports support the existing
statement or the four-step proof.

Searches: msearch leanfinder for Tor-amplitude residue-fibre vanishing found the general
derived-category isGE/isLE zero-homology lemmas, but no replacement for both rank clauses;
loogle confirmed Module.finrank_baseChange, which the proof already uses; msearch grep
returned no exact match. Local rg confirmed the source free-sheaf sections calculation
and found no duplicate universalLowest_fiber_ranks declaration in the live library.

## Where the brief, the DAG or earlier work was wrong

The assigned module is a quarantined repair with zero direct holes, rather than an
unproved theorem. Its complete archived proof must be restored. Its stale proof import
still targeted the retired duplicate derived-pullback construction; current composition
is supplied by the adopted source module. With that corrected, evaluation needed an
explicit universe to avoid an AddCommGrpCat universe mismatch.

The mathematical statement and the DAG proof are unchanged. In particular the proof
retains no a <= b assumption and handles rank zero and empty T; perfection remains an
unused hypothesis of the original interface. No new theorem or node is introduced.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
