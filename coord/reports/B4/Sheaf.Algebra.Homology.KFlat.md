## What changed

Consolidated Sheaf.Algebra.Homology.KFlat with the existing adopted source module.
The file now publicly imports WeilConjectures.Algebra.Homology.KFlat and retains
CochainComplex.IsAcyclicTensorKFlat and CochainComplex.IsKFlatResolution as
semireducible aliases of its identical predicates. The copied tensor-Hom,
localization and zero-morphism proofs are removed. Public instances remain
available from the source under exactly their existing names and attributes.
No consumer or adopted-source file changes. The node proof metadata records the
source reuse and preserves its canonical independent-coefficient Lean attachment.

Change record: coord/changes/B4-kflat-source-consolidation.md. It includes verbatim
old and new definitions and every textual/direct consumer from the downstream scans.

## Proved and sorry left

The consolidated item compiles in 1.7 seconds.
The assigned definition repair has zero holes before and after. Zero sorries closed,
zero added, zero split off; no sorry remains. Both legacy predicates use concrete
source definitions. The two tensor zero-morphism theorems and all localization
infrastructure are the complete existing source proofs. All public signatures and
expanded propositions are preserved by definitional equality.

## No longer needed

No mathematical node or module is pruned. The KFlat module remains necessary for
its two legacy names; its copied private tensor-Hom and localization proofs are
unnecessary. The adopted implementation remains in the library unchanged.

The following direct imports are replaced by the public source import, which supplies
the same declarations transitively:

- WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
- Mathlib.Algebra.Category.Grp.FilteredColimits
- Mathlib.Algebra.Homology.BifunctorShift
- Mathlib.Algebra.Homology.QuasiIso

## Where the brief, the DAG or earlier work was wrong

This is a listed zero-hole retirement/consolidation item, not a theorem with a sorry.
The source twin lacks only the two legacy predicate names. Its implementation is
otherwise identical after renaming those predicates. Retaining these names as defs
preserves consumers that mark K-flatness locally irreducible; an abbrev would alter
that interface. The current source still contains the full copied implementation.
The final packet removes that implementation while retaining the consumer import path.
No new nodes are required, and no unit statement or proof step is bypassed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
