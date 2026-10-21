## What changed

Restored Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology from the exact
quarantine path recorded in coord/rework.tsv. Repaired its imports for the current
library. The old public StrictHenselizationRestriction import is a retired empty
module with no published compiled artifact. The statement now imports its actual
providers publicly: Mathlib.CategoryTheory.Sites.GlobalSections,
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap, and
WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs.

The two private proof imports are StrictLocalMateContinuityPresentation (Sheaf)
and DerivedEtaleCohomologyLimit (WeilConjectures). The complete theorem statement,
its docstring and assembly proof are byte-identical to the archive. All original
small-colimit-model objects are preserved; the canonical upstream theorem concerns
a different strict-local model and is not substituted. No source-library file changes.

The existing DAG node and its Lean attachment already describe this exact proof,
so no node changes are necessary. Both declared proof dependencies are used.
The change record is coord/changes/K7-strict-local-global-homology-restoration.md.

Validation: the unmodified archive fails to compile because the retired restriction
module's compiled artifact is missing. The repaired module compiles without warnings
in 4.4 seconds through lcompile.py. A separate compiler pass with #print axioms
reports exactly propext, Classical.choice and Quot.sound for the theorem (4.8 seconds).
The diagnostic command was then removed. All Lean lines are at most 100 characters.
The three archived direct consumers were checked at their theorem applications;
the unchanged statement supplies precisely the same input. No live direct importer
exists, and no consumer source requires adaptation from this import-only repair.

## Proved and sorry left

Zero-hole rework repair. Proved 0 of 0 textual sorries; closed 0, added 0,
left 0, split off 0. The existing complete theorem
AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology is restored
and kernel checked with only the three permitted axioms. This is neither a new
proof closure nor a decomposition. No unfinished obligation is handed on.

## No longer needed

Removed the retired public import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction;
its empty module is replaced by the three actual statement providers above.
Removed these six unused historical private imports:

- Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
- WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
- Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit
- Sheaf.AlgebraicGeometry.StrictHenselization
- Sheaf.AlgebraicGeometry.StrictLocalGermRestrictionIso
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

These imports supply no proof step directly. Necessary underlying geometry and
cohomology declarations remain available through their owning interfaces and the
two proof dependencies. No mathematical node or module is claimed pruned: the
retired shims were already retired independently. The source-library declarations,
all quarantined archives and every parent dependency remain intact.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes a holed module. This assigned item is instead a
quarantined zero-hole restoration after a failed cluster build, as recorded in
coord/rework.tsv. Its absence did not mean withdrawal. No proof step or statement
needed mathematical correction: the existing presentation gives the colimiting
source cocone and the restriction equation, derived continuity gives the extended
target cocone's colimit property, and Mathlib colimit uniqueness makes the mate
invertible.

Read Stacks etale-cohomology.tex, theorem-higher-direct-images (Tag 03Q9), including
its affine-neighbourhood limit and injective-complex restriction argument. The
qcqs hypotheses, arbitrary bounded-below K, and every integer degree are preserved.
The unit sk-prop-h2 has empty realized lists and its route is unchanged.
LeanFinder returned generic cocone extension/colimit results; Loogle returned the
exact IsColimit.nonempty_isColimit_iff_isIso_desc lemma used in the proof; the search
grep found its Mathlib applications. Repository search found the upstream theorem,
but its strictLocalization/strictLocalizationToBase statement differs from the
original-model theorem assigned here. The current Sheaf presentation is the exact
original-model dependency and already has its fully proved small-model repair.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
