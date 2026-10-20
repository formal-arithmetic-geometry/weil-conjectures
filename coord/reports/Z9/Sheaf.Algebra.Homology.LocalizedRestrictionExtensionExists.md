## What changed

Completed the retirement repair recorded in coord/retire-items.tsv for
Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists. Withdrawn its duplicate
module through deleted.txt. The proved theorem
CategoryTheory.localized_restriction_extension_exists is supplied unchanged by
WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExists.

Adapted both current consumers. ProjectionCompactification changes one private
proof import. RingedSliceExtensionPreservesExact uses a proof-only import all of
the source twin and its proved private CategoryTheory.extensionSheafAdjunction,
instead of the removed public Nonempty wrapper. This reuses the existing actual
construction, with no duplicated helpers and no new declaration. All surviving
signatures, definitions and visibility are unchanged; no upstream file changes.

Reattached new-localized-restriction-extension-exists to the source theorem and
removed the obsolete wrapper from its declaration list. Updated that node and
lem-weil-pbc-ringed-slice-extension-preserves-exact to describe the actual imports
and adjunction reuse. No unit or chapter route changes.

Change record: coord/changes/Z9-localized-restriction-extension-retirement.md.

## Proved and sorry left

This is a zero-hole retirement repair: proved 0 of 0 textual sorries, added 0,
split off 0, and left 0 sorries in the delivered Lean files. The retained source
CategoryTheory.localized_restriction_extension_exists is already fully proved.
Its redundant wrapper CategoryTheory.extensionSheafAdjunction_nonempty is removed,
with its sole consumer adapted to the proved concrete adjunction construction.
SheafOfModules.ringedSliceExtension_preserves_exact retains a complete proof.
Both adapted modules compile individually through lcompile.py --all (5.4 s and
5.0 s), without warnings. The delivery preflight also checks their declarations.
No definition chooses data from an unproved existence theorem.

## No longer needed

Pruned Sheaf.Algebra.Homology.LocalizedRestrictionExtensionExists and both imports
of it. Removed its duplicate private Hom-equivalence and adjunction helpers and
the public Nonempty wrapper. The unchanged source twin provides the main theorem
and the concrete adjunction implementation. No new bridge module or wrapper is
needed. All declared mathematical dependencies remain needed by the source proof:
def-weil-extension-by-zero-presheaf and lem-weil-pbc-sheafification-exact.
No DAG node is deleted and no upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a repeatedly split proof obligation, but the
current queue identifies this item as retire, with zero sorries. The main theorem
has long been proved in both trees. The difference blocking automatic retirement
was the public Nonempty wrapper absent from the source twin; import all permits
its sole consumer to reuse the existing proved private construction directly.
The retirement inventory lists three consumers; the localized-adjunction Sheaf
copy is already absent. Source scanning finds the two adapted consumers only.
Switching the exactness consumer's import alone reproduces the missing-wrapper
compiler error; replacing its single adjunction expression repairs that error.
No mathematical statement was found false, weakened, or changed.

## Second reading by Z9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
