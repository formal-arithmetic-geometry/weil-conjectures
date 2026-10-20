## What changed

Retire the duplicate Sheaf.CategoryTheory.BrownCohomologicalRepresentability as
explicitly requested in coord/retire-items.tsv. Attach
lem-pc-brown-cohomological-representability to the complete theorem of the same
name in WeilConjectures.CategoryTheory.BrownCohomologicalRepresentability.
Update its proof plan to describe that source proof. Change only the proof import
in Sheaf.CategoryTheory.GrothendieckDerivedBrownRetractData; all declarations and
proof applications in that consumer are unchanged. No source-library file changes.
Change record: coord/changes/B4-brown-cohomological-retirement.md.

The source statement has exactly the same category, universes, instance parameters,
compact generation, homologicality, discrete-limit preservation and conclusion.
Its axiom probe passed with only propext, Classical.choice and Quot.sound. The
adapted consumer compiled cleanly in 1.2 seconds. A separate example with the
old exact declaration signature applies the canonical theorem and compiled in
1.0 seconds, verifying that no binder or universe adaptation is needed. The Stacks source read was
derived.tex, lemma-brown (Tag 0A8F), including its entire proof. Empty generating
families and all shifts retain their original hypotheses; no cases are removed.

## Proved and sorry left

Zero holes initially, zero holes left, zero holes added, zero split off. This is a
duplicate retirement, not a newly proved hole or decomposition.
CategoryTheory.brownCohomologicalRepresentability remains fully proved in the
canonical adopted source. The consumer's
grothendieckDerived_localization_brown_data remains fully proved.

## No longer needed

Withdraw lean/Sheaf/CategoryTheory/BrownCohomologicalRepresentability.lean.
Remove its proof imports Sheaf.CategoryTheory.BrownRepresentabilityConstruction
and Sheaf.CategoryTheory.CohomologicalGeneratorDetection. The canonical Brown
proof does not need nodes lem-pc-brown-generator-construction and
lem-pc-cohomological-generator-detection; remove them from this node's proof_deps.
Those modules and nodes are not deleted; their other uses are unaffected.
The old public imports of CompactlyGenerated and Triangulated.Yoneda leave with
the duplicate file. Its consumer already has the public imports needed by its
unchanged statement. The canonical source's imports remain verbatim.
All three parent DAG dependencies and the unit route remain intact through the
canonical attachment. The replacement argument is the complete adopted source
proof, not absence of current importers.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module; this item already has a complete
proof and is explicitly a listed duplicate retirement. The initial read saw a
transiently absent source during repository synchronization; the live source
subsequently appeared, and there is no current rework row for this module.
The old attachment names the duplicate instead of the complete adopted source.
The retirement list's Sheaf BrownRepresentabilityRightAdjoint consumer is already
retired; its canonical replacement imports the canonical Brown source directly.
No mathematical statement was wrong or changed.

Searches actually run through msearch.py: LeanFinder for cohomological Brown
representability returned homological-functor and Yoneda APIs but no full Brown
theorem; Loogle for preadditiveYoneda reported an unknown identifier; grep for
brownCohomologicalRepresentability|exists_bijective found no relevant Mathlib
result. Direct source searches found the complete adopted Brown theorem and its
proved BrownRepresentability.exists_bijective tool, used here.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
