## What changed
Repaired the false arbitrary-P completion interface. Completion now receives affine opens S and V containing g(a) and a, the containment V ≤ g⁻¹(S), and the actual `StandardSingleFlatCounitPresentation` of `p ∣_ S`, `M.restrict (p ⁻¹ᵁ S).ι` and `g.resLE S V hVS`. Thus its K is a sheaf complex on S with both identifications e,t and their equation. P is existentially constructed from the stalk of that same K. The first repair's global `StandardSingleFlatCounitPresentation p M g` hypothesis was not justified by affine localization and has been removed.

The new module `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationPresentationData` supplies these genuinely local witnesses. Its separate node replaces the vacuous zero-complex data route. The old `StandardSingleFlatCounitLocalizationData` module and its theorem remain unchanged: the strengthened replacement has a new name, avoiding an interface change to an unheld module. `StandardSingleFlatCounitLocalization` changes only its private proof import and forced final proof lines, passing the actual local witnesses. Its existing signature is byte-for-byte identical. No definition or target statement changes.

## Proved and sorry left
Holes closed: none. The existing `AlgebraicGeometry.standardSingleFlatCounit_localization_completion` remains a named sorry, now with the corrected intermediate statement (node `lem-pc-standard-single-flat-counit-localization-completion`). Added hole: `AlgebraicGeometry.standardSingleFlatCounit_localization_presentation_data` (node `lem-pc-standard-single-flat-counit-localization-presentation-data`). Both have source citations and complete natural-language proof docstrings. The caller `AlgebraicGeometry.standardSingleFlatCounit_localization` is still proved by combining these two statements, and is not counted as a newly closed hole. This is a required interface repair, not proof progress; one hole is added in the import closure. No arbitrary data are chosen from either unproved existence theorem in a definition.

## No longer needed
Removed the proof-only import `Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalizationData` from the caller, and its proof dependency `lem-pc-standard-single-flat-counit-localization-data`. Its zero-complex witness has no identification with direct image and cannot support the counit argument. No other old proof dependency is removed: completion's stalk-derived-extension comparison remains part of its pending proof plan. No unit realization is bypassed. The removed module may remain reachable elsewhere; only the maintainer determines global pruning.

## Where the brief, the DAG or earlier work was wrong
The old completion's universal arbitrary P is false on identity maps of Spec(k), M=O, P=0: eR in degree zero would identify zero with k. The previous repair incorrectly transported an affine local presentation to a global bounded presentation on B; affine opens do not supply a global bounded complex. In particular a non-quasi-compact base need not have a uniform cohomological bound. The replacement keeps K on S and transports only stalk coordinates back to B and A. The original repair also lacked verbatim old/new signatures and a valid statement_change record; these are supplied.

## New nodes
`lem-pc-standard-single-flat-counit-localization-presentation-data`, in its own Lean module, gives the affine-neighborhood choice and local sheaf presentation, strictly the first step of localization, not the parent's conclusion. It has recorded LeanSearch (unavailable), LeanFinder, Loogle and grep searches, source, full proof plan, creation/blueprint fields and verbatim Lean signature. The existing completion node records the counterexample, corrected statement and all citers; the parent node records the new two-step proof. Change record: `coord/changes/standardSingleFlatCounit_localization_completion.md`.

## Forced adaptations
`Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization` originally supplies P, hPbound, hPflat to completion. Against the repaired completion this fails because P is expected to be an open of B. The adaptation obtains S,V, their membership and affine witnesses, containment hVS and the local hpres from the new data theorem and passes those exact arguments. It also replaces the old proof-only data import. No public signature or declaration visibility is altered. The original caller was compiled in scratch against the changed dependencies to establish the failure; the adapted caller compiles in the delivered set.

## Second reading by M2
1. Compared each delivered module with the repository version. Only completion's intermediate signature changes, explicitly recorded with its Spec(k) counterexample and verbatim old/new signatures. The caller's declaration signature is byte-for-byte identical; the data module is new. All public definitions are unchanged.
2. Compiled the full delivered set in import order through lcompile.py. Inspected every declaration: no axiom, unsafe, opaque, implemented_by, extern, or sorry in data. Exactly the two named theorems above remain sorry. A successful scratch `#print axioms` checked all three delivered theorems; only the three permitted logical axioms and sorryAx are allowed. The latter is expected from the explicitly reported holes, not evidence of completion.
3. Checked local data on identity maps of Spec(k), zero M, empty schemes (a point excludes empty A), arbitrary integer degrees and arbitrary non-quasi-compact B. Containment hVS makes g.resLE well-defined; e,t and their equation now concern the same restricted morphisms and K. The two statements split affine-neighborhood presentation from stalk/counit transport and do not restate the caller. Repeated searches using different terms through LeanSearch (service unavailable), LeanFinder, Loogle and Mathlib grep; read the library stalk-derived-extension comparison and searched the local presentation modules. Restriction-stalk isomorphisms exist, but no existing theorem supplies the complete local presentation or all the completion coordinates directly. Neither hole can be closed by a short application of those tools.
4. Read the unit `sk-thm-picard-coherence` and its realized field: it has no listed realizations here. The affine-local/stalk route is preserved, no unit step or chapter dependency is bypassed. Imports for public signatures remain public; both caller-only helper imports are plain. The obsolete zero-data import and dependency are fully listed above. Since completion remains sorry, its nontrivial derived comparison dependency is retained, not falsely claimed pruned.
5. Checked the three node files against Lean: local schemes and sheaf in the new node match its signature; completion has valid correction metadata including every citer; parent proof_deps are exactly the two lemmas its proof applies. The old data node is not changed. New-node metadata and recorded searches are included. Existing node proof plans explicitly distinguish the pending proof from actual completed work.

Second reading changed the unjustified global presentation to an actual restricted presentation with hVS; moved the new theorem to its own module; kept the old unheld data theorem unchanged; repaired stale/wrong node dependencies and correction records; completed the natural-language proof docstrings; rewrote the report to disclose zero holes closed and one added.

## Forced adaptations

### Sheaf.AlgebraicGeometry.StandardSingleFlatCounitLocalization
Original against changed dependencies failed:
```
/tmp/forced-adaptation-xv0w9pzv/lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalization.lean:101:73: error: Application type mismatch: The argument
  P
has type
  CochainComplex (ModuleCat ↑(B.presheaf.stalk (g a))) ℤ
of sort `Type (u + 1)` but is expected to have type
  B.Opens
of sort `Type u` in the application
  standardSingleFlatCounit_localization_completion (fun {Y₀ B₀ A₀} ↦ h_affine) p M hM g a P

(with the modules compiled into /tmp/forced-adaptation-xv0w9pzv/.lbuild) [8.4 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
