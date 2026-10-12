## What changed
The parent module assembles its unchanged conjunction from separate source and target
component statements, using proof-only imports. The two components are new modules with
named, documented holes. The parent DAG route now records conjunction introduction.

## Proved and sorry left
Closed hole: `AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons`.
Added holes: `AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source`
(node `lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source`) and
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_target`
(node `lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-target`).
This is a decomposition: one hole closed, two added; net -1, not a completed mathematical
proof. The parent still depends on sorryAx through those components.

## No longer needed
The parent directly no longer uses nodes `def-weil-pbc-cartesian-square`,
`def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-geometric-point-field-extension`,
`lem-weil-pbc-inverse-image-stalk-germ`, `lem-weil-pbc-strictly-henselian-sections-stalk`,
and `lem-weil-pbc-unrestricted-strict-henselization-stalk` as proof dependencies.
Removed their four direct proof-only imports from the parent:
`Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`,
`Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`,
`Sheaf.Paper.InverseImageStalkGerm`, and
`Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`.
They remain the documented proof route of the open components; no module is pruned from
the import closure.

## Where the brief, the DAG or earlier work was wrong
The first report called this a proof without identifying the net increase in holes.
The parent node had not been updated. The component nodes lacked search records and
omitted dependencies described in their docstring proofs; their blueprint tags named
the parent. A stale sandbox copy of AbelianExchangeCubeComparisons lacked a newer import.
No mathematical error in the parent statement or unit route was found.

## Second reading by G1
1. Compared the parent against the repository by diff: its existing theorem signature
is byte-for-byte unchanged. No definitions or public imports changed. Removed dependency
scaffolding copies, including the stale AbelianExchangeCubeComparisons copy, from delivery.
2. All three delivered modules compile with lcompile.py. The parent has no sorry; only
the two documented component theorems do. No forbidden declaration forms or hollow
definitions were added. Scratch #print axioms for all three theorems showed only propext,
Classical.choice, Quot.sound, and sorryAx.
3. The components are respectively one conjunct, strictly less than the entire parent,
not restatements of it. Reviewed their canonical-map transport proofs and q=0, zero
sheaf, empty total space, field extension, and arbitrary pullback-model cases. All are
consistent with 03Q9 and 03QO. Ran independent grep, leanfinder, and loogle searches; LeanSearch returned an internal
server error, recorded as unavailable;
read unrestricted stalk, germ restriction, cohomology comparison, and cube definitions.
No exact existing theorem closes these fixed comparison statements directly. The
remaining formal work includes identifying each fixed map with the restriction composite.
4. The parent proof uses conjunction introduction and exactly the two component lemmas.
Removed its unused direct proof imports; the open components retain their stated proof
plans and their imports. Reviewed sk-thm-p1 realized fields: none is bypassed or changed.
5. Added the missing parent-node proof route; completed component searches, dependency
records, self-contained statements, verbatim Lean signatures, sources, and blueprint
metadata. Corrected component docstrings to describe their own map and own proof route.
Verdict: acceptable decomposition, with two genuine unresolved component proofs.
Changes by second reading: imports, stale scaffolding removal, docstrings and blueprint
tags, DAG metadata, and accurate hole/pruning accounting in this report.

## New nodes
`lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source` states only source
comparison invertibility, in StrictHenselizationExchangeCubeStalkIsosSource.lean.
`lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-target` states only target
comparison invertibility, in StrictHenselizationExchangeCubeStalkIsosTarget.lean.
Both retain the original hypotheses and separate parts of the original conclusion;
neither changes an existing statement. No change record is required.
