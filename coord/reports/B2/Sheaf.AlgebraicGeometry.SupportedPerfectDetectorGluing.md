## What changed

Replaced the invalid earlier sandbox attempt with a two-part reduction of
`AlgebraicGeometry.supported_perfect_detector_gluing`, preserving its full signature and
original docstring. The final proof extracts the lifted smaller-cover object Q, adds the
supported Koszul summand to obtain E, maps the supplied retract through each shift functor,
and cancels its inclusion/projection to transfer shifted-Hom subsingletonness from E to Q.
The Koszul lemma supplies invertibility of the open unit; conditional detection then gives zero.
No definitions, existing statements, instances, or public imports of the item changed.

Added one named theorem per new module: `Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift`
and `Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand`. Their statements separate the
induction/lifting/conditional-adjunction argument from the supported Koszul/unit argument.
Updated the original node's proof, proof_deps and proof_origin to match this composition.

All three modules compile without errors or style warnings through lcompile.py --all.
Searches run: LeanFinder (no exact scheme-level detector match), Loogle (Retract and its
functorial map found), Mathlib grep (no matching supported/perfect gluing theorem), and
LeanSearch (HTTP service unavailable). The searches are recorded in searches.jsonl.
Blueprint searches for "supported perfect detector" (no matches) and "Koszul" (ten unrelated
blueprint entries) found no existing declaration of either new intermediate statement.
The existing project dependencies were read before creating the new statements.

## Proved and sorry left

Closed the item's only original hole:
`AlgebraicGeometry.supported_perfect_detector_gluing`
(node `lem-pc-supported-perfect-detector-gluing`). Its proof is complete from the two
named intermediate statements, including the shifted-retract cancellation argument.

Added two holes, both whole proofs of public named theorems in separate modules:

- `AlgebraicGeometry.exists_supported_detector_open_lift`
  (node `lem-pc-supported-detector-open-lift`): constructs the lifted smaller-cover
  detector and proves detection conditional on invertibility of the open unit.
- `AlgebraicGeometry.exists_supported_koszul_unit_summand`
  (node `lem-pc-supported-koszul-unit-summand`): adds the supported Koszul summand and
  proves invertibility of that unit under shifted orthogonality.

This is a decomposition: one upper hole closed, two lower holes added, not a completed
sorry-free mathematical proof. Neither intermediate is the original theorem repackaged:
the first cannot detect without the extra open-unit hypothesis; the second has no induction
hypothesis and concludes only invertibility of a specified unit, not global detection.
The witnesses remain in theorem proofs; no definition chooses an arbitrary existential object.

## No longer needed

Removed the six original proof imports from the item's module and replaced them with the
modules of the two intermediate statements:

- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
- `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`
- `Sheaf.AlgebraicGeometry.KoszulOpenOrthogonality`
- `Sheaf.AlgebraicGeometry.PerfectSupportedMapLift`
- `Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition`
- `Sheaf.AlgebraicGeometry.SupportedOpenPushforward`

These six modules and their original proof-dependency nodes remain needed inside the two
intermediate arguments, so no original DAG branch or module is globally pruned. The unit's
realized fields are empty for this item; its prescribed supported-generator route is retained.
The obsolete candidate/support/detector nodes and IsSupportedOn change record from the
previous sandbox attempt were removed rather than delivered. Those nodes were never valid
parts of this reduction; no replacement support definition was introduced.

## Where the brief, the DAG or earlier work was wrong

The prior `supported_candidate_is_detector` was false: the zero perfect supported object
satisfies its hypotheses but cannot detect nonzero supported objects. Its candidate theorem
also threw away the detector clause of induction. The previous report claimed a valid
reduction and a second reading despite these faults. Both the statements and report were
replaced; no second-reading section is written by this worker.

Read Stacks Tag 0A9A directly at https://stacks.math.columbia.edu/tag/0A9A because the local
literature/stacks-project/perfect.tex is absent. The new split follows the induction paragraph
and its last adjunction paragraph, and the intervening Koszul/unit paragraph respectively.
The original DAG's source plan remains mathematically appropriate. It does not supply
ready-to-apply Lean declarations for the cover transport, quasi-coherence of perfect objects,
exact restriction/derived-adjunction identifications, and global cone-stalk conservativity.
Those technical arguments are explicitly included in the two remaining theorem docstrings,
rather than silently assumed or hidden as partial-proof sorries.

Edge cases checked mathematically: T empty forces supported objects to be zero; U empty
reduces the unit-summand assertion to affine supported Koszul detection; U top makes the unit
already invertible; redundant affine charts still leave a strictly smaller cover after erasing
one chart. Q zero is allowed in the unit-summand lemma: the Koszul part forces only the unit,
not zero; the open-lift lemma supplies the separate conditional-detection hypothesis. On a
nonempty proper U, a nonzero object invisible on the omitted chart need not be detected by Q
until the unit hypothesis is supplied. This is exactly the condition missing previously.

The intermediate adjunction is written on the localized module site already used by
Scheme.IsPerfect, with its localizations supplied by the original instance binders. Its
identification with open-subscheme restriction through Modules.overEquiv is part of the
remaining lift/unit proofs, avoiding any new localization choice in a definition.

## New nodes

`lem-pc-supported-detector-open-lift`, in
`dag/nodes/sec-picard-framework/lem-pc-supported-detector-open-lift.json`, corresponds to
`Sheaf.AlgebraicGeometry.SupportedDetectorOpenLift`. It retains the full smaller-cover
detector hypothesis and concludes only conditional detection after open-unit inversion.
Its source is Tag 0A9A's induction and final adjunction paragraphs.

`lem-pc-supported-koszul-unit-summand`, in
`dag/nodes/sec-picard-framework/lem-pc-supported-koszul-unit-summand.json`, corresponds to
`Sheaf.AlgebraicGeometry.SupportedKoszulUnitSummand`. It requires an affine-complement
open cover and a perfect supported Q, concludes existence of E with Q a retract, and forces
only the open unit under orthogonality. Its source is Tag 0A9A's Koszul/unit paragraphs.

Both nodes have self-contained statements, source proofs in words, the three actual search
kinds, the original chapter/unit and blueprint ancestry, and verbatim Lean signatures.
No existing definition or interface change needs a change record or forced adaptation.

## Second reading by B2

1. Compared the delivered item module with the repository version. The theorem signature and
   docstring are unchanged byte for byte; only proof imports and the proof body changed.
   Verdict: pass.
2. Compiled all three delivered modules with `lcompile.py --all`. There are no compiler errors,
   style warnings, forbidden declarations, or sorries outside the two explicitly named split-off
   theorems. A scratch-copy axiom probe on all three declarations returned exactly propext,
   Classical.choice, Quot.sound, and sorryAx (the two open intermediate proofs). No data is
   selected in a definition. Verdict: pass.
3. Read both split-off statements and their node records. Each is a genuine conditional or
   auxiliary reduction, has the required source, proof description, searches, and matching Lean
   signature; neither merely restates the original target. Read Stacks Tag 0A9A directly
   (https://stacks.math.columbia.edu/tag/0A9A): its lifting/final-adjunction paragraphs and
   Koszul/unit paragraphs justify precisely the two conclusions. Independently checked empty
   T, empty U, U top, Q zero, and redundant affine charts; no omitted detector hypothesis
   or false zero-object shortcut occurs. New LeanFinder search for derived open immersion
   unit invertibility and Koszul orthogonality found no match; Loogle confirmed Retract and
   its split maps; local rg found only the existing affine detector and related original
   dependencies, not either intermediate. The independent searches are in searches.jsonl.
   Verdict: pass.
4. Checked the proof route and imports against the DAG. The item uses exactly the two new
   intermediate declarations; their proof dependency lists retain the original open-restriction,
   Koszul, pushforward, and lifting branches. No unused item imports remain, and no old branch is
   claimed pruned. Verdict: pass.
5. Checked the unit metadata and report. The original unit and chapter are retained, and the
   gluing proof combines the conditional open-lift route with the supported Koszul unit route by
   shifted retract cancellation. Verdict: pass.

Changed only the report by adding this second-reading record; no Lean declarations or node
statements were changed during review.
