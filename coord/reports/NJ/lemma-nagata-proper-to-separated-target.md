# Stage-1 report: lemma-nagata-proper-to-separated-target

## Files written

- dag/nodes/sec-nagata-compactification/lemma-nagata-proper-to-separated-target.json: existing statement becomes a Mathlib leaf, matched exactly by AlgebraicGeometry.IsProper.of_comp, Mathlib/AlgebraicGeometry/Morphisms/Proper.lean:124-125. Zero new nodes; one Mathlib leaf (the item).
- citations.json: empty list, because the leaf has no proof steps.
- report.md: this report. Searches are logged in searches.jsonl.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint id/tag, IsProper.of_comp and the proper-over-separated notion found applications and special cases, not a project declaration stating this general triangle lemma. EliminationOfIndeterminacy.lean:75-76 explicitly says it is Mathlib's theorem and is not restated in the development. The item's existing lean metadata already names Mathlib; this is a Mathlib leaf, not a project attachment.

## WANTED

None.

## Corrections and source audit

The imported node already mentioned IsProper.of_comp in blueprint_lean but had no mathlib_match, had status imported, and retained an unclassified graph-factorization proof paragraph. The pinned Mathlib actually states exactly the item at Proper.lean:124-125. I retained all import flags and blueprint provenance and the old search entry, added the logged searches with their actual results, and replaced the obsolete proof by the leaf record. The statement gains only scheme and proper/separated definition references; no hypothesis or conclusion changes. All existing lean metadata is retained.

I read both the master and main-20261015 item texts and the main proof file; their statements and graph argument agree. I read the chapter and common-modification unit records. The latter needs properness of a map whose composite is proper and whose target map is separated, exactly this lemma. No unit realization change is appropriate: this is not the key node of that unit.

The local source literature/stacks-project/morphisms.tex, label lemma-image-proper-scheme-closed, lines 9948-9979, is Stacks Tag 01W6 by tags/tags. Its part (2) states that X proper over S and Y separated over S imply X → Y proper in a commutative triangle. Its proof factors through the graph, uses closed-immersion properness, base change, and composition. This is the imported proof, now already provided in Mathlib. No statement dispute.

## Unfinished work

None mathematically; required dry run and delivery results will be recorded below.

## Not duplicates

No new nodes were created. Existing blueprint lem-weil-pbc-proper-to-separated is the same triangle statement after renaming X,T; Y,B; W,Y, and is recorded in blueprint.same_as. Existing lem-weil-pbc-proper-over-separated is the same lemma with explicit universally-closed/finite-type consequences. I leave these existing nodes unchanged. Whole-DAG searches for IsProper.of_comp and 01W6 and whole-blueprint searches for proper-to-separated, proper-over-separated, proper separated, and separated target were checked before the leaf decision.

## Review by NJ

I checked delivery-errors B through E against the actual files. There are no new statement-only nodes, hidden clause nodes or duplicate nodes. The item's objects are arbitrary schemes; def-pc-scheme states the scheme notion, and def-weil-proper-morphism defines exactly separated and proper. Both definition node statements were read, and neither supplies a theorem being used without citation.

The final item has no proof steps: it is a Mathlib leaf, so C1/C4 step citations and long-step checks are vacuous, and citations.json is empty. Instead I checked the exact theorem statement, including its surrounding variables at Proper.lean:38 and its body at lines 124-125. With f:T → Y and g:Y → B, its two instance hypotheses are properness of f ≫ g and separatedness of g. The commutative-triangle equation rewrites the first to the given proper T → B. Its conclusion is properness of f and there are no noetherian, finite-presentation, quasi-compact-base, surjectivity or field assumptions. The proof uses Mathlib's morphism-property cancellation theorem; it contains no sorry.

The two notions of properness agree: Mathlib's IsProper is separated, universally closed and locally of finite type (Proper.lean:40-42); the source definition uses finite type, with quasi-compactness supplied by universally closedness as explained in the read definition node. This is the existing accepted Mathlib convention, not an extra hypothesis.

I checked small cases: g the identity gives the same proper map; T empty gives the proper empty map; f the identity yields an isomorphism and hence properness. No nonemptiness or surjectivity is needed. Dropping separatedness would fail, for example the chart section A¹_k → the affine line with doubled origin, over the usual A¹_k, is not closed: its image omits just the other origin and is a proper dense open; its composite to A¹_k is the proper identity, which confirms that the theorem keeps the necessary relative separatedness assumption. The preserved statement assumes it.

All four requested search services were actually run through msearch.py and their returned hits read. The first grep had zero hits because its regex omitted the qualified declaration name; the second located the line but its single-file output lost the filename in the wrapper's parsing; the final directory grep returned the exact full file and line. The two semantic searches also returned a newer name of_comp_of_isSeparated, which I did not choose because the pinned source spells the declaration of_comp. No unavailable search is represented as a negative result. Only the supplied sandbox was written; no Lean or build command was run.

## Delivery checks

First dry run exited with one metadata failure: proof_origin was null, which the preflight rejects even for this existing item converted to a leaf. I set its documentary origin to the local Stacks Tag 01W6(2), naming the exact Mathlib implementation and lines as well. No mathematical change was needed.
