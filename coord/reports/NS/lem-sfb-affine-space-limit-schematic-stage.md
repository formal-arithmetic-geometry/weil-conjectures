# NS stage-1 report: lem-sfb-affine-space-limit-schematic-stage

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-affine-space-limit-schematic-stage.json: statement, split by reusing the existing stronger node; Mathlib verdict no match.
- citations.json: one verbatim statement excerpt for each step/node citation.
- report.md: this report.

No new DAG nodes and no Mathlib leaves. The statement, statement dependencies, created provenance and imported fields are unchanged. The sandbox initially held only dispatcher markers; there was no earlier proof/report to resume. Existing 2026-10-22 Mathlib search records were retained. The additional searches were actually run using msearch.py and logged in searches.jsonl.

## Attachments

None. Searched WeilConjectures for the blueprint tag and for algebraic-space/schematic-limit terminology. The affineSpaceMap declaration in DeformationSpace/Coordinates is about affine n-space, not algebraic spaces becoming schemes. No project declaration stating the item was found. The broader search of Sheaf showed its algebraic-space infrastructure, not a completed project proof of this assertion.

## WANTED

None.

## What needed correction

The item was statement-only. A whole-DAG search found lem-sfb-space-affine-limits-schematic-stages, an existing stronger statement including exactly the needed schematic-stage assertion as well as existence of the sheaf limit, affine projections, the affine-stage assertion, and base-change compatibility. Creating nodes for Tags 07SF or 07SQ here would duplicate it. I reused this node and left its own statement-only proof task untouched. There is no cycle: that node currently has no proof dependencies and only the scheme/algebraic-space definition statement dependencies.

The current latest blueprint (main-20261023-1620) sk-thm-sf-ctf-stability unit and direct-images proof were read. Its proof (3) assembles proper direct image and quasi-compact-open direct image through a compactification. The long inherited provenance describes an earlier supporting alteration/curve-moduli branch; this low-level tool delivery does not change that route or a target. The ancestor tool reports blueprint.from.node = None for this inherited chain. I preserved that existing null provenance rather than inventing a blueprint import, and filled the split report with the current source relation. Whole-blueprint searches for “algebraic space”, “affine limit” and “schematic” found no blueprint statement of this algebraic-space theorem. No statement dispute was found.

## Unfinished work

None for this one-level split. The reused stronger limit node remains an existing unsplit prerequisite, as permitted for a one-level DAG delivery. No compiler, Lake, Lean-writing or repository git command was run.

## Not duplicates

No new nodes. The item is a special case of the pre-existing lem-sfb-space-affine-limits-schematic-stages, which is cited instead of reproduced in a new node. The scheme-only limits in Mathlib cannot replace an algebraic-space-stage assertion.

## Review by NS

I read Stacks spaces-limits.tex, Situation 084R (situation-descent), Tag 07SF (lemma-directed-inverse-system-has-limit), and Tag 07SR (lemma-limit-is-scheme), including its finite affine-open-cover argument via Tag 0827 and Tag 07SQ. I also read Tag 07SQ's statement and surrounding proof. These are the exact small nonempty directed, qcqs, affine-transition hypotheses in the item; the base scheme is arbitrary. I read spaces-properties.tex's absolute diagonal definition and the schematic-locus/gluing discussion. The statement does not need separatedness, finite presentation, a Noetherian base, or surjective transitions.

For step 1 I opened the full statement of lem-a1-space-etale-open-image. Its final sentence explicitly equates topological quasi-compactness with a surjective etale atlas from a quasi-compact scheme, so it provides the precise convention change required. I opened the full statement of lem-sfb-space-affine-limits-schematic-stages: its chart definition of quasi-compactness, diagonal/test definition of quasi-separatedness and representable-test definition of affine morphisms agree with the hypotheses after this change. No theorem is inferred from a definition node. This is a generic off-unit atlas tool, declared in split_report.tool_uses with its limited purpose.

For step 2 the stronger node explicitly says that the fppf-sheaf limit is an algebraic space. The remaining argument is the universal property: maps into the pointwise sheaf limit are component natural transformations; the given limit property of Z constructs the two comparison maps; equality after every projection forces their composites to be identities. The proof writes these maps and equalities, so it does not hide a comparison theorem. No assumption that a categorical limit is already literally the chosen sheaf limit is made.

For step 3 the same existing node explicitly says that if all stages are qcqs and its limit is a scheme, some stage is a scheme. The representing scheme of Z represents the isomorphic sheaf limit L, so that clause applies with all hypotheses checked in the text. This is an application of a previously existing more general node, not movement of this item's proof into a newly named clause. There are no new nodes whose source statements or small cases need independent review.

I tested the empty-space case: the proof does not select a point or require a nonempty scheme, and the existing stage assertion includes the empty scheme. A singleton index reduces to invariance of representability under isomorphism. General transition maps need not be surjective, and none is used as such. The nonempty-index hypothesis is explicitly retained. The proof is over S throughout, so no relative-versus-absolute limit or change-of-base inference is suppressed.

Against delivery-errors B--E: the JSON statement retains correctly escaped TeX and self-contained hypotheses; no new nodes or unsupported notion definitions were introduced; all proof citations have excerpts copied verbatim from the statements, and every non-elementary input is one of those cited statements. The assembly has no new duplicate, restated clause, circular node or hidden induction. Each step is below 2000 characters. Mathlib searches used two semantic phrasings, Loogle, grep in Mathlib/AlgebraicGeometry and LeanSearch; I read the hits, including Scheme.exists_isAffine_of_isLimit at AffineTransitionLimit.lean:1040, whose stages are already schemes. It therefore is not a match for the item. No unavailable search was reported as a negative search.
