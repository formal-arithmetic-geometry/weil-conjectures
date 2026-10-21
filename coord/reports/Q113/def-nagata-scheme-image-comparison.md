# Stage-1 report: def-nagata-scheme-image-comparison

## Files written

- dag/nodes/sec-nagata-compactification/def-nagata-scheme-image-comparison.json — definition; Mathlib leaf, AlgebraicGeometry.IsClosedImmersion.lift (ClosedImmersion.lean:210).
- citations.json — empty list: a definition/Mathlib leaf has no proof steps or proof-step node citations.
- report.md — this report. searches.jsonl is the unmodified search command log.

New nodes: 0. Mathlib leaves in this delivery: 1 (the item).

## Attachments

None. Searched WeilConjectures/ for the exact blueprint id, schemeTheoreticImage, scheme_theoretic_image, and closed-immersion lifting/image language. The project has compatibility and containment lemmas in WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:149,157, but neither is the definition of the comparison map. The construction itself is in Mathlib, so this is a leaf delivery rather than ATTACH.

## WANTED

None.

## Corrections and source observations

The original definition is valid. Its implicit g and its ideal language are made explicit; the meaning and hypotheses are unchanged. Read the current main-20261015 definition (order 78), the imported chapter/unit records, and the image definition's current statement and blueprint_update. At the first delivery only blueprint_update carried the corrected kernel meaning; the current reviewed statement now carries that correction itself. It defines the largest quasi-coherent ideal contained in the sheaf kernel for arbitrary g, and its associated closed subscheme and inclusion. The comparison now explicitly cites that current statement and names its structure-sheaf kernel map. No quasi-compactness hypothesis is added. The other node is read-only and was not changed.

Removed statement dependencies on scheme-theoretic closure, the canonical factor map, the quasi-compact image interface theorem and the closed-immersion image theorem: they are implementation details of Mathlib's lift or are unused by this definition. Retained the scheme, closed-immersion, and image definition nodes. No theorem asserting uniqueness or that the map is a closed immersion is added to this definition; those are the separate existing universal-property item.

## Not duplicates

No new nodes. Searched the whole DAG for IsClosedImmersion.lift and comparison language and the whole blueprint with blueprint_refs.py (scheme image comparison; Comparison map; closed factorization), and ran ancestor. No other blueprint node defines the same datum. The existing lemma-nagata-scheme-image-universal states properties of this map and depends on it. The existing lem-weil-pbc-closed-immersion-factor-ideal-inclusion is a more general theorem about existence and closedness, not a second definition. No node is created for the elementary containment or for any Mathlib implementation step.

## Review by Q113

I read the item's defining paragraph in both blueprint snapshots and checked it against Stacks morphisms.tex, Tag 01R6 (morphisms-lemma-scheme-theoretic-image) and Tag 01R7 (morphisms-definition-scheme-theoretic-image). Tag 01R6 explicitly treats the non-quasi-coherent sheaf kernel by its largest quasi-coherent subideal, so the construction must not assume all morphisms have a quasi-coherent raw kernel.

There are no proof steps and no new nodes to audit under C1/C4. For the construction's hypotheses I read Mathlib ClosedImmersion.lean:203–218: lift accepts a closed immersion z, an arbitrary morphism k, and z.ker ≤ k.ker, and returns a morphism to the source of z. Taking k = g.imageι gives exactly SIm(g) → Z. I read IdealSheaf/Basic.lean:732: le_ker_comp h z states z.ker ≤ (h ≫ z).ker, without extra hypotheses. I read IdealSheaf/Subscheme.lean:576 and the image/imageι abbreviations at 662/665: the kernel of g.imageι is g.ker. Rewriting the supplied equality h ≫ z = g therefore provides the lift hypothesis in one line. I inspected the body of lift, which constructs the morphism through ideal inclusion, rather than choosing unspecified data. Its properties are handled by the separate universal-property node and are not smuggled into this definition.

I opened every retained statement dependency: def-pc-scheme provides schemes/morphisms; def-weil-closed-immersion provides the closed-immersion notion (already a reviewed Mathlib leaf); def-nagata-scheme-theoretic-image now provides the image and its quasi-coherent-kernel meaning directly in its reviewed statement (matching blueprint_update). I also opened every removed dependency to verify it was not required to state the definition. These are statement dependencies, not proof-step citations, so no quotations are required in citations.json.

Edge cases: if z is the identity, the containment is 0 ≤ ker(g), and the comparison is the image inclusion; if g itself is a closed immersion and h is the identity, the comparison identifies its image with its source. If T is empty, ker(g) is the unit ideal and SIm(g) is empty, giving the unique empty-source map to Z. Affine test: for A → B factoring through A/I, I is contained in ker(A → B), and the quotient homomorphism A/I → A/ker(A → B) induces precisely SIm(g) → Z (the correct direction). Nonreduced schemes cause no change because containment is scheme-theoretic, not set-theoretic. Arbitrary non-quasi-compact g is covered by Mathlib's general kernel, as the source intends.

Checked delivery-errors B–E: no new statement-only obligations, no duplicate or restatement nodes, no invented searches, no claims moved into definitions, no theorem used for hypotheses it lacks, no circular citation, and no long non-elementary proof step. All four requested search services ran successfully; their exact queries and results are retained. Nothing was compiled and no repository or launcher file was written.

## Repair of returned delivery

The return identifies reviewed branch head a7ef8f18ea and a landing refusal caused by the changed statement of def-nagata-scheme-theoretic-image. I compared the retained item with the live item: the live item remains imported, so the retained leaf construction and its search records remain applicable. The delivery command builds on current origin/sheaf-dag and preserves current maintainer-owned metadata.

I re-read every retained statement dependency in the current DAG. In particular, def-nagata-scheme-theoretic-image now states verbatim: “Its *kernel ideal*” followed by “$\ker(g)\subseteq\mathcal O_Y$ is the largest quasi-coherent ideal” and “contained in the kernel of $\mathcal O_Y\to g_*\mathcal O_T$”. It then defines SIm(g) as the closed subscheme defined by that ideal and supplies its inclusion. This is exactly the datum used here; neither density nor restriction to opens nor any assertion about the raw sheaf kernel is needed. The item's last sentences now explicitly identify that structure-sheaf map and the closed subscheme inclusion, instead of relying on the earlier report's blueprint_update-only justification.

Under Review by Q113 I reaffirm the source checks for this repair: Stacks Tags 01R6/01R7 and the current blueprint defining paragraph agree with this interpretation. Mathlib Hom.le_ker_comp h z supplies the containment for any factorization h ≫ z = g; ker_subschemeι identifies the kernel of the inclusion of the closed subscheme defined by g.ker with g.ker. Thus IsClosedImmersion.lift has exactly the required hypothesis. These source lines were re-read during this repair. The other two dependencies still supply schemes/morphisms and closed immersions. There are no proof-step citations to re-quote; citations.json correctly remains empty. Identity, empty-source, affine-quotient direction and non-quasi-compact cases remain as checked above. No mathematical statement, search question, or Mathlib query changed, so all five logged searches are reused after reading their actual hits; none is invented or repeated.

The initial required dry run on the retained files exited successfully at fe1c93b2a3c before edits. The repaired node also passed the server preflight at 455d8d06fc9. The final report, including corrected literal TeX quoting, receives a final dry run before pushing.

## Unfinished work

None in the mathematical split. Final server validation and direct delivery follow.
