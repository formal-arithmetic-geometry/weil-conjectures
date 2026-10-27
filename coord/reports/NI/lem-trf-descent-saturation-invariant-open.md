# Stage-1 delivery: lem-trf-descent-saturation-invariant-open

## Files written

- dag/nodes/sec-trace-formula/lem-trf-descent-saturation-invariant-open.json: statement, split; no Mathlib match for the whole item. Statement, statement dependencies, source and blueprint ancestry unchanged.
- citations.json: twelve step/node entries, each quoting the cited node's statement verbatim.
- report.md and searches.jsonl: review and actual search log.

New nodes: 0. New Mathlib leaves: 0. All helpers already exist.

## Attachments

None for the item. CategoryTheory.Over.DescentDatum.descent_orbit_saturated already belongs to lem-pd-descent-orbit-saturated, at lean/WeilConjectures/AlgebraicGeometry/DescentOrbitSaturated.lean:39. Its statement has no finite-cover restriction and its proof contains no sorry. This is a proper helper, not an attachment for the entire item. The nearby exists_descent_norm_affine_shrinking has a finite-cover hypothesis and does not state this item.

## WANTED

None.

## Findings and corrections

The imported statement is correct; no statement dispute or correction is required. The missing proof is now explicit. In particular one must not argue as if scheme fibre products were set-theoretic fibre products. The image identity is justified by the existing lem-weil-pbc-base-change-image, and orbit saturation is taken from its existing theorem about all scheme points. No separatedness, local quasi-finiteness or quasi-compactness of V is used. Openness of W is assumed, so proving universal openness of p is unnecessary.

The existing helper lem-pd-descent-orbit-saturated has an inaccurate parenthetical source reference: Tag 0H8K is groupoids-lemma-descend-along-finite-with-bound, whereas the cartesian-groupoid/descent equivalence is Tag 0APF, groupoids-lemma-cartesian-equivalent-descent-datum. I read the latter and Tag 03JE in groupoids.tex. This delivery relies on the helper's explicit statement and existing proof, not on the mislabelled reference, and does not edit that other node.

The generic open-factorization helper was found in the DAG after the searches returned IsOpenImmersion.lift, lift_fac and lift_uniq. It is reused as lem-weil-pbc-morphism-factors-through-open-subscheme; no redundant leaf is introduced. Whole-blueprint searches for saturation, invariant, open immersion, factors uniquely, lift and factor through found no blueprint node that already states this item. DAG keyword, tag and declaration searches were also made across all chapters. The mathematical claim is not an existing open-image descent theorem: lem-trf-invariant-open-image-pullback assumes an invariant open under a canonical effective datum, while this item establishes invariance under an arbitrary given datum before any effective model exists.

## Not duplicates

No new-node/existing-node pairs: no new nodes are created. In particular the existing orbit, open-factorization, base-change-image, base-change-open-immersion and monomorphism nodes are cited directly.

## Review by NI

I read Stacks Tag 02W8 in more-morphisms.tex, label lemma-separated-locally-quasi-finite-morphisms-fppf-descend, especially the second paragraph defining W and asserting its invariance by the cocycle. The chapter and unit records and the item's retained blueprint ancestry were checked: this is the geometric quotient-presentation support below lem-trf-local-term-locality, not a replacement of the local-term unit's route. No new node needs a separate source review. I read the statements of every node in proof_deps, including the current blueprint_update of def-pd-descent-datum. The updated definition has the same cocycle convention used here.

For step 1, def-pc-fibre-product supplies the universal pair (z,b), and def-pd-descent-datum supplies the isomorphism and cocycle. I explicitly derived diagonal identity and reversed transport by cancelling the invertible diagonal map; these were not assumed as extra hypotheses. Naturality is composition with that universal pair. This checks that the transport datum required by the orbit helper is the datum actually given in the item.

For step 2, def-pc-fibre-product identifies the square for C times A as a pullback over V. The statement of lem-weil-pbc-base-change-image gives the image of the pullback projection for every subset, including the full underlying set of C. Thus its image really is s inverse of C, even at nonclosed points with different residue fields. I read the proof of Tag 01S1, lemma-base-change-surjective, and Mathlib PullbackCarrier.lean:420; neither assumes flatness or rational points. Decomposing C as a union of singleton subsets then gives W as a union of O_c by elementary image/preimage membership.

For step 3, the statement of lem-pd-descent-orbit-saturated gives precisely s inverse O_c = t inverse O_c, not merely a statement about a fixed rational fibre. I read its whole project proof and its signature in DescentOrbitSaturated.lean. Its hypotheses are a scheme map, a scheme over its source, a transport descent datum, and the displayed defining pullback and universal target. Step 1 supplies these with X=A, Y=B; there is no finite, flat, surjective, closed-point or quasi-compact hypothesis. The written membership argument proves the union is invariant; it is not outsourced to a new node restating the item's clause. This is a generic tool from another unit, declared in split_report.tool_uses.

For step 4, the statement of lem-weil-pbc-open-immersion-base-change makes both j_0 and j_1 open immersions, with pullback identifications checked by their universal pairs. The base-change-image node identifies their underlying images as the indicated preimages of W. Invariance then proves both image-containment hypotheses for phi and phi inverse. The statement of lem-weil-pbc-morphism-factors-through-open-subscheme supplies exactly existence and uniqueness of the two factorizations. I read Schemes Tag 01HI, lemma-restrict-map-to-opens, and Mathlib OpenImmersion.lean:701, 705, 708. These are actual scheme morphisms, so the proof does not infer factorization through an arbitrary immersion from an image inclusion.

For step 5, the statement of lem-weil-pbc-open-immersion-monomorphism permits cancellation of j_0, j_1 and iota. I read Schemes Tag 01L7, lemma-immersions-monomorphisms. The composites with the inclusions reduce the proposed inverse identities to phi inverse phi = 1. Composing the defining restriction equation with (v,b), then projecting to V, is the exact transport compatibility required in the item, not an unspecified identification. Applying that equality twice and then the original cocycle gives the restricted cocycle after cancellation of iota; the universal test scheme proves equality of scheme maps. def-pc-fibre-product supplies the final equality from the projections. All compatibility arguments are written out in the proof.

I tested C empty, W empty and V empty: unions and inverse images are empty, and the unique restricted maps satisfy all identities. For identity p the saturation is C and the datum is identity, as expected. A disjoint-union covering with a datum exchanging copies produces the union of the corresponding opens, exactly the invariant union used here. The orbit theorem explicitly handles nonclosed and inseparable points. I checked B1-B10, C1-C8, D1-D5 and E1-E7 against the statements and sources: there are no new-node form issues, no cited hidden proof constructions, no unsupplied non-elementary fact, no restatement node and no changed hypothesis. The five steps have lengths 576, 456, 545, 761 and 1043 characters, so none exceeds the 2000-character long-step threshold. The restriction and cancellation steps are short applications of the cited universal properties, not hidden separate lemmas.

The logged whole-item searches return cover restriction, gluing and pseudofunctor descent definitions, which do not give arbitrary scheme saturation invariance. The second phrasing was also searched. The open-factorization searches found an exact helper match, checked at source and reused from the DAG. Older searches already in the imported item remain intact; only searches actually run in this sandbox were appended. No Lean file, compiler, Lake, local DAG checker, repository git command, or launcher edit was used.

## Unfinished work

None in the one-level split. The required server dry run and direct delivery follow this report.
