# Stage-1 worker report: lem-sfb-regular-point-blowup-functions

Group Q16, 2026-10-22. Direct delivery; the worker performed the required self-review.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-regular-point-blowup-functions.json: split statement; eleven proof steps, using existing nodes only. Statement, statement dependencies, original source, and inherited blueprint ancestry retained.
- citations.json: one verbatim statement quotation for each node cited by each proof step.
- searches.jsonl: actual Mathlib search records produced by msearch.py. The item's original Q07 searches are retained in its JSON, and the new Q16 searches are appended.
- report.md: this report. write_split.py is a sandbox-only reproducibility helper.

New nodes: 0. New Mathlib leaves: 0. No Lean files written or compiled, no repository or launcher files changed, and no direct git commands run.

## Attachments

None. Searched the project Lean source for the exact blueprint tag and for blowup/function/structure-pushforward terminology. Existing blowup chart, invertible-centre, complement and flat-base-change declarations provide tools but do not state this entire regular-functions assertion. The source's declarations containing sorry were not treated as proofs.

## WANTED

None. All sources needed for the argument are present in literature/stacks-project/.

## Findings and changes

The item had a valid statement and a source description, but no proof. There was no earlier sandbox node or report to resume. I kept the statement exactly, including the nonempty-fibre hypothesis. The proof of Stacks 0AGS gives the local answer at n=0, but directly introducing a new local-functions lemma would move almost all the item into that node. Instead the split proves the local calculation explicitly using the two chart subalgebras and existing regular-sequence lemmas. This argument is marked proof_origin.by = agent: it is an alternative proof of the local assertion, not a transcription of the descending-twist-cohomology proof in 0AGS.

The affine localization and basic-open stalk argument identifies the actual canonical coefficient map, not an abstract isomorphism of two rings. This is needed by the point-blowdown factorization parent. For dimension one, the single-chart calculation uses the principal maximal ideal directly and needs no separate DVR node. For dimension zero, the blowup is empty and contradicts the fibre hypothesis. No statement dispute was found.

The two levels fixed above the node were read: the six-functor chapter and the ctf-stability unit. This is a local geometric prerequisite below the stable-curve/alteration branch, not a replacement of that branch. Generic off-unit tools are declared in split_report.tool_uses where required. blueprint_refs.py ancestor reports from.node = None for this already-created chain; I retained that inherited null ancestor and the full specific place and via chain rather than inventing an imported ancestor.

## Mathlib and duplicate checks

I searched the whole DAG and imported blueprint for blowup, regular functions, Hartogs, the relevant local-algebra facts, and the tags 0AGS, 02KH, 00PD and 07DV. In particular, the existing regular-local-generators-regular-sequence and regular-sequence-powers nodes already state the precise algebra used by the chart calculation. The existing flat-base-change-cohom node states the general qcqs morphism version, avoiding any unjustified affineness of the blown-up preimage. All these nodes are reused; no candidate new node remains.

Actual msearch.py queries for the item include leanfinder with both a sheaf-pushforward formulation and a two-dimensional-local-ring/global-functions formulation, loogle for AlgebraicGeometry and blowup, Mathlib grep for blowup/blowing and for birational/normal-pushforward terminology, and leansearch for the regular-surface formulation. Read hits describe localizations, stalks, basic-open rings and definitions of birationality. None proves the blowup assertion. No unavailable query was reported as a negative result, and no unrun query was recorded.

## Not duplicates

No new nodes are proposed. All intermediate non-elementary tools were found in the existing DAG.

## Review by Q16

I read the actual statement and proof of resolve.tex, Tag 0AGS (lemma-cohomology-of-blowup), including clause (4) and its descending-induction proof. I also read divisors.tex Tags 0804 (lemma-blowing-up-affine), 0805 (lemma-flat-base-change-blowing-up), 02NS (lemma-blowing-up-projective), and 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), coherent.tex Tag 02KH (lemma-flat-base-change-cohomology), and algebra.tex Tags 00NP (lemma-regular-domain), 00NQ (lemma-regular-ring-CM) and 07DV (lemma-regular-sequence-powers). No new node needs a separate source review.

For step 1, I opened the regular-scheme definition and the global blowup, gluing and local-model statements. They identify the affine construction; the cover-independence statement supplies the isomorphism over the base when the affine cover is refined. The Noetherian-ring definition gives finite generation of the centre ideal. The proper-blowup statement applies to that finite ideal. The proper and finite-type definitions give separatedness and quasi-compactness, and the separated-implies-quasi-separated statement gives the remaining hypothesis. I did not assume the whole scheme T separated.

For step 2, the localization-flat statement applies to any multiplicative set and the affine flatness criterion passes from rings to schemes. The cited flat-base-change-cohom statement explicitly allows any qcqs morphism and any flat base map, so it applies to this non-affine Y and to both R_h and R_p. The structure module is quasi-coherent by its rank-one affine description. I wrote the comparison on elementary tensors, its ring structure, and its compatibility with coefficients and subsequent localization; these make the later stalk identification the canonical map.

For step 3, I checked that the basic-open statement gives the neighbourhood basis, and separately cited principal-localization-open-immersion for the scheme identification Spec(R_h) = D(h). A topological homeomorphism alone would not have sufficed for that use. The module-stalk statement gives representatives and equality after shrinking, and the affine-open-stalk theorem gives the coefficient localization R_p = O_T,x. The displayed fraction argument proves both surjectivity and injectivity of the resulting stalk identification and identifies beta_x.

For step 4, I read both the definition of bc_g and the flat-blowup-base-change statement. The latter alone refers to a constructed map, so the definition is cited too. Its extended ideal is pA, and its map is over Spec A. The definition puts the new base first in the fibre product; the proof explicitly accounts for the factor exchange. Hence the comparison preserves the coefficient map used in step 3.

For step 5, the regular-scheme statement supplies regular localness and the regular-local-domain statement supplies the domain property. I checked the dimension bound using strict prime chains, their contractions from localization, the cited prime/irreducible-closed-set statement, and closure in T. This does not require pure dimension, irreducibility or excellence.

For step 6, the regular-local definition provides zero or one maximal-ideal generators. The regular-parameters statement supplies the nonzerodivisor in dimension one. The chart-cover statement applies also to the single generator 0; its chart ring is a subalgebra of A_0 = 0, so this is an empty spectrum. The fibre comparison is a direct associativity computation with the same residue field. In dimension one, every generator of the chart subalgebra equals a coefficient and the coefficient map is injective, so the whole single-chart blowup is Spec A.

For step 7, the existing regular-parameters theorem says exactly that a minimal pair generating the maximal ideal is a regular sequence. I checked that neither parameter is zero and that the quotients required in the regular-sequence definition are nonzero. The chart-cover and chart-ring statements provide two charts as subalgebras of A_s and A_t. No extra quotient-ring-presentation theorem is being assumed.

For step 8, I opened the affine-Proj, Rees, chart-map, chart-isomorphism, homogeneous-away-to-chart and degree-zero-localization statements. In particular the homogeneous-away-to-chart definition says verbatim that xT^n/(aT)^n maps to x/a^n. This is what identifies the ratios and their restrictions; the step explicitly writes the maps from the overlap rings to A_st. Thus equality of the two restrictions of a global section implies the fraction equality actually used in step 9, without assuming an unwritten description of global functions.

For step 9, the powers lemma applies with module A and positive exponents r,q; the regular-sequence definition then says precisely that t^q acts injectively on A/(s^r). Denominators can always be enlarged to make the exponents positive. Domain cancellation is available from step 5, so equality in the localization gives an equality in A. The proof writes the resulting divisibility a = s^r e and b = t^q e, and uses the chart subalgebra inclusions to conclude equality in the actual chart rings.

For step 10, the cited ringed-space statement includes that the structure ring is a sheaf. Uniqueness on the two-chart cover gives surjectivity from the two coefficient equalities. Injectivity follows from the explicitly injective map A to A_s; it is not inferred merely from the existence of an abstract isomorphism. For step 11, the complement theorem gives the coefficient isomorphism away from the centre, and the stalk statement gives the local representatives and equality-after-shrinking used in the written inverse-gluing proof. The locally-ringed-space-morphism statement gives the restriction naturality. This proves the sheaf isomorphism and every open-section assertion simultaneously.

I tested the edge cases on a field (zero-dimensional blowup empty, explicitly excluded), a DVR (one-chart identity), a two-dimensional regular local ring such as k[s,t] localized at (s,t), exponent-zero fractions (enlarged before the powers theorem), and disconnected or nonseparated regular schemes (the proof remains local on the target). The argument uses a reduced centre, not an arbitrary thickening of the point, and requires neither excellence nor an algebraically closed residue field. I corrected the source tags for properness and for the complement lemma while checking the tags table. I also added the explicit theta_a formula and the principal-localization open-immersion citation after checking what their shorter companion statements did and did not say.

Against delivery-errors B--E: no new unsplit nodes, no hollow notions, no duplicate or clause-restatement helper; every non-elementary input is an existing cited statement, not its proof; no per-degree derived comparison is involved; the item statement is unchanged; and every proof step has a source, a Boolean elementary flag and a matching quotation. All eleven proof steps are under 2000 characters, and none hides an uncited lemma: the overlap and final stalk arguments are written out, while the regular-sequence powers argument cites its existing node. The server review_split preliminary check passed. The required full dry run and delivery follow this signed review.

## Unfinished work

No mathematical part of this split remains unfinished. Existing cited unsplit tools remain independent stage-1 items; this delivery does not claim to prove those nodes or to compile a Lean proof.
