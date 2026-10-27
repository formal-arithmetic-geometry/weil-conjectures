# Worker report

Item: lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer. Group Q07. Stage 1 only, direct delivery, 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer.json: split into nine proof steps; statement and statement dependencies preserved.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-descent-flat-monomorphism-subset.json: statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-flat-monomorphism-quasiaffine-neighbourhood.json: statement-only lemma, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- dag/nodes/sec-six-functors-basics/lem-sfb-localization-spectrum-flat-monomorphism.json: Mathlib leaf, no proof. The monomorphism clause uses AlgebraicGeometry.IsPreimmersion.of_isLocalization (Preimmersion.lean:93), with the Mono instance (:65). Flatness uses Flat.SpecMap_iff (Flat.lean:67), RingHom.flat_algebraMap_iff (RingHom/Flat.lean:31), and IsLocalization.flat (Flat/Localization.lean:37).
- citations.json: verbatim statement excerpts for each of the 26 step/node citations. Searches are retained as produced in searches.jsonl. Scratch scripts and the DAG statement index are sandbox-only aids, not delivery files.

## Attachments

None. Searched the live project Lean source under lean/WeilConjectures both for the item and blueprint docstring tag and for integral/affine-neighbourhood, semilocalization, admissible-subset and flat-monomorphism terminology. No project declaration gives this equivalence with all its hypotheses and clauses. Existing project declarations of unrelated integral-fibre results do not attach this item. Mathlib localization declarations are recorded only as a Mathlib leaf.

## Literature requested

WANTED: literature/anantharaman-groupes-dimension-un.pdf, Proposition 4.1.3 (OCR 4.1.5), printed p.55, for lem-sfb-integral-finite-fibre-affine-neighbourhood-transfer. Primary statement read at https://www.numdam.org/article/MSMF_1973__33__5_0.pdf .

WANTED: literature/raynaud-critere-effectivite-descente.pdf, Un critère d'effectivité de descente, §1 Proposition 1.2 and Corollary 1.3, §3 Theorem 3.3, Proposition 3.4 and Corollary 3.8, printed pp.2,12–15, for the item and the two new Raynaud lemmas. Primary scan read at https://www.numdam.org/article/SAC_1967-1968__2__A5_0.pdf . No PDF was downloaded or written into the repository. Because this archive is absent, proof_origin.by is agent. The construction, subset equality and final principal open are written out rather than left to the external document.

## Faults and scope

The imported statement is correct as stated; no STATEMENT-DISPUTED repair was needed. The imported source's Raynaud “5.8” is an OCR error: the corresponding corollary is 3.8, printed p.15. The scan's theorem/proposition heading OCR also gives 3.4/3.5 where the subsequent cross-references give 3.3/3.4. Both the printed page and the actual assertion are recorded to remove ambiguity. The item's maintainer-owned source field is preserved.

The latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, step (3). This is the inherited trait/group descent support branch of that direct-image argument, not a replacement route for the target. tools/blueprint_refs.py ancestor returns None for the item. I retained its null from.node and full inherited via chain and prepended the item for each new node. Place fields identify the precise inherited finite-set affine-neighbourhood branch. Whole-blueprint searches found no equivalent node, so same_as is empty.

The only off-unit non-Mathlib statement tool is lem-weil-pbc-surjective-universally-closed-affine-target (Stacks 05YU): it supplies affine descent for F′→F, as a generic theorem. It does not supply finite-set neighbourhood transfer and does not replace the unit route. It is declared in split_report.tool_uses. The other cross-unit results used here are existing definitions or Mathlib leaves.

## Not duplicates

lem-sfb-integral-descent-flat-monomorphism-subset vs lem-per-flat-monomorphism-local-structure: the existing node describes a given quasi-compact flat monomorphism (stalks, fibres, Noetherianity); it does not descend the existence of one along an integral surjection or supply the cartesian square.

lem-sfb-flat-monomorphism-quasiaffine-neighbourhood vs lem-sfb-quasiaffine-affine-basic-open-criterion: the existing criterion describes quasi-affineness of a given scheme via its global principal opens; it does not extend the image of a flat monomorphism to an open neighbourhood in its target.

lem-sfb-localization-spectrum-flat-monomorphism vs lem-weil-pbc-localization-spectrum-embedding: the existing node gives the underlying topological embedding and primes in its image; it states neither stalkwise flatness nor the categorical monomorphism property.

lem-sfb-localization-spectrum-flat-monomorphism vs lem-weil-pbc-localization-module-exact: exactness of localization on modules is algebraic; the new Mathlib leaf records the geometric map's flatness and monomorphism for arbitrary test schemes, not an exactness assertion.

Before creating these nodes I searched the whole DAG for admissible subset, pro-open, flat monomorphism, quasi-affine neighbourhood, localization, and the candidate declaration names; the full statement index was read to distinguish actual statements from metadata hits. Whole-blueprint searches included affine neighbourhood, integral surjective, finite set, semilocalization, admissible subset, flat monomorphism, quasi-affine neighbourhood, integral affine neighbourhood and localization flat monomorphism. Existing localization-spectrum embedding, prime avoidance, qcqs permanence, surjective base change and 05YU nodes are reused. No new node has the finite-set equivalence or one of its two implications as its statement.

## Review by Q07

I read Anantharaman's printed p.55 statement and Raynaud's Corollary 3.8 on printed p.15 against the item: the source allows an integral surjection, only set-theoretically finite fibres, and Noetherian local rings downstairs. The item's locally Noetherian hypothesis is sufficient; it does not require the source to be Noetherian or the cover to be finite or flat. The empty set is treated separately using Spec(0). I read Raynaud's admissibility definition, Proposition 1.2/Corollary 1.3, Theorem 3.3 case (ii), and Proposition 3.4. The new descent node is about arbitrary subsets and supplies the cartesian comparison used later; the new neighbourhood node assumes a quasi-compact flat monomorphism, quasi-affine source, and quasi-separated target. It does not assume finite presentation. These are distinct prerequisites, not clauses renamed from the item. The new localization leaf was checked against the actual Mathlib source lines listed above; the match has no finite-type or Noetherian requirement and permits the zero localization.

For each step I opened the cited existing node's statement, not only its dependency list:

1. The definition of integral includes affine; affine-morphism permanence gives an affine inverse image of an affine target. The spectrum definition supplies the empty spectrum of the zero ring. This proves necessity without finite fibres.
2. The locally-Noetherian/quasi-separated leaf states exactly that affine intersections downstairs are quasi-compact. Affine permanence says an affine morphism is quasi-separated, and qcqs-morphism permanence (2) transfers this from Z to Y. Finiteness of E′ uses precisely the finite underlying fibres, not finite generation of the algebra.
3. Localization-spectrum embedding states that its image is the primes disjoint from S. Prime avoidance explicitly says an ideal contained in the finite union of the primes is contained in one. Applying it to the prime ideal r proves the claimed generalization locus in a few lines. There is no new “finite-point localization” node hiding this calculation.
4. The new Mathlib leaf gives both flatness and monomorphism. Open-immersion and flatness definitions show directly that composing with V→Y changes no stalk map and remains a monomorphism. Affine-scheme qcqs gives quasi-compactness of F′, and qcqs-morphism permanence (1) applies because step 2 established Y quasi-separated. No local-Noetherian claim about Y is used.
5. Integral/universally-closed equivalence gives closedness. The definition of universally closed includes the identity base change. Closedness applied to the closure of a singleton proves q⁻¹(H)=H′ in the written argument. Continuity proves the other inclusion. This argument needs neither going down nor flatness of q.
6. The new descent lemma is applied with the exact subset H and image equality from step 5. Its statement includes the isomorphism F′≅Y×_Z F; that comparison is not borrowed from its future proof. The Noetherian hypothesis is checked on Z, not on Y.
7. Surjective-base-change states surjectivity for arbitrary scheme base change. Integral/universally-closed plus its definition gives universal closedness of the projection, explicitly for each further T→F. The existing 05YU node assumes just affine source, surjectivity and universal closedness, all now available, so gives affineness of F. No normality or Noetherianity of F is needed in this stronger existing version.
8. The new neighbourhood node needs qc flat mono j (step 6), quasi-affine F (affine by step 7 and quasi-compact by the affine qcqs leaf), and quasi-separated Z (step 2). All three are checked. Its conclusion gives an actual open subscheme with the requisite quasi-affine presentation.
9. In that presentation the complement is V(J) by the Zariski topology. Prime avoidance provides one element of J avoiding all marked primes. Clause (0) of affine-ideals-closed-subscheme, applied to the whole affine scheme Spec B, says this principal open is affine. Transport across the presentation is an isomorphism of open subschemes. This uses no false assertion that all finite sets in arbitrary schemes have affine neighbourhoods.

I tested the new statements on H empty/full, the identity integral cover, and Spec of a field. Empty H gives the empty flat monomorphism and cartesian empty square; full H gives the identity. The neighbourhood lemma with X empty admits the empty quasi-affine open, and with f the identity asserts only quasi-affineness already hypothesized. For localization I checked S={1} (identity), 0∈S and the zero ring (empty spectrum), and comparable marked primes: redundant primes do not change the localization image, so no incomparability hypothesis was silently used. Nonreduced schemes cause no reduction step; all structure sheaves remain their given sheaves. A nonfinite integral cover is used only via affineness/closedness/descent, so the proof does not smuggle in finite presentation.

B1–B10: both unsplit nodes have empty proof/dependency fields, complete object introductions, inline meanings of monomorphism/quasi-affine, definition dependencies, single-backslash TeX, precise source locations, real logged searches, and filled blueprint metadata. The Mathlib leaf records one declaration per clause and the lines read. C1–C8: every non-elementary assertion is a cited node; citations.json contains verbatim text, and the generic 05YU tool is declared. D1–D5: the item constructs the localization, proves the subset equality and constructs the final affine open; no new node merely repeats its conclusion. E1–E7: hypotheses were checked step by step above. I replaced an initially considered separate semilocalization lemma by the short prime-avoidance calculation, and used the existing stronger 05YU node instead of adding another Chevalley lemma. Every step is below 2000 characters; no long step contains an unrecorded comparison lemma.

## Unfinished work

No stage-1 mathematical part remains. The two new unsplit prerequisites are intentionally statements only for subsequent workers. No Lean was written and no compiler, Lake or build tool was run. The first dry run found two metadata errors: a grouped definition citation was not recognized and the Mathlib match lacked its explicit line field. I changed the new statements to individual bracketed citations and added line 93, re-read all five Mathlib declaration locations, and regenerated the affected verbatim citation quotes. The initial server review_split check passed. The complete delivery preflight is rerun after these corrections.
