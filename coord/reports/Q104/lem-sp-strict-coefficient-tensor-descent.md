# Stage-1 delivery: lem-sp-strict-coefficient-tensor-descent

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-strict-coefficient-tensor-descent.json`: existing statement, split in eight steps using existing nodes only. Statement and statement dependencies unchanged. The Mathlib searches found no match for the whole strict varying-coefficient-system theorem.
- `citations.json`: all 17 step/node pairs, each quoting the cited statement verbatim.
- `report.md`: this report. The sandbox also retains the real search log and its item-specific writing script; these are not DAG nodes.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and item id and for strict coefficient, semilinear tower, tensor-system and descent terminology. The exact id/tag has no occurrence. Related results about fixed-coefficient towers, coefficient comparison presentations and exact-functor localization do not assert this full ordinary-derived strict varying-ring-system construction. In particular the site strictification refutation concerns a different finite-precoverage assertion. No sorry-containing declaration is claimed as an attachment.

## WANTED

None. All sources used are already present in the read-only repository.

## Defects corrected and route

The imported item had a complete intended statement but no proof. Its Construction paragraph in the current blueprint compresses three distinct points into “quasi-isomorphisms ... so this is functorial”: abelian componentwise detection for varying coefficient systems, existence of the exact derived functor, and uniqueness/naturality with respect to roofs. The split now supplies all three explicitly. The unit has no proof steps to replace: this is precisely the strict-complex construction within the reduction-tower node, not an alternative smooth-purity route. No SGA source is used.

No statement dispute was found. No hypotheses or conclusions were changed. The coefficient maps need neither flatness nor surjectivity. “Complex of R-modules” here means module sheaves on the given site, as the existing definition node explicitly states.

## Search record and duplicate check

Ran the mandated msearch command for the item with LeanFinder (two different formulations), Loogle, LeanSearch and source grep. The five new records are copied from `searches.jsonl`, preserving tool and query exactly. All services answered successfully. Read the resulting hits: `Functor.mapDerivedCategory` assumes an exact underived functor (ExactFunctor.lean lines 26--37), so cannot construct nonflat scalar extension. `Tor` and `Tor'` (Monoidal/Tor.lean lines 39--55) are homology-valued projective-resolution bifunctors, not this unbounded derived functor. Presheaf tensor and restriction infrastructure do not provide strict-system localization. Earlier Q92 search records on the live item were retained as inherited records, not claimed as searches run by Q104.

Searched all DAG node statements/titles for K-flat resolutions, quasi-isomorphism preservation, resolving subcategories, fraction localizations and strict tensors; searched tags 06YS, 06YT, 06YY, 0G7D and 06XN. Ran blueprint_refs ancestor and searches for K-flat, resolving, strict coefficient, tensor.*tower, K-flat.*resolution, and coefficient.*tensor. Reused lem-pc-kflat-resolution, lem-pur-derived-change-of-rings, lem-pur-left-derived-from-kflat-class, lem-trf-right-fraction-dense-subcategory, the quasi-isomorphism calculus node and the localization universal property. The fixed-R inverse-system augmentation node and scalar-tower realization node do not state varying-ring strict derived descent. No new node was necessary, so no new/existing same-tag pair needs a Not duplicates entry.

## Review by Q104

I read the current blueprint reduction statement and its full Construction paragraph, together with its normalized-tower unit and chapter. For the mathematical inputs I read Stacks sites-cohomology.tex Tag 06YS (lemma-K-flat-resolution), Tag 06YT (lemma-derived-tor-quasi-isomorphism-other-side), Tag 06YY (lemma-derived-base-change) and Tag 0G7D (lemma-factor-through-K-flat). I also read derived.tex Tag 06XN (lemma-find-existence-computes, dual part), Tag 0GSL (lemma-localization-subcategory and its refinement proof), Proposition 05SE (proposition-derived-functor) and Lemma 015F (lemma-right-derived-exact-functor). The proof origin is marked agent: Stacks treats one coefficient change, and the varying-ring strict-system assembly is written out here. No new-node source is required because there are no new nodes.

Step 1 uses exactly the statement of def-pc-sheaf-restrict-scalars (unchanged underlying abelian sheaf) and def-weil-abstract-derived-category (kernel/image cohomology and quasi-isomorphisms). Kernels and cokernels of a semilinear transition inherit the transition because scalar restriction leaves them unchanged; component inverses then prove the abelian and detection assertions. This is a direct construction, not an invocation of the fixed-category inverse-system lemma. I checked in particular that no exactness of extension of scalars is used.

Step 2 uses the sectionwise tensor and sheafification formula in def-pur-sheaf-tensor-product. The balanced relation is preserved by each R-algebra coefficient map; the chain and homotopy identities are written explicitly, including transition compatibility. These computations descend by sheafification. Step 3 uses that same additive tensor formula and the statement of lem-pur-homotopy-category-triangulated, which explicitly gives cone triangles and exactness of Q. Its block matrix verifies the signed projection as well as the differential, and establishes exactness on homotopy categories even for nonflat coefficients. Both are routine calculations, not new assignable lemmas.

Step 4 takes clause (1) from lem-pur-derived-change-of-rings: it is genuinely on an arbitrary ringed site, not just the one-point-site lemma lem-pc-kflat-tensor-quasi-iso. For every n its hypotheses are an R-algebra map and a quasi-isomorphism between K-flat R-complexes. Those are exactly the hypotheses here. Step 1 converts these levelwise conclusions to a strict-system quasi-isomorphism. I specifically avoided citing the narrower ring-only tensor result.

Step 5 takes the complete arbitrary-unbounded resolution statement from lem-pc-kflat-resolution, including flat terms, and the exact left-derivation statement from lem-pur-left-derived-from-kflat-class. The latter needs an exact functor from K(A) into a triangulated target, not an exact underived tensor functor. Step 3 proves the former, step 1 establishes that the target category is abelian, and step 4 supplies precisely its inversion hypothesis. I checked its comparison orientation LF(QP) -> G(P).

Step 6 reads the actual statements of lem-pur-quasi-isos-saturated-triangulated and lem-trf-right-fraction-dense-subcategory. The first supplies both Ore and cancellation axioms, not just two-out-of-three; the second requires a FULL subcategory and one denominator into every object, exactly the subcategory and the resolution of step 5. It makes no assumption of a functorial resolution. The natural-transformation clauses (2)--(3) of lem-weil-pbc-localization-universal-property give uniqueness compatible with normalization, which the mere uniqueness of a derived Kan extension would not alone establish for an arbitrary normalized lift. The displayed roof formula records the comparison on actual derived morphisms. All localizations are taken in a common larger universe.

Step 7 uses lem-sf-exact-functor-derived-triangulated only for the exact evaluation functors proved in step 1. Clause (2) of lem-pur-derived-change-of-rings explicitly gives canonical K-flat computation of the single-level functor. The universal property then extends that natural comparison from resolving objects; no commutation of arbitrary functors with a Kan extension is assumed. Step 8 uses the unchanged-underlying-sheaf definition to verify exactness of scalar restriction and the same localization natural-transformation clauses. The q_n formula is already a strict chain map from step 2, so its composite-index formula is proved before localization, rather than inferred from unrelated derived level objects.

Every cited statement was read; citations.json quotes the whole statement so its requested clause can be checked without a paraphrase. The non-elementary sources are represented by existing cited nodes, and each off-unit generic tool is declared in split_report.tool_uses. Those tools serve the Construction argument, not a substitute unit route. Traversed their statement and proof dependency closures to check that none returns to this item. No proof step is longer than 2000 characters.

Small cases: on the empty/zero module category the formulas are the unique zero functors. With identity coefficient maps the transitions are identities. Arbitrary nonsurjective maps still preserve the balanced relation. For the nonflat case R=Z and S_n=Z/2 (constant coefficients), tensor of an arbitrary quasi-isomorphism need not be a quasi-isomorphism; the proof restricts inversion to K-flat representatives and correctly retains the nonzero Tor of Z/2 tensor^L Z/2. A complex unbounded in both directions is covered by 06YS and the derived criterion, with no degreewise boundedness used. The identity composite-index case and three-index composition follow from the displayed strict formulas. This checks B1--B10, C1--C8, D1--D5 and E1--E7 against the actual sources and hypotheses: there is no new-node relabelling, no tag-only input, no use of an uncited proof, and no hidden flat-coefficient assumption.

## Unfinished work

No mathematical portion of the assigned one-level split remains. Required server dry run and push are performed after writing this report; their output is authoritative for delivery status.
