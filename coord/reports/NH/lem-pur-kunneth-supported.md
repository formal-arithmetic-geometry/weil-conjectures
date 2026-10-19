# lem-pur-kunneth-supported — NH stage-1 repair

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-kunneth-supported.json`: existing statement, repaired split; not a Mathlib leaf.
- `citations.json`: 35 verbatim statement quotations for the eight proof steps.
- `report.md`: this report.

## New nodes

None. Zero new Mathlib leaves. Existing generic statements cover the hidden arguments; introducing copies would violate the duplicate-node rule.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag and for supported Kunneth terminology. The trace-formula occurrences concern supported correspondence classes, not this full two-clause theorem. The node's existing stage-2 Lean binding is retained without asserting that its proof is finished. Master is reference material only.

## WANTED

None. The current blueprint proof and relevant Stacks sources are present locally. No SGA source was used.

## Returned point and repair

The dedicated handoff in `coord/returns/NH.md` identifies old step 1 (2757 characters) as hiding lemmas and requires retaining the statement, Lean record and proof route. I replaced it with three arguments, citing the existing statements which supply Noetherian finite-type permanence, Noetherian open-subscheme permanence, finite type of a quasi-compact open immersion, separated finite-type base change, separated composition, lower K-flat representatives and exact constant-coefficient inverse image. The remaining finite-algebra-generator and total-degree calculations are written out; these are two-line consequences, not new lemmas. This addresses the substantive return instead of merely cutting its paragraph at character boundaries.

I also removed the old long proof by roofs of witness naturality. The current pro-etale product definition already specifies a natural derived theta comparison and evaluation counits. Step 8 writes the naturality equation and its adjoint argument directly. Step 7 separately applies the existing site-comparison equality. The localization steps retain the original double-localization route and explicitly cite the compatibility node for the actual supported products, including the boundary square. All step references were renumbered.

The complete natural statement and the entire `lean` record are unchanged as JSON values. Historical metadata, searches, imports and blueprint fields are preserved. The current blueprint main-20261015 proof has the same four-paragraph route as the old master source; proof-step sources now point to that current proof. The item is not its unit's statement, so no unit metadata is edited.

## Not duplicates

No new node pairs arise. Whole-DAG/blueprint searches found the ordinary Kunneth theorem, the supported product definition, the existing comparison and localization nodes, and the existing generic geometry interfaces. These are cited instead of duplicated. The two partial proper Kunneth statements do not state arbitrary closed-support Kunneth with its pro-etale clause.

## Review by NH

I read the current blueprint `main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-kunneth-supported.md` and its separate proof, the historical unit and chapter records, and the return entry. I read Stacks `sites-cohomology.tex`, Tag 0F1M (lemma-bounded-below-tor-amplitude), including its pullback clause; `etale-cohomology.tex`, Tag 09XP (section-cohomology-support) and Tag 0F1E (remark-define-kunneth-map); `morphisms.tex`, Tags 01T4 (lemma-base-change-finite-type) and 01T6 (lemma-finite-type-noetherian); and `properties.tex`, the definition and open-subscheme characterization at 01OV/01OW. These justify the retained source route. There are no new nodes requiring their own source review.

For step 1, I opened pqf-def-locnoeth and the three cited Noetherian/open-immersion statements. The first defines the affine criterion, the second explicitly includes a Noetherian target and finite-type source map, the third makes every open Noetherian and quasi-compact, and the last requires precisely the quasi-compact open immersion established by affine intersections. A field is Noetherian because there are only two ideals. The definition of finite type gives the finite charts, and taking the generators at the two stages together verifies the composite finite-type assertion. The proper-permanence node's closed-immersion base-change clause supplies the restricted closed diagonal; the proper-morphism definition supplies the meaning of separated. No properness of X or Y is asserted or needed.

For step 2, I read lem-pod-separated-finite-type-base-change: it supplies exactly the product projection over Y for arbitrary base change. The separated-composition clause (e) of lem-weil-pbc-proper-fp-permanence supplies absolute separatedness of the product. The tensor-product chart has the explicitly listed algebra generators, giving finite type; the same construction works for all four product ambients. I checked that both factors have already been proved finite type and separated.

For step 3, I read the entire lem-kun-0f1m statement and all three clauses of prop-weil-pbc-inverse-image-modules-exact. The former supplies a representative zero below a and its K-flat pullbacks, not merely an abstract flatness definition. The latter identifies the constant coefficient ring and module pullback, and supplies exactness. Thus the representative of K remains zero below c, and the derived tensor is computed by the pulled-back K-flat model as in def-kun-derived-tensor. The total-degree inequality is explicit and persists after open restriction. No boundedness of the derived sections tensor is assumed; it belongs to unbounded D(A).

For steps 4 and 5, I read lem-pur-support-restriction-triangle, lem-pc-derived-tensor-second-factor-functor, lem-pur-supported-product-localization, lem-pur-ordinary-kunneth-finite-ring, lem-sf-triangle-morphism-iso, def-pur-supported-exterior-product and def-weil-finite-field-fiber. The triangles require bounded-below sheaf complexes, established in step 3. Tensor exactness is in D(A), not just a sheaf category. Localization explicitly includes the second-variable boundary with its signed left-tensor shift comparison. The ordinary Kunneth node applies to the actual canonical arrow in the unbounded ordinary etale category and includes these coefficient rings, without constructibility. The standing coefficient prime is different from char(k). Full supports give the ordinary arrow by the definition's forgetting-support identification. The triangle two-isomorphism lemma then proves the first component invertible for both X and U.

For step 6 I checked the actual target support triple: T=X times Y, B=X times W, C=Z times Y. Its intersection is Z times W, and its third ambient is U times Y. The first-variable localization statement supplies precisely the three displayed products and the boundary square. Its last two components are those proved invertible in steps 4 and 5. This uses the statement of the localization node, never uniqueness of a triangle completion or material buried in that node's proof.

For step 7, I read lem-pur-support-site-comparison in full. Its statement gives the displayed equality of the actual exterior-product arrows as well as the comparison isomorphisms, and requires F bounded below; this is why step 3 is necessary. The product ambient satisfies its separated finite-type hypotheses by step 2. For step 8 I read def-weil-pbc-etale-origin-witness and the full def-pur-proetale-supported-exterior-product statement. The latter defines the product as the adjoint of theta and evaluation counits and explicitly fixes theta's derived naturality. Its naturality squares prove the displayed equation before applying the adjunction bijection. Conjugating by the specified witness isomorphisms proves precisely the second clause. The finite-ring, ordinary module-sheaf coefficient categories agree throughout; no condensed or completed tensor category is silently substituted.

I checked delivery-errors B through E. All citations have verbatim statements in citations.json; the proof dependency list is their union. There is no new statement-only node with a hidden proof, elementary duplicate, restated item clause, or cyclic new dependency. Every remaining substantive input has a cited existing node. The definition-only citations are used for their actual constructions (finite-type charts, tensor totalization, or the defined product adjoint), not for unstated theorems. No statement dispute is introduced.

Edge cases: empty X or Y and empty support give zero sections and the unique zero-object isomorphism; full supports recover ordinary Kunneth. For a point and K=A with L=A the product is the ordinary unit isomorphism. Shifting K and L shifts the lower bound by c+a as the explicit total-degree calculation predicts, including negative bounds. Nonflat K is allowed because only the L factor uses K-flatness. Thickened closed subschemes cause no change to the localization supports. Noncanonical witness automorphisms satisfy the same naturality conjugation, so the result is about the specified map, not only existence of some isomorphism.

I inspected the former long step and the witness argument for hidden comparisons. All final steps are below 2000 characters (maximum 1446); geometry and K-flat existence are now obtained from existing statements. The only calculations left inline are generator lists, a truncation cohomology calculation, the degree bound, and adjunction naturality.

## Searches

Inherited searches were retained. Fresh searches were made only through msearch.py and are recorded in searches.jsonl. The supported Kunneth queries in two phrasings gave algebraic etale-locus and local module-cohomology hits, not the sheaf-theoretic supported Kunneth statement. Loogle and grep found no supported Kunneth declaration. Exploratory geometry queries led back to existing DAG Mathlib interfaces, so no new geometry node was created. Exploratory K-flat queries returned module flatness criteria and bounded representatives; no new node was created. Two exploratory grep subdirectories were mistakenly specified with a Mathlib prefix and thus did not search the intended subtree; I did not use those zero results as evidence of absence. The actual item grep searched the whole Mathlib tree.

## Unfinished work

None in the requested one-level split. The existing cited unsplit compatibility children retain their own stage-1 work; this repair does not claim those are proved. No Lean files were written, compiled, or built.
