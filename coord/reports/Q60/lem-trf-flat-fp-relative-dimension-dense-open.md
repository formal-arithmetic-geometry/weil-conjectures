## Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-flat-fp-relative-dimension-dense-open.json`: item, statement unchanged, seven-step split, no exact Mathlib match.
- `citations.json`: one entry for every node used by every proof step, quoting its statement verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own log; `write_split.py` is sandbox scratch only.

## New nodes

None. There are zero new Mathlib leaves. The split reuses the Mathlib leaf `lem-weil-pbc-flat-lfp-open` and the existing finite-type dense-open dimension and open-cover results.

## Attachments

None. Searched the whole `WeilConjectures/` tree of `/home/ubuntu/weil-src-slopmaster2` for the item's exact id, dense-open dimension language, and flat finite-presentation dimension language. The hits concern smooth relative dimension, Noether normalization, or unrelated cohomological fibre dimensions; no declaration gives this item. No upstream master sorry declaration is treated as proved.

## WANTED

None. All sources needed for this split are in the local Stacks checkout.

## Findings and changes

The imported statement agrees with Stacks Tag 081L, `flat.tex`, `lemma-flat-finite-presentation-dimension-over-dense-open`, alternative (1). Tag 02NJ, `morphisms.tex`, `definition-relative-dimension-d`, defines its bound exactly as the local topological fibre-dimension inequality written in the item. Local finite presentation supplies local finite type, so no hypothesis is missing. The bound is on dimension at a point, not on the Krull dimension of the fibre local ring. The statement has not been changed.

The original proof was empty. The new proof follows 081L case (1): take the 054T open pieces of constant fibre dimension, use 01UA openness to rule out pieces of dimension greater than e, and conclude from their fibrewise dense union. The last implication, abbreviated in 081L, is expanded on finite-type affine opens of the fibres. The existing dense-open clause of `lem-kun-dimension-extension` and the open-cover dimension theorem do exactly what is needed. Thus no second copy of 054T or 0A21 and no node restating a clause of the item is created.

DAG searches included tags 081L, 045U, 054T, 01UA, 0A21 and phrases about dense opens, fibre dimensions, and component dimensions. Whole-blueprint searches through `tools/blueprint_refs.py search` included `dimension dense`, `dense fibre`, `locally algebraic`, `dimension component`, and `0A21`; none supplied another blueprint statement of this item. `ancestor` confirms `lem-trf-local-term-locality`. Its inherited descendant chain and exact Tag 081L support place are retained. The chapter and unit records were read, including the current contracting-correspondence correction; this is a generic scheme-theory tool under the existing modification branch, not a change of the unit's route or of its statement.

Current Mathlib queries were run only through msearch.py: LeanSearch, a valid Loogle query, two LeanFinder phrasings, and grep. The actual queries and hit summaries are appended to the item and remain in searches.jsonl. The relevant hits were openness, flatness, and smooth relative dimension, not the asserted dense-open theorem. Read `UniversallyOpen.lean` around lines 132–149, especially `UniversallyOpen.of_flat` (147), and `Smooth.lean` around lines 129–145; the first is already the DAG's openness leaf and the second requires smoothness. Existing searches inherited from the item's creator are retained verbatim.

## Tool uses

The item's split_report declares the existing cross-unit tools for review: `lem-sbc-flat-fibre-dimension-strata-core`, `lem-weil-pbc-dimension-at-point-open-subspace`, `lem-sc-scheme-sober`, `lem-weil-pbc-dimension-bound-open-cover`, and `lem-kun-dimension-extension`. These are used only for the statements quoted in citations.json. In particular the Kunneth chapter node supplies its purely geometric dense-open dimension clause, with no coefficient-category identification. `lem-weil-pbc-affine-chart-base-change-iso` is already Lean-closed; `lem-weil-pbc-flat-lfp-open` is already a Mathlib leaf. No maintainer-owned top-level tool_uses field is written.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. Reused the existing dimension-piece theorem rather than creating a trace-formula version.

## Review by Q60

I read 081L's statement and its complete case-(1) proof in flat.tex, 045U and 054T in more-morphisms.tex, 01UA's existing Mathlib implementation, 02NJ's dimension definition in morphisms.tex, the affine/open pullback formulas 01I4 and 01JR and sobriety 01IS in schemes.tex, and the neighbourhood minimum 0055 and local/open-cover dimension argument 0B7I in topology.tex. I also read 0A21's statements in varieties.tex, especially the invariance under nonempty opens for irreducible schemes and the component-dimension description. Each cited node's statement was opened; I did not take a fact from its proof as if its statement provided it. No new statement-only source needs review because there are no new nodes.

Step 1 uses the actual definitions of an open immersion, fibre, fibre product and dimension at a point. It explains the residue-field identification and both inverse fibre maps through the universal property. The resulting homeomorphism preserves the same distinguished fibre point and its neighbourhood dimensions. This is a formal identification, not an application of a base-change invariance theorem with stronger hypotheses.

Step 2 cites `lem-sbc-flat-fibre-dimension-strata-core`, whose statement really supplies opens V_n, dense inverse-image union in each fibre, and local fibre dimension n at every point of V_n. Its base open is the whole S, so the restricted hypotheses are exactly the item's hypotheses. The statement is sufficient; no Cohen–Macaulay datum, disjointness, or pure-dimensionality is imported from its proof.

Step 3 cites `lem-weil-pbc-flat-lfp-open`, whose statement explicitly gives openness for a flat locally finitely presented morphism. Nonemptiness of the image and intersection with U follow from points and the item's definition of density. The contradiction uses the original-fibre bound established in step 1, so there is no unproved invariance under field extension.

Step 4 uses the pointwise affine presentation from `def-sbc-locally-finite-presentation` and the complete statement of `lem-weil-pbc-affine-chart-base-change-iso`. Its rings are R, B and kappa(s); the inverse image of the base chart in Spec kappa(s) is the whole spectrum. Its conclusion explicitly identifies the inverse-image open with Spec(kappa(s) tensor_R B). Tensor generators are written out using balancing, so no tensor finite-generation lemma is hidden. `def-weil-finite-type-morphism` supplies the meaning of finite type; an affine scheme with this finite set of algebra generators is finite type over the field. No claim that arbitrary intersections of affine opens are affine is made.

Step 5 restricts density to the open A by testing its nonempty opens. Its only non-elementary citation, `lem-weil-pbc-dimension-at-point-open-subspace`, states the equality of the two local topological dimensions at every point of an open subset. It applies because H is open in Y, not merely locally closed.

Step 6 takes actual minimum-attaining neighbourhoods from `def-kun-topological-dimension-at-point`. `lem-sc-scheme-sober` gives uniqueness as well as existence of generic points, which provides both quasi-sobriety and T0 as explained in the step. These are precisely the hypotheses in `lem-weil-pbc-dimension-bound-open-cover`; its statement permits arbitrary covers and empty spaces. Hence the bound on dim H is justified by a theorem explicitly cited here.

Step 7 uses only the dense-open clause of `lem-kun-dimension-extension`. Its finite-type-over-a-field hypothesis is checked for A in step 4, not asserted for the whole fibre or X. The dimension notation agrees by the quoted `def-kun-dimension`. The local-dimension minimum bounds the value at x by dim A, and the open-subspace lemma identifies that value with the one in the original fibre. This completes the pointwise conclusion for arbitrary x.

I checked empty X and empty fibres (no points to test), empty S (then X is empty), U=S, and e=0. If U is empty its stipulated density forces S empty. As a nontrivial test, A^r_S has one constant-dimension piece r: the open-image argument forces r<=e whenever its restriction satisfies the hypothesis. A disjoint union of components of different dimensions is handled piece by piece; the argument never assumes equidimensionality of a fibre. It also permits a non-Noetherian or nonreduced base. Fibre charts are finite type over fields, so the finite-type dimension tool is used only where justified. Dependence traversal of the reused nodes found no path back to the item; no cited node is merged. Every proof step is below 2000 characters. The main correction in the work was to expand 081L's fibrewise-density sufficiency explicitly and reuse the existing dimension results rather than add another component-dimension lemma.

## Unfinished work

None for this one-level split. Independent maintainer review remains the next project stage after direct delivery.
