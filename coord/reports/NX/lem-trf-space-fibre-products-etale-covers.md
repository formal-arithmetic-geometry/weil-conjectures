# Stage-1 repair: lem-trf-space-fibre-products-etale-covers

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-space-fibre-products-etale-covers.json`: split statement, seven explicit proof steps, no Mathlib match; no new nodes.
- `citations.json`: one verbatim current statement excerpt for every step/node citation.
- `review.md`: mathematical findings and resolution of each return point.

The unmerged child `lem-trf-fibre-product-over-representable-diagonal` is withdrawn from this delivery. Its returned node, the returned parent, report and citations remain in `archive-returned/` in this sandbox, and `searches.jsonl` is retained. This removes an unlanded proposed addition, not a node of the shared DAG. Four existing Mathlib leaves are reused; no new leaf is created.

## Attachments

None. The project search in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact item id and `AlgebraicSpace|algebraic.space` finds no declaration stating the item. No Lean was written or compiled. The master checkout is not used as evidence of a finished proof.

## WANTED

None. All sources used are in the supplied Stacks checkout.

## What was wrong and what changed

The returned head was 2544e89fce. The current shared item is still unsplit, with the same statement and the complete historical ancestry. I compared all JSON fields of the retained sandbox item against the current item, retained the prior searches and delivery materials, and refreshed the current base metadata. The required initial dry run exited successfully at d0179d6e10; that mechanical acceptance did not repair the mathematical return.

D1: the old child is precisely the fibre-product clause under weaker assumptions, so applying it was not a split. Steps 1–4 now construct the sheaf, its diagonal and its scheme atlas in the parent. No substantive clause is delegated to a new restatement.

C1/C4/D5: Stacks spaces-topologies.tex 041F ends with “Omitted.” Step 6 now proves representable etaleness by scheme tests; step 7 proves joint surjectivity by choosing field-valued representatives and a common field extension. Neither step applies 041F as a theorem. The proof of the atlas calls four existing scheme permanence nodes, each of whose statements I read. Thus etale base change/composition and surjective base change/composition no longer hide behind the definition of an algebraic space.

B9: the rejected child's ancestry consisted only of the item and omitted the intervening created nodes. That proposed child is withdrawn. The parent retains the complete current-base chain through ample-local, polarized-scheme descent, polarized-log descent, log-ideal charts, log blowup, desingularization, nodal resolution, plurinodal alteration, nearby duality, specialization comparison and trace specialization to lem-trf-local-term-locality. No new node has an ancestry to fill.

I made the point-set meaning of “jointly surjective” explicit at the end of the statement: points are equivalence classes of field-valued maps, with equality after a common extension (03BU). This adds a definition inline and a field-definition dependency; it changes no hypothesis, conclusion, or convention about representable etale maps. In particular, the final scheme assertion is proved under the item's explicit representability convention, rather than asserted for a broader notion of an etale map.

The returned parent’s Mathlib query strings did not match the retained command log. I replaced its search records by the exact tool/query strings and actual hit lists in searches.jsonl. The retained searches include two substantive phrasings, for fibre products and for etale covering pullbacks. Their hits are scheme permanence/covering declarations and generic relative-representability declarations; none states this algebraic-space result. No unrun search is recorded and no searches were repeated unnecessarily.

## Not duplicates

No new nodes. Whole-DAG tag/word searches and blueprint_refs searches for `representable`, `jointly surjective`, `fibre products`, `algebraic spaces`, and `03BU` found no blueprint node stating the item. The four reused permanence nodes state scheme facts, not this algebraic-space closure and covering result. The withdrawn 04T9 child would have been the forbidden clause restatement; it is not delivered.

## Review by NX

I read both returned node files in full and Stacks spaces.tex 02X2 (lemma-fibre-product-spaces), 04T9 (lemma-fibre-product-spaces-over-sheaf-with-representable-diagonal), the definition 025Y, and spaces-topologies.tex 041F (lemma-etale), including its omitted proof. I also read spaces-properties.tex 03BU and the following Tag 03H4 (lemma-points-cartesian) in full. The seven-step proof is the construction in 04T9, followed by the explicit common-extension argument of lemma-points-cartesian for the omitted covering proof. For the reused scheme facts I read morphisms.tex 01S1, 02GO and 02GN and the statement of every cited DAG node. There are no new statements to test or new sources to justify.

Step 1 uses def-trf-algebraic-space for F, G and H being sheaves and def-weil-pbc-sites-and-cohomology for the equalizer/gluing condition. Gluing the two coordinates and testing their equal images in H is elementary; I wrote both existence and uniqueness instead of citing a general limit theorem.

Step 2 uses exactly the representable-diagonal clause of def-trf-algebraic-space and existence of scheme fibre products in def-pc-fibre-product. A test T gives two equality loci A and B; the scheme A times_T B represents simultaneous equality. No product-of-representable-transformations theorem or identification from a cited proof is being assumed. The proof on test schemes specifies the representing object.

Step 3 uses those same statements for U and V and their atlases, the scheme U times_S V, and representability of Delta_H. In particular, the H hypothesis is used here; one cannot conclude U times_H V is a scheme over an arbitrary sheaf without that hypothesis. This is the explicit source construction, not an application of the rejected child.

Step 4 uses the atlas scheme-test clause of def-trf-algebraic-space, scheme pullback existence, lem-weil-pbc-surjective-base-change and lem-weil-pbc-etale-scheme-base-change for A times_T B to B, and lem-trf-surjective-morphism-composition plus clause (2) of lem-weil-pbc-etale-composition-cancellation for its composite to T. All four nodes concern arbitrary scheme morphisms; no finite-type, Noetherian, quasi-separated, or nonempty assumptions are added. The equality T times_P W = A times_T B is justified by the two lift data. This establishes representability as well as both properties of the atlas, and then all three defining conditions for P are available. Each permanence node is already a Mathlib leaf, so no off-unit tool declaration is needed.

Step 5 uses the natural-transformation clause of def-trf-algebraic-space. The two inverse sectionwise constructions give existence and uniqueness for every algebraic space Q, so the universal property really is categorical. def-pc-fibre-product is no longer wrongly used as a theorem about universal properties in a sheaf category.

Step 6 uses the algebraic-space fibre products established in the preceding steps and exactly the definition of representable etale in def-trf-algebraic-space. A scheme test T gives T times_H H_i, already a scheme etale over T by the hypothesis; this does not assume base change along a nonscheme preserves an unspecified property. When G itself is a scheme the identity test gives the final scheme clause directly.

Step 7 uses the point convention expanded in the statement and def-weil-field for its fields, not a theorem falsely attributed to the algebraic-space definition. If z and a point of H_i have equal image in |H|, the definition provides a common extension M with exactly equal H-sections. The section pair over M is then an actual point of the fibre product mapping to z. This is the complete short argument in the source's lemma-points-cartesian; it is elementary once the point equivalence is written. A rational point over the original K is not claimed. This checks the possible residue-field extension, which an argument on underlying sets alone would miss.

Edge cases checked: empty S; F, G or an atlas empty; identity atlases when the spaces are schemes; H terminal; infinite covering families; the empty family (forcing H and then G to have no points); nonsplit field extensions, for which a common extension rather than a K-rational lift is essential. No statement dispute was found under the explicit representability convention. I checked B1–B9 (no new nodes; inline definitions, correct tags, ordinary TeX), C1–C8 (actual cited statements, no hidden permanence theorem, no child/circular citation, only existing Mathlib tools), D1–D5 (the construction and omitted argument are now in the parent), and E1–E7 (all scheme tests and fields have the indicated hypotheses). Every proof step is under 1000 characters, so none crosses the long-step threshold. The historical unit binding is retained, and this helper does not replace the unit's contracting-correspondence proof.

## What remains unfinished

Nothing in this one-level split. Lower existing nodes retain their own statuses. The repaired split passed the remote dry run (c889210e2b). After tightening the source tag and citation excerpts, a final dry run and push are required; deliver.py records the resulting delivery commit.
