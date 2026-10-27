# Q145 — lem-trf-pointed-etale-diagram-pullback

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-pointed-etale-diagram-pullback.json`: statement, split into six proof steps; the entire diagram is not a Mathlib leaf. Existing Mathlib leaves supply the general geometric facts.
- `citations.json`: seven step/node entries with verbatim excerpts of the cited statements.
- `report.md`: this report. `searches.jsonl` is the unmodified log written by msearch.py.

No new nodes or new Mathlib leaves. No unit or chapter files changed.

## Attachments

None. I searched the live project `lean/WeilConjectures/` for the blueprint tag, the item id, pointed etale charts and diagram/pullback terminology, also checked `lean/Sheaf/` and `dag/lean_names_upstream.json`, and found no declaration stating the whole item. Related pointed-etale ring lemmas are different statements. No compiler or Lake command was used.

## WANTED

None. All sources used are already in the repository.

## Corrections and source observations

The item's statement and statement dependencies are unchanged. There was no earlier split or report in this sandbox and no repair note for this item. The live node was unsplit. Its imported searches were preserved; I added the searches actually recorded by msearch.py for Q145, including a second semantic phrasing. One Loogle query used the deprecated `IsEtale` name and returned an unknown-identifier diagnostic: I recorded it as unavailable for that pattern, then reran it using `Etale`, obtaining the two etale projection instances. Search hits do not state the full item in one line. I read Etale.lean lines 39–93 and PullbackCarrier.lean lines 294–308 and 410–430 to distinguish the individual results from this assembly.

The historical blueprint ancestry is retained and its role explained in split_report.blueprint. I read the current main-20261015 locality proof and the unit/chapter records: the current locality argument is about contracting correspondences, and this historical auxiliary nodal-chart base-change lemma does not change that route. Stacks 0CBY, first proof, first paragraph explicitly reduces the finite-type diagram by base change; the proof here supplies the universal-property and marked-point details of that sentence. I read Morphisms Tags 02GN/02GO/02GP and 01S1 with its preceding Tag 0495, and Schemes Tag 01JP/01JT. No SGA source was used.

## Unfinished work

None in this stage-1 split. Existing cited leaves remain unchanged.

## Not duplicates

No new nodes were created. I searched the DAG for 0CBY, 01S1, the corresponding source labels, etale base change/composition and fibre-product point/image statements, and searched the whole blueprint with blueprint_refs.py for pointed etale diagram pullback, base change and fibre product. The useful existing nodes are cited rather than recreated. A general fibre-product associativity node is unnecessary because the actual maps and their inverse checks fit in Step 1.

## Review by Q145

I checked the split against delivery-errors B–E with the source and each dependency statement open. The item introduces all of its schemes, maps, points and hypotheses; its four notion dependencies define schemes, fibre products, etale morphisms and open immersions. I did not add hypotheses such as finite type, surjectivity of the original chart, a rational marked point, separability of residue extensions or an algebraically closed base. No statement dispute was needed.

Step 1 uses the universal-property sentence of def-pc-fibre-product, which explicitly gives existence and uniqueness of maps with prescribed compatible projections, and includes uniqueness of the fibre product up to projection-compatible isomorphism. I wrote both directions of each displayed isomorphism: the first inverse uses the given S-circ isomorphism alpha, and the second uses (w_0 a', b') as the V coordinate. The equation e_0 w_0 = f_0 p_0 ensures the maps land in the correct fibre products, and checking the two projections proves each composite is the identity. This is an elementary finite-limit calculation, not a new associativity lemma hidden as a node.

Step 2 takes exactly etale stability under arbitrary base change from lem-weil-pbc-etale-scheme-base-change, and clauses (1) and (2) of lem-weil-pbc-etale-composition-cancellation say exactly that open immersions are etale and etale maps compose. The base changes are e_0 along c and p_0 along q; the subsequent maps are the given open inclusions. The map f itself is never assumed etale.

Step 3 again uses only the stated universal property in def-pc-fibre-product. I defined both model projections and the map r to the original model. For arbitrary compatible morphisms A and B from a scheme Q, their equality over Z_0 gives both the V_0-coordinate equality needed to construct L and the Y-coordinate equality needed to prove m L = B. Uniqueness uses the U_0 and V projections. This checks the actual cartesian square, rather than asserting that an unspecified comparison transports etaleness. It is a routine universal-property verification and is under 1000 characters.

Step 4 uses precisely the arbitrary-base-change conclusion of lem-weil-pbc-etale-scheme-base-change, with m_0 as its etale map and r as its base map, now justified by Step 3. I checked that being a V_0-morphism gives pr_V0 m_0 = w_0, as required in Step 3. The equalities pr_V m = w and e w = f p are then computed explicitly from the projections and the restriction identity.

Step 5 uses the full subset-image equality in lem-weil-pbc-base-change-image, not merely surjectivity of a base change and not the proof of that node. I substituted C = {u_0}, p_0:U_0 -> X_0 and q:X-circ -> X_0. Its right side contains the specified x because q(x) = p_0(u_0); membership on the left supplies a point with both specified projections. This is the exact ordinary-point existence needed and does not promise a rational point over kappa(x). Tag 0495 and the proof of 01S1 confirm the interpretation.

Step 6 uses def-pc-scheme's category of schemes and the definition of morphisms of locally ringed spaces. Pullback on structure-sheaf sections of a composite is composition of the section maps by definition. I wrote the contravariant equality, checked that the two sides lie in Gamma(V,O_V), and substituted the given tau. No cohomological or flat base-change theorem is being used for functions.

For B, there are no new nodes, no postponed proof sketches inside statements, no undefined extra notions, no invented Mathlib matches and no unrun searches. TeX is stored with single logical backslashes. For C, every used non-elementary result is a cited existing statement, and citations.json excerpts are substrings of those statements; proof_deps is exactly the union of uses. All cited statement results are already Mathlib leaves, so no off-unit tool-use request is needed. For D, the proof carries the actual construction and projection checks and does not transfer a clause into a new node. For E, I checked identity base change, identity open restrictions, disconnected etale charts, non-closed marked points and nontrivial residue-field extension. For example Spec(C) over Spec(R) allows multiple ordinary points after base change; Step 5 asserts existence, not uniqueness, so that case is respected. Empty schemes cause no false existence assertion because the hypotheses already specify u_0 and x. The arbitrary morphism Y -> T need not be etale: only m_0 is used as the etale model arrow. No proof step exceeds 2000 characters.
