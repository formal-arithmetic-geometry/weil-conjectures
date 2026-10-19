# Stage-1 split: lem-coef-cocartesian-joyal-fibration

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cocartesian-joyal-fibration.json`: existing statement retained; proof expanded to six steps, with no new node.
- `citations.json`: verbatim excerpts for every cited node in every proof step.
- `report.md`: this report.
- `searches.jsonl`: searches recorded by `msearch.py`.

Zero new nodes and zero Mathlib leaves. The three existing statement dependencies and the existing model-category homotopy-extension/cylinder statements are reused.

## Attachments

None. I searched both named read-only Lean source trees for the exact item id, HTT Proposition 3.3.1.7, cartesian/cocartesian fibration terminology, and likely declaration names. No sorry-free project declaration states this item. The upstream master source is reference material only and was not treated as proof evidence.

## Wanted literature

WANTED: Jacob Lurie, *Higher Topos Theory*, HTT.pdf, Proposition 3.3.1.7 and its proof (printed pp. 209–210), including Corollary 3.3.1.2 and the opposite cocartesian assertion. The IAS/Harvard PDF was read online on 2026-10-17 and is not archived in `literature/`; no document was downloaded. No SGA source is used.

## What changed and what was wrong

The imported node had the correct statement but no proof. I retained its exact arbitrary-base hypotheses, including the absence of quasicategory and nonemptiness assumptions, and followed the source route: factor the base through a quasicategory, transport the cartesian fibration across the categorical equivalence, solve the lifted square over the quasicategory, lift the base homotopy and correct the relative homotopies, then pass to opposites for cocartesian fibrations. The blueprint ancestry remains `prop-coef-integral-exceptional-adjoint`; the split realizes its auxiliary sentence that HTT Proposition 3.3.1.7 supplies arbitrary-base categorical fibrancy for the filtered-cone rectification.

The proof is marked agent-written because the source is online rather than archived. No statement dispute was found. No existing node duplicates the full arbitrary-base lifting assertion; the quasicategory-base clause in `lem-coef-relative-marked-anodyne-calculus` is strictly weaker and is used only after the base replacement.

## Review by Q128

I read the item statement, its chapter `sec-six-functors`, unit `sk-prop-sf-biduality-general`, the current blueprint ancestor paragraph, and the full statements of every cited node. The item is exactly HTT Proposition 3.3.1.7: for a degreewise injective categorical equivalence $A\hookrightarrow B$ over any simplicial base, a cartesian or cocartesian fibration supplies a strict diagonal. The edge cases $A=\varnothing$, $B=\varnothing$, empty total space, empty base, identity fibrations, and a point base satisfy the statement without adding hypotheses.

Step 1 uses the Joyal model structure statement: factor $S\to\Delta^0$ and use the fibrancy characterization to obtain a quasicategory $T$. I checked that the factorization stays in the input universe and that no quasicategory hypothesis on $S$ is smuggled in.

Step 2 uses the exact clause (2) of `lem-coef-cartesian-base-equivalence-invariance`, which supplies the replacement cartesian fibration and universal categorical-equivalence comparison after arbitrary base change. I checked the marked-relative model statement: natural cartesian markings are fibrant, all objects are cofibrant, and a weak equivalence between fibrant objects has a marked inverse and coherent sharp mapping paths. The generic right-homotopy-extension statement supplies the relative strictification used to preserve the given map on $A$.

Step 3 applies the quasicategory-base clause of `lem-coef-relative-marked-anodyne-calculus` to $q:Y\to T$ and then the Joyal lifting characterization to the categorical-equivalence inclusion $i$. The cartesian/cocartesian horn definitions are the exact ones in `def-coef-infinity-fibrations`; no stronger marking or base condition is used.

Step 4 uses the relative mapping-cylinder criterion to represent the equivalence between the two base maps by a homotopy fixed on $A$. The initial-horn/cartesian lifting condition is applied simplexwise to lift that homotopy, preserving its boundary. I checked that the endpoint map lies over $jg$ and that no fibrancy assumption on $A$, $B$, or $S$ is needed.

Step 5 follows the source's final composite: pair the corrected map with $g$, use the comparison inverse, and apply the cartesian lifting condition to the remaining homotopy fixed on $A$. The endpoint therefore satisfies $hi=f$ and $ph=g$ as strict simplicial equalities. Every non-elementary ingredient is cited; the two homotopy corrections are not hidden behind the word “transport.”

Step 6 uses the opposite clause of the marked-relative model statement. Reversing simplices exchanges cartesian and cocartesian horns and preserves monomorphisms, categorical equivalences, and lifting squares, so the cartesian result gives the cocartesian result.

Against delivery-errors B–E, the item is self-contained through its existing definition dependencies, has no new statement-only node to audit, and records real Mathlib searches. The four fresh `msearch.py` calls (LeanFinder, Loogle, grep, LeanSearch) returned only ordinary Quillen/model-category or inner-fibration declarations; none states the arbitrary-base cartesian/cocartesian-to-Joyal theorem. `citations.json` was generated by checking every quote as an exact substring of the cited statement. The dependency closure has no path back to the item, no SGA source is cited, and no Lean file or compiler was written or run.

## What remains

No new prerequisite was created. The item is ready for the independent second reader and the required server dry run.


## Second reading by Q128

I independently read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the item and every statement cited in the original and repaired proofs. I read HTT Proposition 3.3.1.7 on printed p. 209, Corollary 3.3.1.2 on p. 205, the following self-duality discussion on p. 210, and Lemma 3.1.3.6 on p. 157 in the Harvard PDF. These are simplicial results with no Stacks tag; no SGA source is used. I also read the current main-20261015 ancestor proof, paragraph 2 (coherent finite adjunction and derived inverse limit), and the recorded chapter/unit. This auxiliary lemma supports the filtered-cone lifting prerequisites of that coherent realization; it changes neither the unit nor the chapter route.

Item statement: PASS against HTT Proposition 3.3.1.7 and its opposite dual, hypothesis by hypothesis: arbitrary simplicial base and total space, every monomorphic categorical equivalence, and strict triangles. No statement change or statement dispute. Over a point it is quasicategory fibrancy; for identity fibrations the base map itself is the diagonal. For empty base all maps have empty domain; for empty total space a square has empty A, and a categorical equivalence from empty A forces B empty (test against the empty quasicategory). Empty A or B is consequently covered without imposing nonemptiness. The n=0 and n=1 simplices require no additional horn hypotheses.

- Step 1: PASS against the full statement of lem-coef-joyal-model-structure and HTT's base replacement: functorial factorization of the terminal map gives T fibrant in the input universe.
- Step 2: REPAIRED/PASS against clause (2) of lem-coef-cartesian-base-equivalence-invariance, the full family of hypotheses there, lem-coef-marked-relative-cartesian-model supplying that family, and the pullback/marking clause of lem-coef-relative-marked-anodyne-calculus; explicitly introduces Z and its natural marking.
- Step 3: REPAIRED/PASS against the universal comparison applied to every vertex and the marked model's exact fiber/inverse criteria: obtains v and a sharp mapping path vu to identity, without claiming this path is fixed on A. Kan 2-horn fillers compress or reverse its edges if needed.
- Step 4: REPAIRED/PASS against the quasicategory-base Joyal-fibration clause of lem-coef-relative-marked-anodyne-calculus and the Joyal lifting characterization; checks qa=jgi, qk=jg, wi=uf, pr=g and ri=vuf as strict identities. Both A and B remain arbitrary simplicial sets.
- Step 5: REPAIRED/PASS against the sharp restriction Kan-fibration clause of lem-coef-relative-marked-anodyne-calculus, itself HTT Lemma 3.1.3.6: A and B are marked flat, the path precomposes with f, and lifting its initial vertex along restriction supplies the final endpoint with exactly hi=f and ph=g. The arbitrary base S is an allowed hypothesis of that cited statement. No use of the desired Joyal fibrancy of p occurs.
- Step 6: REPAIRED/PASS against the opposite horn convention and the defining categorical-equivalence tests: reversal preserves monos, takes inner horns to inner horns, and identifies the relevant functor homotopy categories with opposites. The written three-line identification justifies self-duality; the rest is reversal of the two triangle identities, so this step is elementary.
- New nodes: NONE. No duplicate, elementary helper, restated item, or new Mathlib leaf is introduced; B1–B7 have no new-node instance to repair.

Changes and reasons:

- Removed the unsupported assertion in old step 2 that inverse homotopies can already be chosen relative to A. The final mapping-space lift makes the required correction instead.
- Combined the old extension and base correction into the strict lift of repaired step 4. Old step 3 already forced g'=jg, so its subsequent nontrivial base correction was redundant; moreover a cartesian fibration does not lift an arbitrary homotopy forward from its initial endpoint merely by its cartesian horn definition.
- Replaced old step 5's unproved simplexwise extension by the exact Kan restriction theorem. Removed the generic right-homotopy-extension and relative-cylinder dependencies: the former required a justified good path object, and the latter characterizes cylinder maps but does not by itself produce the claimed homotopy.
- Made every hypothesis of the conditional base-equivalence node explicit, and justified the inverse through vertex fibers rather than silently equating categorical and Cartesian equivalences.
- Expanded the opposite argument and replaced unrelated cocartesian-horn citation excerpts with verbatim full statements of the actual cited nodes. Verified all eleven quotes and the exact step/use coverage.
- Independently ran LeanFinder, Loogle and grep with fresh mapping-space/inner-fibration phrasing. The returned types are ordinary fibered categories, all-horn Quillen fibrations and inner fibrations, not the item. Read Mathlib InnerFibration.lean:29–100; no full match. Read-only keyword searches of both project source trees found no relevant attachment. Normalized search results to the exact searches.jsonl records and removed two old node records absent from that log; all seven retained searches are genuine logged calls.
- Checked the dependency closure of each principal prerequisite: none reaches this item (428, 429 and 312 visited nodes respectively). No new node, Lean file, compiler call, or live-project edit was made. The preserved first-worker review above describes the initial version; this second reading records the repaired delivery.
