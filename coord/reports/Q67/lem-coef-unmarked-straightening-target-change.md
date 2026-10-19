# Worker report: lem-coef-unmarked-straightening-target-change

## Files written

- `dag/nodes/sec-six-functors/lem-coef-unmarked-straightening-target-change.json`: seven-step split, unchanged statement, no new nodes and no Mathlib leaves.
- `citations.json`: seven verbatim excerpts, one for each step/dependency pair.
- `searches.jsonl`: eight actual searches, recorded by msearch.py. The item's audit retains its inherited grep records and adds the exact logged queries and responses. The inherited “not run” placeholder is superseded by these actual searches.

## Attachments

None. Searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint tag and for straightening, unstraightening, coherent cones, target change and enriched Kan extensions found no declaration stating the item. The master checkout was read only as reference; no sorry declaration was treated as a finished proof.

## Literature wanted

WANTED: Jacob Lurie, Higher Topos Theory, Section 2.2.1 and Proposition 2.2.1.1(2), archival copy for this item. I read the official IAS PDF online, printed pp.73–74: the correspondence construction on p.73 and both clauses of Proposition 2.2.1.1 on p.74. The source states target-change functoriality without proof. The detailed proof here is agent-written. No Stacks tag states this simplicial-enriched result, and no SGA source is used.

## Corrections and limitations

The item statement and its two statement dependencies are unchanged. The first draft invoked enriched Yoneda and a coend/word normal form without sufficient cited support. Self-review removed that entire calculation. The final proof uses the existing structural clause of `lem-coef-cone-boundary-projective-cells` and proves the comparison by categorical pushout universal properties. Its added dependency is in the same unit and its transitive statement/proof closure does not contain this item. No new node or source dispute remains.

The current main-20261015 ancestor proof was read at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2, the displayed finite mapping-complex adjunction before the derived inverse limit. The inherited `sk-prop-sf-biduality-general` unit binding and historical ancestry are retained. This foundational node serves the ordinary-base straightening comparison, step 8 of `lem-coef-space-valued-straightening`; it is not the unit's key statement, so no unit realization fields were edited.

## Review by Q67

I read `coord/delivery-errors.md` B–E, the complete item, the recorded chapter and unit, the current ancestor proof and the actual statements of both proof dependencies. The source proposition assumes only a simplicial set S, a simplicial functor pi between simplicial categories, and phi with the given opposite variance. It imposes none of the Kan, fibrancy, cofibrancy or equivalence hypotheses that would make the marked-straightening node inapplicable here. The item has exactly these hypotheses and the same Kan-extension comparison. The U-description and compatibility clauses follow from the explicit maps below. I read the marked node to exclude using it outside its locally Kan setting.

Step 1 uses `lem-coef-cone-boundary-projective-cells` precisely for its statement that the old full subcategory of M is the target category, all M(v,c) are empty and M(v,v) is Delta^0. I checked both instantiations: target D^op with phi, and target D'^op with phi'=pi^op phi. The node allows arbitrary small targets, repeated images and arbitrary X. The other citation, `lem-coef-unmarked-straightening-quillen`, states exactly the cone-pushout construction, its mapping diagram and enriched transformations. No Quillen-equivalence clause or model assumption is used. This structural theorem is the sole non-elementary input.

Step 2 constructs E_G directly. Its composition into the new object is G's action, so the functor identities prove all the new category axioms. The old mapping sets and lack of reverse arrows established in Step 1 make a functor with specified old restriction exactly an enriched natural transformation; I checked its action-square equation against the straightening node's definition. This remains true when pi identifies objects or G has empty/non-Kan values.

Step 3 uses the two pushout universal properties from the straightening node's stated construction. I checked the boundary equality on C[X], not C[S]: F on that boundary is pi^op phi C[a]=phi' C[a]. The proposed inverse functor agrees on each pushout factor. This proves both inverse equations by uniqueness, and identifies beta_G as b mapping to (pi^*b)u. Naturality in G follows from that formula. No coend, enriched-Yoneda or existence-of-Kan-extension theorem is imported.

Step 4 gives an explicit inverse to the particular adjunct in the item. I checked the types H:D->sSet, K and P:D'->sSet, h:P->K and t:K->P. The equation (pi^*t)u=eta follows from beta_P(t)=eta. It yields th=1_P by the defining Kan adjunction, while beta_K(ht)=u=beta_K(1_K) yields ht=1_K. Thus the argument proves that the specified map is invertible, not merely that some comparison exists. Both injections used are bijections already established in the statement or Step 3, so this step needs no external theorem.

Step 5 checks X-naturality on the two actual pushout factors before taking adjuncts. Step 6 applies the exact U-simplex definition in the straightening statement: the displayed equation for a monotone theta proves compatibility with faces and degeneracies as well as the projection to S. Step 7 checks identity and composite substitutions on the same factors, then uses the uniqueness of adjuncts. Identity and composite Kan-extension identifications are the canonical ones induced by the defining adjunction bijections; arbitrary choices of left adjoints are never identified literally without them.

I tested X empty (both mapping diagrams are initial), S empty (necessarily X empty), terminal targets, pi the identity, pi identifying two objects, diagrams with empty mapping values, and X=Delta^0 (the usual covariant representable and its restriction adjunction). For a terminal source mapped to an object e of D', the comparison sends a point to the identity at e, with D' acting by postcomposition; this verifies the opposite-category variance. If D is empty then S and X are empty; no nonexistent object was chosen. Composite and simplex-operator formulas handle noninjective maps as well as identities.

B1–B9 introduce no new-node obligations: there are no new definitions or statement-only children. I searched the DAG and the whole blueprint for cone realization, collages and target change. The existing `cone-boundary-projective-cells` supplies the structural input and was reused; the canonical cone-presheaf adjunction has only the identity target, and the marked target-change node has additional target hypotheses. The Mathlib searches returned ordinary Kan extensions, strict-Segal/coskeleton interfaces, enriched-functor definitions and coherent simplicial thickenings. I read the returned signatures and the relevant Mathlib files; none states this target-change comparison. Search queries and outcomes are retained exactly as logged, including the unsuccessful first Loogle pattern and the first grep's overqualified subdirectory.

C1–C5 and D1–D5: all imported mathematical facts are stated by the cited nodes; no dependency's proof is used as its interface, no content is moved to a restatement child, and the omitted source details are carried by the elementary pushout and adjunction calculations. C6–C8: the added structural dependency is in the item's unit, its closure is acyclic with respect to this item, and no off-unit tool use is needed. E1–E7: smallness, opposite variance, attaching-map domains, arbitrary object maps, empty cases, and the actual specified mate were checked above. There is no statement or source correction.

Every proof step is below 2000 characters. I regenerated citations.json from actual statement substrings and verified each substring and the complete set of step uses locally. The initial six-step draft passed server checks and a full no-push dry run; those results do not certify this subsequent mathematical revision. The final revision must receive its own no-push dry run before handover.

## Second reading by Q67

I independently read HTT §2.2.1, Proposition 2.2.1.1(2) (printed pp. 73–74) and checked the item's statement hypothesis by hypothesis: arbitrary small simplicial set S, small D,D', arbitrary simplicial functors φ and π, the stated opposite variance, the specified cone pushout map, its left-Kan adjunct, and the right-adjoint U description. The identity and composite clauses are exactly the functoriality in that proposition. I tested S=∅, X=∅, X=Δ⁰, π=id, π identifying objects, empty mapping simplicial sets, terminal targets, and D=∅; all constructions and variance remain defined and the claimed maps reduce to the expected identity or initial cases.

- Step 1: checked against the structural clause of `lem-coef-cone-boundary-projective-cells` and the cone/presheaf definitions in `lem-coef-unmarked-straightening-quillen`; the two pushouts have the stated old subcategories, no arrows from v to old objects, and q induces exactly u. Verdict: PASS.
- Step 2: checked the explicitly constructed collage `E_G`, its composition, units, and action-square equations against the definition of enriched natural transformation; no Kan or fibrancy assumption is used. Verdict: PASS.
- Step 3: checked the inverse by the two categorical pushout universal properties and the equality on the boundary `C[X]`, including the formula for β and its naturality in G. Verdict: PASS.
- Step 4: checked the specified mate using only the defining Kan-adjunction bijections; β_P(t)=η gives both inverse equations by injectivity. Verdict: PASS.
- Step 5: checked cone functoriality for every map X→Y over S and the adjunct naturality equation. Verdict: PASS.
- Step 6: checked the simplex-operator equation for every monotone θ:[m]→[n], so the degreewise β bijections assemble over S and are natural in G. Verdict: PASS.
- Step 7: checked identity and composite target substitutions on both pushout factors and the canonical composed-adjunction identification; the U composite law follows degreewise. Verdict: PASS.
- No new nodes were introduced, so there are no new-node statements to audit. The existing dependency statements were read in full; both are in the same proof unit and say exactly the facts used.

I found no mathematical or citation defect requiring a JSON repair. I added this independent audit section only; the item, its seven steps, proof dependencies, searches, and citations remain unchanged. The source PDF is not archived in `literature/`, so the existing `WANTED` entry remains appropriate.
