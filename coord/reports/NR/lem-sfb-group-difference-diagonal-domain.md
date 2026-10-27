# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-group-difference-diagonal-domain.json`: statement item, split into eight proof steps; not in Mathlib. The statement and its six statement dependencies are unchanged.
- `citations.json`: one verbatim statement quotation for every citation in each proof step.
- `searches.jsonl`: actual search-command log; inherited item searches were preserved in the item and current searches were appended.
- `report.md`: this report. No new DAG nodes; zero new Mathlib leaves.

## Attachments

No attachment for the item. Searched the project source by the literal blueprint tag, item id, rational/group terminology and difference-map/diagonal terminology. The hits concern diagonal conormals, derived Mayer--Vietoris differences, and ordinary group-scheme operations; none states the domain criterion. No Lean was written or compiled.

The existing `lemma-nagata-dense-flat-pullback` records the closed Mathlib declarations `AlgebraicGeometry.IsSchemeTheoreticallyDominant.of_isPullback` and `.pullbackSnd`. I read the current Mathlib source, including lines 38, 74, 94 and 114, and its quasi-compactness and flatness hypotheses. This is an existing attachment, not a request to edit that node. The existing `lem-chow-agree-on-dense-open` likewise already records a closed project declaration.

## WANTED

None. The source PDF and Stacks TeX needed for this split are present.

## Issues found and changes made

The item had a statement and Mathlib searches but no proof. Its statement is correct as imported. Milne's Chapter I Lemma 3.3, printed p.17, uses an auxiliary point u in U. That sentence cannot simply be applied as a k-rational-point argument for the present arbitrary-field scheme statement. I retained the source's difference-map route and supplied smooth fpqc descent instead: on T=N intersect (X times U), the actual morphism a=c(x,y)f(y) descends along its projection onto the open image W. No statement hypothesis was added, and no geometric integrality of X was inferred.

The item inherits a long auxiliary chain from the six-functor stability argument. I read the latest blueprint unit and its direct-images proof (3). This generic geometry prerequisite does not replace any unit step, and the item is not the unit's key statement, so the unit's realization fields are not edited. Its existing blueprint provenance (including null nearest ancestor) is preserved; ancestor lookup prints None and the server review accepts that provenance. Searches of the whole imported blueprint for difference, dense, scheme theoretically dense, and flat base change found no second statement of the item. The last search did reveal the already existing general density lemma and eliminated the only prospective new node.

## Search results and reuse

For the item I ran LeanFinder in two phrasings, Loogle for AlgebraicGeometry/RationalMap, LeanSearch, and the search-command grep for RationalMap/PartialMap. Hits `RationalMap.domain`, `mem_domain`, `toPartialMap` and `IsOver` describe domains and representatives; none relates the two-variable group difference to diagonal extension. I read the source of the domain/representative API and did not treat it as a match.

For the prospective flat-density fact I ran two LeanFinder phrasings, LeanSearch, two Loogle patterns, and grep patterns. The first grep used a spelling different from Mathlib's `IsSchemeTheoreticallyDominant`; the broader second grep found the correct file, and the corrected Loogle query found `IsSchemeTheoreticallyDominant.of_isPullback`. The whole-DAG/blueprint search then found `lemma-nagata-dense-flat-pullback`, which is cited without creating or changing any node. These auxiliary searches remain in searches.jsonl; no unrun query or unavailable service has been recorded as a negative result.

## Not duplicates

No new nodes. In particular the flat-density fact is a citation of `lemma-nagata-dense-flat-pullback`, not a duplicate node, and the separated-target uniqueness is a citation of `lem-chow-agree-on-dense-open`.

## Tool uses

`split_report.tool_uses` declares the generic off-unit tools for scalar-extension exactness, flat locally finitely presented openness, fpqc descent of morphisms, and composition of separated morphisms where applicable. The two Nagata density facts and the equality principle already have closed Lean audit records. These uses supply ordinary geometry to Milne's group-difference argument; they do not substitute a different route for a six-functor unit proof.

## Review by NR

I read Milne, Abelian Varieties, Chapter I Lemma 3.3, printed pp.17--18, with attention to the first paragraph (the sole part this item isolates). The forward implication and identity value are precisely the source's group difference construction. The converse in the report and item is an agent-written completion of the source's point argument over arbitrary k. I also read the latest blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`, the latest Nagata flat-density statement, and the statements of every cited DAG node. There are no new statements to review.

1. Step 1 uses `lem-weil-pbc-finite-type-over-noetherian` for Noetherianity of X over the Noetherian field spectrum. Its statement does give exactly that, without a smoothness requirement. `lemma-nagata-reduced-dense-image-schematic` requires a reduced target and qcqs map with dense image: X is reduced by the integral-scheme definition; the open U is quasi-compact since X is Noetherian, and an open immersion has isomorphic diagonal. I read Stacks 01T6, 056D and 01RE in morphisms.tex. The last identification with injectivity of structure-sheaf restriction is the cited definition node; restriction and composition of injective section maps are elementary. This proves density without assuming X is geometrically integral.

2. Step 2 uses `lem-sfb-stack-chartwise-smooth-etale-calculus` only for its explicit clauses on base change, open-source restriction (open immersions are locally isomorphisms), composition, and smooth implies flat and locally finitely presented. Schemes are special cases of its representable maps. I read Stacks labels lemma-composition-smooth (01VA), lemma-base-change-smooth (01VB), lemma-open-immersion-smooth (01VC), and lemma-smooth-flat (01VF). `lemma-nagata-dense-flat-pullback` takes a qcqs schematically dense map and a flat base change; both times that map is U into X. This produces successively X times U and U times U. I read Stacks 081H and 081I, including their quasi-compact/retrocompact qualifications, and the current Mathlib declarations. The extra citation `lem-weil-pbc-proper-fp-permanence` is used solely for its explicit separated-composition clause (e); the field spectrum is affine and its multiplication map exhibits a closed diagonal. This makes G an absolute separated target, so the old statement of the equality node suffices even without its stronger relative blueprint update.

3. Step 3 uses `lem-chow-agree-on-dense-open` exactly to equate two morphisms on an overlap once their equality on a schematically dense open is known. Both have source N intersect N', not X, and target the separated scheme G from step 2. I read Tag 01RH, lemma-equality-of-morphisms, in morphisms.tex and the current blueprint update. Gluing compatible morphisms on fixed open subsets requires no scheme gluing/existence theorem: the continuous maps and structure-sheaf maps glue directly by the sheaf axiom, and locality of the ring maps is checked on the cover. This establishes the unique b required by the item, rather than assuming its existence.

4. Step 4 uses only the group-scheme definition: its multiplication and inverse give the displayed c, and the group identities give c on the diagonal equal to e. I checked the actual domain N=Omega intersect (V times V): its inverse diagonal is V because Omega contains all of Delta(X). On N intersect H both factors lie in V intersect U, where the stated extension condition applies. This proves one inclusion by a construction, not by a new node restating the inclusion.

5. Step 5 is the point where arbitrary fields matter. A point of the diagonal supplies a residue-field point of the fibre N_x, so that fibre is nonempty even when x is not closed. `lem-weil-field-scalar-extension-exact` explicitly states exactness for every field extension; hence the map of field spectra is flat by the local-ring definition, and the cited smooth/flat calculus gives flatness after base change to X. The density lemma therefore applies to U into X and X_{kappa(x)} into X. It proves density after this field extension without assuming it is integral. The nonempty open N_x meets the dense U_{kappa(x)}, producing a point of T_x. The openness node explicitly states the flat locally finitely presented hypothesis used for the smooth q. I read Tag 01UA, lemma-fppf-open, in morphisms.tex. No rational point has been selected.

6. Step 6 checks fpqc in the exact convention of `def-weil-pbc-fpqc-covering`, Tag 022B. The singleton smooth surjection need not be declared quasi-compact: its affine opens have open images, and each affine open of W has a finite subcover of those images. Thus it satisfies the finite affine-image condition in the definition. The formula a=c times f(p2) uses the group operations, in their written order. On the inverse image of U, both coordinates are in U and c equals phi; cancellation is valid for a noncommutative group. This is an equality of morphisms on every test scheme, not equality of closed points.

7. Step 7 checks the descent equation rather than calling it automatic. R=T times_W T is smooth over W using the cited calculus, so the density lemma applies to W intersect U into W (qcqs since W is an open of Noetherian X) and R into W. On that dense open both candidate pullbacks are f of the same first coordinate; 01RH extends their equality to R. `lem-galois-fpqc-morphisms-descend` states full descent of morphisms between arbitrary W-schemes with their canonical data, not merely effective descent of objects or a definition. With source W and target G times_k W its equation reduces exactly to a r1=a r2. I read descent.tex Tags 0241 (lemma-fully-faithful) and 02W0 (lemma-refine-coverings-fully-faithful), including the full-subcategory conclusion. Applying uniqueness after restricting the covering to W intersect U proves the extension property. Hence x belongs to the defining union D.

8. Step 8 glues equalities already proved: the constructed difference on each V times V equals b by the uniqueness from step 3, and the group identity on its diagonal is e by step 4. These V cover D by definition. No uncited comparison or additional theorem is used.

I checked the edge cases U=X (both domains are the full relevant schemes), constant f (the difference is the identity), dimension-zero integral smooth X (a finite separable field spectrum), and X not geometrically integral (for example Spec of a nontrivial finite separable extension of k). The last case can make X times_k X disconnected; the proof uses schematic density, never irreducibility of that product. In characteristic p no separability of kappa(x)/k is used in the density argument. An extension of f cannot be glued by image containment alone: the proof explicitly constructs a, checks the overlap equation, and descends it. Separatedness of G is used for uniqueness, while smoothness and connectedness of G are harmless unused hypotheses retained from the item. All non-elementary steps have citations whose full statements are quoted verbatim in citations.json; all steps are shorter than 2000 characters. The review against B--E removed the prospective duplicate density node, replaced the hidden rational-point choice, and added the separated-composition citation to avoid relying on an unstated relative reading of the old equality node.

## Unfinished work

None in the one-level split. Existing dependency nodes retain their own stage states.

## Validation

The server `review_split` passed. The full required `deliver.py --no-push` dry run then exited successfully with `OK (not pushed)` at ca90e6f455f and reported that server preflight passed. The statement was unchanged; all eight proof steps are under 2000 characters. This report now records that result; a final dry run validates the report before push.
