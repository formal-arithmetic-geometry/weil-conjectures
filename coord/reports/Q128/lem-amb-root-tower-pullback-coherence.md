# Q128: lem-amb-root-tower-pullback-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-root-tower-pullback-coherence.json`: statement, split; retains the original statement, statement dependencies, provenance and blueprint ancestry. Eight proof steps and declared generic tool uses added. Mathlib verdict: no match for the complete assertion.
- `citations.json`: one verbatim statement quote for each step/node citation.
- `searches.jsonl`: actual recorded searches from msearch.py. The additional sandbox script `write_split.py` only constructs this delivery and is not a library or launcher change.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this item is not its unit's key statement.

## Attachments

None. The exact blueprint tag has no project declaration. Searches of WeilConjectures by roots, root pullback, Tate inverse limit and the item id found only partial interfaces. In particular, `AlgebraicGeometry.Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_comp` in `lean/WeilConjectures/EtaleCohomology/TateTwist/RootsOfUnityPullback.lean:39` is a finite-level etale composition statement, not a pro-etale tower/tensor/reduction theorem. Its finite-level conclusion alone cannot discharge this item. No Lean was written, compiled or built.

## WANTED

None. All source material needed for this assembly is present.

## Problems found and changes

The imported item was a statement-only extraction of returned root-projection steps 6-9, with no proof. The statement is well typed and true with its specified constant-ring identifications. No statement correction or statement dispute was needed. Its last sentence is essential: the proof constructs a cone with vertex v^{-1}L and never claims that inverse image preserves the infinite limit. No finite root map or reduction map is assumed invertible.

The existing generic tower lemma `lem-pur-tate-inverse-limit-base-change` was inspected, but requires finite-level comparison isomorphisms. This item deliberately does not use such a hypothesis. Instead, its proof constructs the compatible tuple directly from arbitrary finite-level linear maps, using the already existing sectionwise limit definition. This is a short elementary construction and does not warrant a second tower lemma.

The tensor comparison must be the pro-etale/ringed-topos one. `lem-weil-pbc-module-pullback-tensor` is an O-module statement on schemes and is not cited. Likewise `lem-weil-pbc-constant-ring-inverse-image-comparison` is etale-only and is not cited. The generic small-site constant-module theorem and the independent-universe algebraic tensor theorem have the hypotheses actually needed here.

## Searches and reuse

Searched the whole DAG for roots-of-unity, inverse-limit and pullback/tensor concepts and for tag 03EL. Read the full statements of the root comparison definition and theorem, the generic tower comparison, the constant-left-module inverse-image theorem, the site composition generator theorem, the ordinary tensor comparison, the tensor adjoint test, and the definitions cited in the final steps. A transitive dependency check of all final proof dependencies found no path back to this item.

Ran blueprint_refs.py ancestor for the item: `thm-amb-vector-bundle-purity`. Whole-blueprint searches `roots of unity`, `root tower`, `inverse limit`, and `tensor product pullback` did not find an exact duplicate of this combined assertion. Kept `same_as: []`. Read the current main-20261015 proof of that ancestor and the fixed chapter and sk-prop-an unit. This is coefficient bookkeeping below the vector-bundle integration paragraph and does not replace any unit-level purity step. Off-unit proof results are declared individually in split_report.tool_uses.

All additional Mathlib searches were run through msearch.py with this group and item and their exact logged queries are recorded in the item's mathlib_searches. Two LeanFinder formulations were read, together with LeanSearch, two Loogle queries and two grep searches. Hits included finite `rootsOfUnity`, `restrictRootsOfUnity`, abstract `limit.post` and its projection/composition lemmas, `SheafOfModules.hasLimit` and evaluation-preserves-limit instances. Read RootsOfUnity/Basic.lean (definition at 56 and induced-root-map interface at 144-154) and Sheaf/Limits.lean (hasLimit and evaluation preservation at 69 onward). These are components or generic infrastructure, not a one-line specialization giving the full assertion on the specified pro-etale root tower. The existing limit node already supplies the relevant Mathlib leaf; no duplicate leaf was created. None of these services was recorded as unavailable when it returned hits.

## Not duplicates

No new nodes were created; consequently there are no new/existing-node pairs sharing a Stacks tag to distinguish. The original item is retained as the combined assertion assigned in the brief. The existing generic tower comparison assumes finite-level isomorphisms, whereas this item does not; this delivery creates no replacement for it.

## Review by Q128

I read the current main-20261015 ancestor proof, the item's source and every cited node statement. For the underlying human-written sources I opened Stacks sites.tex Tag 03CB (lemma-composition-morphisms-sites), Tag 00WX (lemma-adjoint-sheaves), and Tag 00W2 (lemma-limit-sheaf); sites-modules.tex Tags 03CO/03DB (sectionwise abelian and module limits), Tag 03D7 (lemma-adjoint-pullback-pushforward-modules), Section 03EK (section-tensor-product), and Tag 03EL (lemma-tensor-product-pullback). The assembly is marked agent-written because these sources provide the constructions rather than this specific eight-clause root assertion. There are no new statements requiring additional sources.

Step 1 uses the specified pro-etale construction and the left-exact-site theorem to obtain a geometric inverse image on the chosen small sites. The generic constant-left-module theorem actually states the constant-ring isomorphism carrying scalars to the same scalars, and its compatibility with composition. The constant-sheaf and sheafification definitions justify the additional naturality in a coefficient ring homomorphism by equality on constant presheaf sections. This avoids silently importing an etale-only comparison. Site and coefficient universes are the compatible small-site ones of the inverse-image definition; the generic lemmas apply in the larger coefficient universe.

Step 2 uses precisely clauses 1 and 2 of lem-pur-roots-of-unity-inverse-image-iso: power-transition compatibility and semilinearity. It does not use clause 3's isomorphism hypothesis. The roots definition supplies the killed-by-N module action and power transitions; the inverse-limit statement supplies the compatible tuples. I checked the exponent calculation with representatives differing by a multiple of ell^s and with the transition from s+1 to s. Module axioms are the ordinary exponent laws, and the constant sheafification extends the constant-scalar construction. In particular Z_T is the constant sheaf of the abstract ring Z_ell throughout, not silently the inverse limit of constant finite rings.

Step 3 reads the literal root adjunct in def-pur-roots-of-unity-inverse-image, rather than borrowing an unstated coherence clause from it. Its formula on a generator is pullback of the unit along the composite U -> T' x_T V -> V. The cited site-composition generator theorem states both the nested-generator normalization and the equality test for abelian sheaves. Its functors are the base-change site functors, after the canonical fibre-product associator; that associator respects projections by their universal property. Pulling a unit through two such projections equals pullback through their composite, so the two claimed maps agree. Identity is the same calculation with the identity projection and the normalized identity adjunction. Thus this step proves the new root compositor instead of merely asserting that it is functorial.

Step 4 uses the full sectionwise description in def-pur-sheaf-inverse-limit. The displayed transition calculation makes the tuple belong to the target limit. Since each component map is linear and natural in restrictions, the tuple assignment is a linear sheaf morphism; equality of every coordinate is literal equality of sections of that limit. This is an elementary instance of the cited definition, without an infinite-limit preservation theorem or a surjectivity assertion for projections.

Step 5 expands each projection of the composite and substitutes step 3. Naturality of the cited site compositor moves the projection across the identification. The uniqueness just proved in step 4 then gives the limit identity and compositor. This is a short coordinate computation, not a separate general lemma hidden inside the proof.

Step 6 invokes lem-pur-independent-inverse-image-tensor-comparison, whose statement explicitly supplies a natural tensor isomorphism and its value on transported generalized pure tensors. The algebraic lift is the action-transport construction in def-weil-proetale-inverse-image, so the finite-limit and algebraic-transport hypotheses are satisfied. Constant B is identified by step 1. I checked the extra scalar extension in the notation v^*: along that isomorphism y tensor b maps to by, inversely y maps to y tensor 1. The map defining h_v is balanced because c_L is linear. The tensor and sheafification definitions then construct the sheaf map and its B-linearity. No flatness or nonzero-ring hypothesis is needed.

Step 7 uses the original-section tensor adjoint equality test, not an incorrect assertion that all target sections are pure tensors. That node also states the evaluation for two successive inverse images, conditional on a normalized compositor. The site generator theorem provides exactly this normalization and step 1 together with the inverse-image action definition gives its scalar compatibility. Substitution of the step-5 limit compositor makes the tensor values identical, proving h composition; the identity case is the same unit-normalized evaluation. The cited source statements therefore provide the equality detection actually used.

Step 8 checks that ell^rB=0 gives the required factorization through Z/ell^r and that the projection formula is balanced. The two composites have exactly the displayed tensor values, equal by step 4; the same adjoint test detects their equality. It does not cancel alpha or c_r. This is elementary from the earlier projection equation and the cited tensor universal property/test, so it remains an elementary step instead of a new node restating the reduction clause.

I tested the construction when T or T' is empty, B is the zero ring, r=1, v is the identity, w is the identity, and B=Z_ell with no finite-stage annihilator. The tuples, tensor maps and equalities remain meaningful in all these cases; in the last case only the conditional reduction clause has no instance. Neither nonemptiness nor finite-type, noetherian, flat, or finite-coefficient hypotheses are inserted. Primality and invertibility of ell are retained as assigned, although the formal coherence calculation itself needs neither root-map invertibility nor a chosen primitive root. Every proof step has fewer than 1100 characters, and none hides a long comparison argument. There are no new elementary, duplicate, or clause-restatement nodes. The checked statements and proofs support all cited uses; citations.json copies their actual statements verbatim.

## Unfinished work

None at the natural-language split level. The remaining required actions are the server dry run and direct delivery; their success is reported by the final delivery response.
