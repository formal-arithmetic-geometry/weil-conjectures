## Worker report

Files written: dag/nodes/sec-six-functors-basics/lem-sfb-finite-locally-free-fppf-descent.json (item, statement, split); citations.json (26 verbatim statement quotations). No Lean files were written or compiled. No repository file was changed.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. All mathematical inputs already have DAG nodes. The proof now has seven steps, each below 1000 characters; no hidden long step is retained.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint tag and by finite-locally-free/descent terminology. DescendFiniteLocallyFree.lean proves descent to an inverse-limit stage (Tag 06AC), not fppf effectivity. Descent.lean proves descent for closed subschemes of a fixed ambient scheme; it does not state effectivity for arbitrary covers with arbitrary transition isomorphisms. IsFiniteLocallyFreeOfDegreeOfEtaleCover.lean concerns an already existing morphism and an etale covering, not construction of a scheme. None attaches to this item.

## Literature wanted

None.

## Corrections and limitations

The imported statement is unchanged. The empty proof has been replaced. The inherited blueprint creation chain has no imported ancestor: tools/blueprint_refs.py ancestor reports None. I retained its detailed existing from.place, from.node and via, and filled same_as with []. This is inherited metadata, not an invented blueprint ancestor. I read the current literature/blueprint/latest unit, its direct-images statement and proof; the unit record and chapter record were also read. This item is a supporting algebraic-geometry descent input on the already recorded Hilbert-stack branch. It is not the key node of the unit and does not change the unit realization fields.

The existing etale-degree-descent node is too narrow for an fppf cover. Instead Step 4 explicitly invokes the three existing fpqc property-descent statements and Step 5 invokes the existing arbitrary-base-change rank statement. No new node restates the item or one of its clauses. Nothing remains unfinished in this stage-1 split.

## Searches

Before writing I searched all dag/nodes by Tags 0245, 02VO, 023Q, 02KD, by affine/fpqc/fppf/descent terminology, and read every cited statement. I searched the whole imported blueprint using tools/blueprint_refs.py search for 'finite locally free', 'affine descent', and '02VO'; no blueprint node states this stack assertion. The old item already records two semantic phrasings; I read its results and kept them. The new msearch.py calls in searches.jsonl use LeanFinder, LeanSearch, Loogle and grep. I read the hits: FlatDescent supplies descent of isomorphism and other properties of an existing morphism, Finite supplies affineness/base change of finite morphisms, and the module hits give rank properties. None constructs a finite locally free scheme from descent data. In particular IsFinite.instDescScheme is a finite coproduct over a common target, not effectivity. I inspected Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean, Finite.lean and FlatRank.lean. The distinct LeanFinder and LeanSearch phrasings plus the item's retained earlier queries check the terminology in both directions. Only actually run queries are appended to mathlib_searches; exact query texts are preserved.

## Not duplicates

No new node was created. The singleton affine-effectivity node is deliberately reused with the existing family-to-singleton encoding. The rank node is deliberately reused rather than adding another copy of Tag 02VO for fixed degree.

## Review by NA

I read descent.tex Tag 0245, label lemma-affine: its hypothesis is an fpqc covering and affine local objects, not quasi-compactness of the covering morphism. I read Tag 02VO, label lemma-descending-property-finite-locally-free: its proof separately descends finite, flat and locally finite presentation and then reads degree on fibres. I read Tag 023Q, label lemma-fpqc-universal-effective-epimorphisms, including the explicit compatible-map/unique-map formulation, and morphisms.tex Tag 02KD, label lemma-base-change-finite-locally-free. I verified the tag-to-label map in tags/tags. The statement agrees with these sources specialized to fppf families; fixed degree is a rank condition at every base point. No noetherian, positive-degree or quasi-compact-base hypothesis is added. There are no new nodes with additional sources to review.

Step 1 cites the finite-morphism-permanence node for finite base change, flat-morphism-base-change for flat base change, qcqs-morphism-permanence clause (3) for locally finite presentation, and finite-flat-rank-iso clause (2) for arbitrary-base-change rank equality. I read all four statements and checked that the last applies because the original map is finite, flat and locally of finite presentation. The definition node defines these as finite local freeness and defines degree by fibre algebra dimension. Fibre-product uniqueness proves the stated coherence; I do not take a pullback-coherence theorem from a mere definition. This step is marked non-elementary because the permanence and rank results are substantive cited inputs.

Step 2 uses finite local freeness only to obtain finiteness and uses the finite-integral-morphism definition, which explicitly includes affineness. I read the entire statement of fppf-family-coproduct-descent-encoding: it supplies the singleton datum, its fpqc membership even for infinite families, and the equivalence with family effectivity for the same scheme. These are exactly what Step 2 and Step 3 need. Its statement, not an internal construction from its proof, is being used. The scheme-coproduct-family statement supplies open, disjoint, covering coprojections, so the affine chart inverse image is in the matching summand. The affine-local-target statement explicitly permits testing on one affine open cover; I checked that all our opens and their inverse images are affine. No claim that the infinite coproduct map is quasi-compact is needed.

Step 3 uses fpqc-affine-descent-effective only in its stated singleton form: Step 2 supplies both required hypotheses. It yields a scheme with a datum-compatible isomorphism. The fixed-realization clause of the family-encoding statement then supplies exactly the required local isomorphisms and transition data. Step 3 does not assume the descended morphism is already finite or affine.

Step 4 uses fppf-covering-is-fpqc for the original family, rather than incorrectly treating a merely jointly surjective flat family as fpqc. Each of fpqc-descend-finite, fpqc-descend-flat and fpqc-descend-locally-finite-presentation states descent for an arbitrary fpqc family and an existing global scheme morphism. Step 3 supplies that morphism; the local isomorphisms supply all three hypotheses, using finite-locally-free's definition. Their conjunction is exactly the definition, not an uncited converse criterion.

Step 5 uses joint surjectivity from fppf-site's definition to choose a point over each point. The rank node's clause (2) applies to every scheme base change; its statement explicitly identifies rank with the dimension of the fibre coordinate algebra. The local isomorphisms identify those algebras linearly, so they preserve dimension. The degree definition now gives precisely d everywhere. I deliberately did not cite the etale-only descent node, since fppf members need not be etale.

Step 6 uses fppf-covering-is-fpqc and fpqc-covering-base-change to obtain the cover of Z required for gluing maps. The latter's statement is for either projection orientation after the canonical fibre-product symmetry. The representable-descent statement glues maps into an arbitrary target scheme; I use it first with W, then with T to prove that the glued morphism lies over T. Pullback universality identifies its restriction with the supplied isomorphism, rather than assuming the target of the glued map is a pullback. I read its explicit existence and uniqueness equations and recorded them verbatim in citations.json.

Step 7 inverts the compatibility equations, applies Step 6 to the inverse family, and uses the same representable-descent uniqueness to check both inverse identities. This final assembly is elementary relative to Step 6; its sole cited statement is used only to test equality locally. It proves actual descent of isomorphisms, not merely descent of underlying maps. The cited lemma's arbitrary scheme targets cover both inverse identities.

For delivery-errors B I checked self-contained statements of the existing inputs and retained single-escaped TeX in the JSON; there are no statement-only new nodes or Mathlib leaves to mislabel. For C I checked every cited statement as above, recorded one exact quotation per step/node occurrence, and declared all nonclosed off-unit statement tools in split_report.tool_uses. These are generic scheme-descent tools, not replacements for the six-functor unit route. For D the proof constructs the global scheme via affine descent, separately establishes its properties and fixed degree, and glues maps and inverses; it does not outsource the item to a renamed equivalent node. For E I checked arbitrary base T, infinite covers, empty covering members, d=0, the empty base and empty index set. Joint surjectivity forces T empty for an empty covering; then its unique empty object has every asserted constant-degree condition vacuously. On a nonempty base d=0 does not require a chosen point in Z; only base points are lifted to T_i. The proof never assumes etaleness, nonemptiness, or reducedness of a local object. No step longer than 2000 characters remains. No correction to the statement was necessary.
