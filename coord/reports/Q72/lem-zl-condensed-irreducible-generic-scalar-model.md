# Stage-1 report: lem-zl-condensed-irreducible-generic-scalar-model

## Files written

- dag/nodes/sec-zeta-weil/lem-zl-condensed-irreducible-generic-scalar-model.json: existing statement split into four proof steps; statement unchanged; no exact Mathlib match.
- citations.json: verbatim statement quotations for all 11 step/node citations.
- searches.jsonl: five searches run by the required msearch.py command, including two semantic phrasings, LeanSearch, Loogle and Mathlib grep. The inherited item searches remain in the item, and the new actual queries/results are appended.
- report.md: this report. No new nodes, no Mathlib leaves, no Lean files or compiles.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for generic-scalar and condensed/dualizable terminology; no declaration of the project states this item. The completed lisse-evaluation input does not itself state generic scalar descent on a prescribed cover.

## WANTED

None. The proof source is present: Hemo–Richarz–Scholbach, Constructible sheaves on schemes, arXiv:2305.18131, Theorem 4.13, printed p. 12, diagram (4.4) and its following paragraphs; Lemma 4.1(2), printed p. 8; Proposition 4.3(3). Also read Stacks sites-cohomology.tex, lemma-derived-pullback-composition (Tag 0D6D) and lemma-pullback-tensor-product (Tag 07A4), including their K-flat proofs, and verified those labels in tags/tags.

## Audit findings

The item has no statement error. It asks for existence of an isomorphism on U with the prescribed P; it does not require the resulting isomorphism to restrict to the initially chosen alpha on all of the generic fiber. Pulling back along a section proves exactly the stated existence and the asserted isomorphism of M. In general s composed with r is not the identity; the argument only uses r composed with s equal to the identity.

No new lemma is needed: the generic-fiber component and coefficient comparison is already stated by lem-zl-generic-fiber-components-section; the ordinary derived component square is already stated by lem-zl-component-derived-pullback-square. The latter is an existing unsplit dependency, not a claim of a finished Lean proof. Neither is recreated or strengthened. Checked the whole DAG for relevant titles, generic/component and condensed/scalar terminology; searched the whole blueprint using blueprint_refs.py for generic scalar, generic, component, perfect-constant and dualizable, and followed the nearest ancestor. The existing parent local-model theorem is more global but depends on this item and cannot be cited in its proof. A reachability inspection of every chosen input found no dependency path back to this item.

The off-unit citations are generic tools: geometric-field-proetale-evaluation identifies the generic point's coefficient topos with the profinite topos, and ringed-derived-monoidal-comparisons supplies pullback composition and identity. Both are declared in split_report.tool_uses. The argument stays on HRS's component-section route inside the local-model input to the blueprint's field-stage projection formula. There is no SGA source.

## Not duplicates

No new nodes were created. All seven proof inputs are existing nodes, including the two component interfaces that could otherwise have been duplicated.

## Review by Q72

I read the item against the actual irreducible-case proof of HRS Theorem 4.13, including diagram (4.4), its proof of component surjectivity and section existence, and the paragraph that pulls an arbitrary generic isomorphism back using the section. I also read Lemma 4.1 and Proposition 4.3. The ordinary derived module categories, canonical pulled-back coefficient rings, fixed P and quantifier over every prescribed ind-etale w-contractible affine cover are retained. Faithful flatness is a hypothesis of the item; the component-section input needs less, which is legitimate. No reducedness of X or U, coefficient flatness, finite presentation of u or uniform t-structure assertion has been inserted.

Step 1 uses the statement of condensed-lisse-proetale-locality for preservation of dualizability, geometric-field-proetale-evaluation for the coefficient-compatible profinite topos identification, and condensed-wcontractible-lisse-evaluation for the perfect/lisse equivalence at the one-point profinite set. The singleton is extremally disconnected and its coefficient sections are precisely R. A coefficient-compatible equivalence of module sheaf categories is exact and preserves the tensor universal property; applying it to complexes gives the derived tensor identification. Thus evaluation supplies a perfect complex over R, not over an unrelated stalk or section ring. I opened all three statements and copied the relevant assertions into citations.json.

Step 2 applies generic-fiber-components-section with X, eta and the actual u. Its statement gives a continuous section, the commutative component square, the coefficient-compatible derived equivalence for V, scalar compatibility, and the identification of V to eta with the structure map of S_eta. Every one of its hypotheses is in this item, including algebraic closedness and the ind-etale condition. I did not infer a derived scalar comparison from a bare definition of the component projection: the cited statement expressly includes it.

Step 3 uses locality again for K restricted to U, the component equivalence in the evaluation theorem to choose M and beta, the coefficient-compatible derived square applied to the affine projection V to U, and the generic-fiber equivalence from step 2 to transport alpha. Both U and V are affine since X and eta are affine. I checked the directions: pi_V inverse image carries r inverse image of M to g inverse image of pi_U inverse image of M. Full faithfulness is used on the isomorphism of those two derived objects; its inverse also descends, so the descended map really is an isomorphism. No conservativity of geometric points is assumed.

Step 4 uses the scalar definition, ringed-derived-monoidal-comparisons and the scalar clause of the evaluation theorem. On a profinite slice the coefficient ring is restriction of Lambda; a continuous map gives slice pullback by fiber product on profinite test objects, preserving finite limits and finite jointly surjective covers. Its coefficient map is the canonical restriction isomorphism. Consequently the cited general ringed-topos comparison applies to these actual morphisms. Expressing the scalar functor as pullback of L_*(P), composition gives both s inverse image of r inverse image of M equal to M and s inverse image of L_S_eta(P) equal to L_S(P). Applying pi_U inverse image and beta inverse then proves the U assertion. This step uses the exact ordinary derived scalar functor, not an unjustified t-exactness or tensor-flatness claim.

For small cases I checked X equal to a geometric point, P equal to zero, the zero coefficient ring, a disconnected w-contractible source, and nonreduced X. At a point the argument reduces to the stated evaluation equivalence; zero objects and zero coefficients satisfy all formulas; disconnectedness is handled on the entire profinite S and requires no finite partition; nilpotents never enter the proof. The generic component section input is valid without reducing X, so no hidden integrality assumption appears. Nonempty X and faithful flatness exclude the empty source in the item, although the component and scalar identities also make sense on empty profinite spaces.

Against delivery-errors B–E: there are no new statements to misstate, duplicate or populate with an unperformed search. Every non-elementary fact in the four steps has an explicit existing node, each node's statement was read, and each citation has a verbatim quote. No parent theorem, proof-only construction, definition masquerading as a theorem, or circular dependency is used. The chain of isomorphisms and the two section identities are written out. The argument is assembled from smaller existing inputs rather than moved into a restatement of the item. All four steps are shorter than 2000 characters. Nothing required correction in the statement or source.

## Unfinished work

None for this one-level stage-1 split. Existing unsplit dependencies retain their own queue positions.
