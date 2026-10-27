# Stage-1 worker report: lem-sp-signed-double-roos-tensor-exchange

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-signed-double-roos-tensor-exchange.json`: item, statement, split into eight explicit coordinate steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/dependency pair.
- `report.md`: this report. `searches.jsonl` records the actual five searches made through msearch.py; `write_split.py` is sandbox-only preparation code, not a delivery node.

New nodes: 0. New Mathlib leaves: 0. No claim or clause is transferred to a new node: the matrix computation, product identifications, tensor signs and augmentation calculation are written out in the item. The inherited searches, source and blueprint provenance are retained.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, signed double Roos, Roos with tensor, and iterated/double cones. The project has single-tower Roos constructions and comparisons but no declaration giving all the item's clauses. No compiler, Lake or build command was run.

## WANTED

None. The relevant source documents are present. The blueprint supplies the completeness/reduction-as-cone motivation, not the coordinate proof; accordingly `proof_origin.by` is `agent`.

## Findings and corrections

The statement is unchanged and passes the sign/type checks below. The original item had no proof. Its Roos model uses coordinates `(v,u)` and differential `(dv,-du-(1-s)v)`. The definition node writes the same model in reverse order `(y,z)=(u,v)`; switching the biproduct order recovers exactly the stated convention, without negating either component.

Mathlib searches through the prescribed command found `HomologicalComplex₂.totalFlipIso`, mapping-cone shift/additive-functor comparisons, tensor constructions, and general shift commutators. I read `Mathlib/Algebra/Homology/TotalComplexSymmetry.lean`, including the component construction at line 57, `totalFlipIso` and the inclusion component identities. These are useful for implementation but do not directly give the two termwise countable-product Roos constructions with the specified tensor exchange and augmentation identities. Matching them requires constructing and identifying the relevant complexes and maps. The second semantic phrasing returned shift commutators rather than an exact Roos statement. All five actual query strings and their returned hits are appended to the item's inherited search records. None was unavailable and none is recorded as a leaf.

## Not duplicates

No new node was created. Searched the existing DAG for Roos, tensor exchange, coordinate interchange, augmentation identity, and fibre/cone calculus, and searched the whole blueprint using `blueprint_refs.py search Roos`, `search tensor`, and `search cone`. Read the existing endomorphism-fibre double-cone and coordinate-calculus statements. They give fibre/cone and shift comparisons, not this strict double-product/tensor statement. Existing definitions and the normalized comparison are reused directly. `blueprint_refs.py ancestor` confirms `sk-lem-sp-tower`; the item's existing concrete `from.place` and via chain are retained, and no blueprint node states the whole conjunction in another form.

## Review by Q27

I read the item, chapter `sec-smooth-purity`, unit `sk-lem-sp-tower`, and the current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/sk-lem-sp-tower.proof.md`. Its sentences saying reduction is a cone and the limit is complete are the route this auxiliary calculation serves. The proof stays within that route. I read Stacks `derived.tex`, Tag 014E / `definition-cone`, for the cone matrix; `homology.tex`, Tag 012Z / `definition-associated-simple-complex`, for the total tensor sign; `sites-cohomology.tex`, Tag 0941 / `lemma-derived-limit-is-ok`, including its K-injective proof; and `sites-modules.tex`, Section 03EK / `section-tensor-product`, for sectionwise tensor followed by sheafification. Stacks 0941 alone is about abelian sheaves: the module/unbounded/exact-product naturality assertion used here comes from the explicitly cited existing node `lem-weil-strict-roos-comparison`, whose full statement I read, not from a claim that the source tag directly states it.

For step 1 I checked `def-weil-category-product` states the projection universal property, and `def-sp-abelian` supplies finite biproducts. The product swap and product/biproduct maps are explicitly inverse by their projections. The commuting double transitions are an item hypothesis and imply `AB=BA` on each coordinate. No tensor/product preservation theorem is presumed here.

For step 2 I checked `def-weil-strict-roos-model` actually specifies the cone differential, diagonal action and evaluation. Reversing its `(y,z)` ordering to the item's `(v,u)` convention yields the displayed four entries. In particular the last differential is `dh+Bc-Ab`, not `-dh+Bc-Ab`.

For step 3 I substituted `(a,c,b,-h)` in the same four-entry differential with `A,B` exchanged, and compared all four entries with the image of the source differential. The reversed map is an inverse. This is an explicit sign calculation from the cited model, not an invocation of an unnamed interchange lemma.

For step 4 I checked the model's diagonal action and evaluation clauses. The two evaluation squares retain respectively `(a,b)` and `(a,c)`, on which the sign is one; the only negated entry is discarded. Every component of a strict morphism commutes with the product projections, so naturality follows on those same components.

For step 5 I checked `def-weil-abstract-derived-category` states localization at quasi-isomorphisms and `lem-weil-strict-roos-comparison` states descent, naturality, the comparison with total derived inverse limit and its normalization on projections and augmentations. The site is small in the module universe and countable products are exact, exactly as that comparison requires; no boundedness or normalization of a coefficient tower is added. The iterated derived comparison is the conjugate of the explicit chain isomorphism under these normalized comparisons. The proof does not appeal to uniqueness of an unspecified morphism between homotopy limits.

For step 6 I checked `def-pur-sheaf-tensor-product` defines the sheafified sectionwise tensor and `def-weil-presheaf-modules-sheafification` states the unique factorization needed to sheafify inverse unit maps. The two rank-one maps and their inverseness are written explicitly using the balancing relation. `def-pc-tensor-complex-sheaves` supplies the direct-sum totalization, and `def-pur-principal-koszul-quotient-towers` specifies the degrees -1,0. Thus only two terms occur in each tensor degree, even for unbounded Q. The inverse product/biproduct maps were already constructed in step 1 using the cited product definition. There is no assertion that arbitrary tensor products commute with products.

For step 7 I checked the three cited definition statements supply all three differential contributions: the Roos sign, tensor Koszul sign, and principal Koszul arrow and transitions. The exponent comparison is `(-1)^(a+p)=(-1)^p(-1)^a`. The Roos arrow is `-(1-s_n)` on both sides. The comparison leaves coordinates unchanged, so its transition, inclusion and evaluation identities are checked by the actual component maps, not a bare assertion of transport.

For step 8 I checked that the Koszul-tower definition states compatibility of the degree-zero inclusion with transitions and does not require t regular or Q K-flat, and that the strict Roos definition gives the zero-shifted-component augmentation. The calculation is `(v tensor 1,0,u tensor 1,0)` before beta and `(v tensor 1,u tensor 1,0,0)` afterwards. These are exactly the two coordinates retained in j-degree zero and the two zero coordinates in j-degree one. Applying the inverse tensor comparison leaves the former unchanged and produces precisely `u_H0`. This proves equality of the specified chain maps, which localization preserves.

I checked the B--E return criteria point by point. No new node needs additional hypotheses, provenance, sources or searches; there are no elementary, duplicate, Mathlib, or clause-restatement child nodes. Every cited node's statement was opened, the exact part used has a verbatim quotation in `citations.json`, and the sole non-elementary step cites the comparison theorem itself. The union of uses is `proof_deps`; no cited theorem depends on this item. All off-unit ingredients are generic definitions or the normalized Roos comparison, declared in `split_report.tool_uses`, and do not replace the unit's proof route. All steps are shorter than 2000 characters and consist of one explicit construction or coordinate calculation, so none hides a long comparison lemma.

Small cases: for t=0 the Koszul differential vanishes but the negative-degree transition is zero and the degree-zero transition is still one, so the same component calculation applies; for t invertible no contraction or regularity argument is used. In characteristic two the single negation becomes the identity and both differential formulas reduce consistently. For zero complexes all maps are zero between zero objects; for complexes concentrated in an arbitrary positive or negative degree the two tensor degrees and four Roos positions are exactly those displayed. Identity and zero transitions both satisfy the product formulas (A=1-s or A=1 respectively), and the sign test works in either case. For genuinely unbounded Q no infinite tensor diagonal appears because L has only two nonzero degrees. Exact countable products are needed only at the derived comparison step, not for any chain-coordinate construction.

## Unfinished work

None in the item's stage-1 split. Existing cited nodes retain their independent statuses. Delivery remains subject to the server dry run and the maintainer's independent review.
