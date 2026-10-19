## Files written

- dag/nodes/sec-smooth-purity/lem-fin-finite-boundary-reconstruction.json: statement, split with seven proof steps; Mathlib searches found no match.
- citations.json: verbatim statement quotations for every step/node citation.
- report.md: author's review and handover.

No new nodes and no new Mathlib leaves. Existing node metadata, import flags and blueprint fields are retained. This item is not the unit key statement, so no unit record is changed.

## Attachments

None. Searches of WeilConjectures/ in the slopmaster2 source and exact upstream master found no declaration tagged with this item, and the searches for boundary reconstruction and constructible boundary concepts found only unrelated curve boundaries and compactification constructions. No master sorry declaration is treated as a finished proof. The item's recorded slopmaster2 audit is none. There is no matching item file in the archived slopmaster2 blueprint tree.

## WANTED

None: all sources used are present locally.

## Statement and proof corrections

STATEMENT-DISPUTED: the imported statement says "between finite-type schemes" without naming the base. The type check is that "of finite type" is a property of a scheme morphism; for a scheme one must supply a structure morphism. The unit's neighboring lem-fin-proper-bounded-constructible explicitly says finite-type k-schemes, and lem-fin-extension-by-zero and lem-fin-closed-immersion require finite type over k. I made this same implicit field k explicit in the item. This is a clarification of the unit setting, not a replacement by arbitrary Noetherian schemes, and the second reader should check that interpretation. No other hypotheses or conclusion change.

The imported geometric-stalk-conservative citation states only detection of isomorphisms; the extension-by-zero definition does not state the stalk formulas or exactness. I replaced that incomplete justification with the existing ordinary-etale lem-cbc-open-closed-recollement theorem, not a new restatement of the item. Exact sheaf preservation is lifted to complexes by explicit cohomology calculations. Derived pushforward composition and triangle preservation now have theorem citations. Both uses of the constructible triangulated-subcategory theorem are preceded by an explicit boundedness argument: its statement is inside D^b, and cannot itself supply that check on an arbitrary object of D^+.

## Unfinished work

None for this one-level stage-1 split. The existing lem-fin-finite-reflects-derived remains a child to be split by its own worker; it is not asserted to have a finished Lean proof here. No delivery push has been made.

## Not duplicates

No new nodes. Whole-blueprint searches for the item id and title found only this item; the search for exact-functor cohomology found no blueprint hit. I searched the entire DAG by statement content for localization, exact-functor cohomology, derived direct-image composition, triangle preservation, long exact cohomology and finite-type Noetherianity, and reused the existing nodes. In particular I did not duplicate lem-cbc-open-closed-recollement or lem-weil-pbc-exact-functor-complex-cohomology.

## Review by NP

I read the chapter and sk-prop-sf-cbc unit records, both paragraphs of the master's item proof, and the neighboring proper bounded-constructible and finite-reflection blueprint proofs. The unit has no listed proof steps to replace; the split keeps the item's localization, proper image, finite reflection and reconstruction route. I read Stacks etale-cohomology.tex Tag 095L (lemma-ses-associated-to-open), derived.tex Tag 015F (lemma-right-derived-exact-functor), sites-cohomology.tex Tags 07A5 and 0D6E, and morphisms.tex Tag 01T6 against those parts of the argument. The sheaf-to-cohomology calculation is the degreewise kernel/image/quotient calculation supplied by the cited exact-functor cohomology statement (homology.tex Tag 010N). I also read etale-cohomology.tex Tag 03RZ, which justifies the finite-coefficient constructible closure used by the existing derived-subcategory theorem; none of this uses non-torsion discrete or adic coefficients.

Step 1 uses exactly the finite-type-over-Noetherian statement and the affine finite-ring-map definition from def-weil-finite-integral-morphism. A field is Noetherian by its two ideals; a finite module list generates the algebra, so the finite morphism p has the finite-type hypothesis needed to obtain Noetherian Z. This step is elementary after the cited theorem.

Step 2 uses the whole ordinary-etale D^+ triangle statement of lem-cbc-open-closed-recollement, including its exact closed direct image. I checked that this statement is for finite commutative Lambda and arbitrary complementary immersions, and does not assume K bounded constructible. The module inverse-image theorem explicitly identifies pullback with inverse image for constant coefficients and makes it exact; the exact-derived-functor theorem explicitly states that every bounded below complex computes the derived functor. Thus C is Ri_*i^*K before we apply composition.

Step 3 uses lem-fin-extension-by-zero only on individual constructible cohomology sheaves, with its finite-type-over-k hypothesis on Y. The separate extension-by-zero exactness statement and exact-functor complex-cohomology statement give H^q(A)=a_!H^q(a^*K). Their quoted statements contain precisely those facts. No new lemma is needed for this three-line lifting to bounded constructible complexes.

Step 4 uses the additive-right-derived triangulated theorem in its actual generic abelian-category scope. Its K-injective-resolution hypothesis is supplied by prop-pur-kinjective-resolutions-exist, whose site-smallness condition is met by the explicit small-skeleton convention. The total-derived K-injective computation and the D^+ injective representative theorem, read together with the direct-image definition, make the identification with the bounded below Rb_* precise. Composition uses only clause (5) of lem-weil-derived-direct-image-composition: it explicitly covers ordinary etale modules over any commutative ring. I checked this clause instead of silently using the pro-etale A_E,n clause or the integral clauses. Every cited statement was opened and its used part copied to citations.json.

Step 5 uses lem-fin-proper-bounded-constructible with proper b, the same field base and finite coefficient convention, and the long-exact-cohomology theorem with the preceding distinguished triangle. If P and Q are supported in [u,v], H^n(Q) and H^{n+1}(P) vanish for n outside [u-1,v], proving boundedness of the cone first. Only then is the D^b triangulated-subcategory statement applied. This repairs the main ambient-category gap in the imported proof.

Step 6 uses the exact module pullback and exact-functor cohomology statements to retain the lower bound of K under i^*. The finite-reflection statement applies because p is finite by the item, S and Z are Noetherian by step 1, Lambda is finite commutative, and its derived image is bounded constructible by step 5. It states precisely reflection of D^b_c on ordinary etale derived categories; there is no surjectivity hypothesis to manufacture.

Step 7 uses exactness of the closed image from the recollement statement and the exact-functor cohomology statement, then lem-fin-closed-immersion only for sheaf constructibility. Y is of finite type over k, as that statement requires. The final long exact sequence proves the remaining bound on K, and the constructible-derived-subcategory statement proves constructibility after that bound. I did not infer exactness for all sheaves merely from the higher-vanishing clause for constructible sheaves.

For edge cases, Z empty gives the open-only case and the third term zero; G empty gives finite reflection with b=bi; K zero gives all zero triangles. For a finite p with empty geometric fibres, no claim about reflecting global surjectivity is used. Arbitrarily high cohomology on the finite boundary is ruled out by finite reflection, so the finite-boundary hypothesis is doing real work. The cohomology-bound calculation at u-1 and v is checked explicitly. The zero coefficient ring also gives the trivial zero categories. I checked every reused dependency for a path back to this item and found none, so the added foundational citations introduce no cycle.

Against delivery-errors B--E: there are no new statement-only-node, duplicate-node or invented Mathlib-leaf issues. The proof uses theorem statements, not constructions hidden inside their proofs; every non-elementary fact has a node citation and a verbatim supporting quotation. Off-unit inputs are declared as generic tool uses in split_report, without changing the chapter or unit route. The statement base clarification is reported above rather than silently weakening the statement. Mathlib searches were run only through msearch.py; LeanSearch returned Internal Server Error and is recorded unavailable, while two semantic phrasings, Loogle and two source greps found no reconstruction theorem.

## Second reading by NP

- Item statement: checked against the blueprint node and its source paragraph; the explicit field $k$ clarification preserves the intended finite-type hypotheses and the conclusion.
- Step 1: checked against `lem-weil-pbc-finite-type-over-noetherian` and `def-weil-finite-integral-morphism`; the Noetherian and finite-implies-finite-type deductions are elementary.
- Step 2: checked against `lem-cbc-open-closed-recollement`, exact inverse image, and exact-derived-functor statements; the $D^+$ triangle and identification with $Ri_*i^*K$ are supported.
- Step 3: checked against `lem-fin-extension-by-zero`, extension-by-zero exactness, and exact-functor cohomology; the degreewise constructibility and boundedness argument is explicit.
- Step 4: checked against the triangulated derived-functor, K-injective, direct-image, and composition nodes; the ordinary small-etale coefficient clause is the one used.
- Step 5: checked against proper bounded constructibility, the long exact cohomology sequence, and the triangulated constructible subcategory; boundedness of the cone is established before applying the $D^b$ result.
- Step 6: checked against exact inverse-image cohomology and `lem-fin-finite-reflects-derived`; all finite and Noetherian hypotheses are supplied by steps 1 and the coefficient convention.
- Step 7: checked against recollement exactness, closed-immersion constructibility, long exact cohomology, and the triangulated subcategory; the final cohomological bound and constructibility conclusion follow.
- New nodes: none; therefore B1--B7 and duplicate/Mathlib-leaf checks are vacuous. Existing-node searches covered the recollement, exact-functor, composition, finite-reflection, proper-image, and closed-immersion dependencies.
- Edge cases checked: empty boundary or open, zero complex, finite field base, and endpoint degrees $u-1$ and $v$; each gives the stated vanishing or trivial triangle.
- Changes made: none to the split files; the prior report's field clarification and replacement of insufficient citations are retained. Dry-run delivery passed preflight.
