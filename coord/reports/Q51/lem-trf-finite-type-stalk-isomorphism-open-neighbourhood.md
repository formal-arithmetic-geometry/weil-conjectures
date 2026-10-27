# Q51 stage-1 delivery

## Files written

- dag/nodes/sec-trace-formula/lem-trf-finite-type-stalk-isomorphism-open-neighbourhood.json: item, statement, split into seven steps; no exact Mathlib match.
- citations.json: one verbatim statement quotation for each of the 23 step/node citation pairs.
- searches.jsonl: actual search-command log, including the second semantic phrasing.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The split reuses existing results rather than duplicating them.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for stalk-isomorphism/local-isomorphism language found no declaration proving this item. The project's Mathlib/Morphisms/LocalIso results assume a local isomorphism and do not give the implication of this item.

## WANTED

None. The source is available locally.

## Source, statement and route

Read literature/stacks-project/varieties.tex, Tag 09NH (lemma-local-isomorphism), its entire statement and proof, and the following Tag 09NI argument. The item's statement matches 09NH with the variables renamed: finite type, reduced target, finitely many target components, and an isomorphism of the induced local ring map. No finite presentation, Noetherian condition, separatedness, or reducedness of the source is used. The identity of the local map, rather than a mere abstract ring isomorphism, is essential and is retained.

Read the chapter and sk-i-curve-zero unit records and the latest blueprint proof of lem-trf-local-term-locality. This item is a supporting algebraic-geometric lemma in the recorded 09NI dependency chain; its proof does not change the contracting-correspondence route of that blueprint node. No unit realization fields are applicable to this supporting node.

No statement dispute or source error was found. The imported item had no proof; the delivery supplies the denominator calculation. The source's two concluding assertions (surjectivity and injectivity) are expanded explicitly, including why the new denominator fprime avoids p. The inherited searches are preserved and fresh, logged searches with both phrasings have been appended. Read Mathlib/AlgebraicGeometry/Morphisms/LocalIso.lean and SpreadingOut.lean:335-360: neither is an exact or one-line specialization giving 09NH.

## Not duplicates

No new nodes were created. Whole-DAG tag/keyword searches and blueprint_refs.py searches for local isomorphism, stalk/isomorphism, minimal/prime and 09NH did not find a second node stating this item. The existing item and its parent are retained. The radical, minimal-prime, affine-stalk, component and principal-localization facts used below are all existing Mathlib leaves.

## Review by Q51

I checked the statement and complete proof against the local source Tag 09NH. For step 1 I read the statements of def-weil-irreducible-components, lem-sc-irreducible-components-cover, lem-sc-components-open-injection, lem-weil-pbc-affine-opens-basis, def-weil-finite-type-morphism, def-pc-reduced-scheme and lem-weil-pbc-spec-irreducible-components-minimal-primes. They respectively give closed maximal irreducible components, containment of every irreducible subset in a component, the component restriction to an open, an affine neighbourhood, an affine cover with finitely generated coordinate algebras, reduced section rings, and the precise V(r) description of spectrum components. Component restriction only asserts an injection: I did not assume its surjectivity. Instead I explicitly contain a component of U in a component of X and use maximality to obtain equality. The finite union of the discarded closed components is closed and misses x. An original component meeting the remaining open must contain x, which is exactly the input needed to put every minimal prime of A below p. The affine source chart is chosen from the finite-type cover itself, so no theorem about arbitrary affine restrictions of finite-type maps is silently used.

For step 2 I read def-weil-affine-spectrum, lem-weil-pbc-affine-open-stalk-localization and lem-weil-pbc-spec-map-stalk-localization. The first provides the ring-map/scheme-map dictionary, the second identifies the ambient stalks and germs, and the third states the actual local map a/s -> phi(a)/phi(s). Thus the map alpha used in all subsequent equations is the hypothesized map, not an unrelated isomorphism. Both charts contain the prescribed points and the image of q is p.

For step 3 I read the complete statements of def-weil-pbc-localization-at-prime, lem-weil-pbc-prime-contains-minimal-prime, lem-weil-pbc-zero-locus-eq-iff-radical-eq and def-pc-reduced-scheme. The localization definition explicitly gives the annihilator test for a zero fraction. The prime lemma is applied with I=0. The radical node explicitly gives the intersection formula, not merely equality of zero loci. Primality and the containment of every minimal prime in p imply that a zero numerator is in every minimal prime, then every prime, then is nilpotent and hence zero. This is a short elementary deduction from those cited statements, not an uncited assertion that reduced rings always inject into a localization at a prime (that assertion would be false).

For step 4 the cited prime-localization definition gives both fraction representations and the zero criterion, applied once for each of the finitely many algebra generators. I wrote the products of the denominators and annihilators and the corresponding numerators explicitly. No finite generation of a relation ideal is assumed. For step 5 I read def-weil-ring-localization-away and lem-weil-pbc-localization-away-universal-property: they give fractions with a single power denominator and the unique extended map. The finitely many generator equations put all of B, and specifically h, in the image. Since phi(f) and h avoid q, the comparison with B_q exists; the isomorphism of local rings then shows fprime avoids p. The maximal ideal of A_p is given in the prime-localization definition, so the unit test takes place in the correct local ring.

For step 6 the same localization definition and universal property give gamma. I checked that its image contains each generator and both inverses needed for every fraction of C: h inverse is f^N/fprime. For injectivity, the composite with B_q is the specified local map, and a fraction in its kernel has numerator zero by step 3. This argument requires only reducedness of A and imposes no reducedness on B. The denominator f fprime avoids p, so all maps in the comparison really exist. These elementary fraction calculations are written as steps rather than artificial new nodes.

For step 7 I read lem-weil-pbc-principal-localization-open-immersion, def-weil-affine-spectrum and def-weil-open-immersion. The principal-localization theorem gives the open subschemes as schemes (a topological homeomorphism alone would not suffice). The spectrum dictionary carries the actual A-algebra isomorphism gamma to an isomorphism over U, so its composite with the original inclusion is exactly the restriction of g. The definition of open immersion then gives the requested conclusion in X.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 of delivery-errors.md against the written item: all citations are existing unmerged nodes; every step has a Boolean elementary flag; the non-elementary tools have their full applicable statements; there is no newly invented lemma, clause restatement, or use of a cited proof instead of its statement. All proof steps are below 2000 characters. Every citation is copied verbatim into citations.json. The proof uses only Mathlib leaves and definitions off the item's unit, so no off-unit unsplit tool is substituted for its route. No SGA source is cited.

Edge cases checked: the zero-generator algebra case uses empty products equal to 1; a zero ring or empty source cannot have the specified point y; p may be minimal or maximal; several components may meet at x; the ambient source may have nilpotents away from y, which the annihilator product removes without a reduced-source assumption. No argument uses finite presentation or Noetherianity. No Lean was written and no compiler or build command was run.

## Unfinished work

None in the requested stage-1 split. Existing cited leaves are reused without modification. Server dry-run and delivery results are supplied by the delivery tool.
