## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-point-morphism-classification.json`: statement, corrected and split into five steps; no exact Mathlib match.
- `citations.json`: twelve step/node entries with verbatim quotations from the statements read.
- `searches.jsonl`: six actual searches for the corrected classification; the imported search records remain in the item.

New nodes: 0. Mathlib leaves: 0. No unit record was changed: this item is not the unit's key node.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact blueprint tag and item id, geometric-point morphisms, stalk natural transformations and strict-local lifts found no declaration stating the item. The finite-etale group-scheme point declarations do not classify morphisms of topos points. The upstream master was not treated as finished evidence.

## WANTED

None. The proof uses the available Stacks source and existing DAG statements.

## Statement corrected

STATEMENT-DISPUTED: the original item is ill-typed and false. It writes `a composed with bar y = bar x`, although the displayed domains require `bar y composed with a = bar x`. Fixing the order does not repair its claimed bijection or its claim that all point morphisms are invertible.

The source itself contradicts that claim. I read `etale-cohomology.tex`, Tag 04FN (`remark-map-stalks`), including its last paragraph: geometric-field maps give isomorphisms of stalk functors, but more general morphisms of points correspond to specializations and need not be isomorphisms. Tag 04HU classifies objects, not all their arrows. I also read Tag 0GJ2 (`section-specialization`), the actual construction and germ formula, and `sites.tex` Tags 00YH (`lemma-maps-u-points`) and 00YI (`definition-morphism-points`) for the opposite direction of the fibre transformation.

Two counterexamples distinguish the two errors.

1. Noninjectivity even with the same support: take `S = Spec C`, `Omega = algebraic closure of C(u)`, and both geometric points `Spec Omega -> S`. The automorphism `u -> u+1` of `C(u)` extends to an automorphism of its algebraic closure and fixes C. Its spectrum and the identity are distinct S-morphisms. Every etale C-scheme is a disjoint union of copies of Spec C; its lifts from Spec Omega are just its components. Both automorphisms act identically on those lifts, hence on every germ of every etale sheaf. Thus the purported injection already fails on a fixed-support fibre.
2. Nonsurjectivity and failure of general invertibility: take `S = Spec C[[t]]`, the closed geometric point `bar s = Spec C`, and a geometric generic point `bar eta = Spec overline(C((t)))`. The ring is strictly henselian, so its strict localization at `bar s` is S. The generic lift into S gives the specialization arrow `p_eta -> p_s` of 0GJ2. For the representable sheaf of the open `D(t)`, the closed stalk is empty and the generic stalk is a singleton. The mate is the nonbijective map from the empty set to a singleton. No S-map between the displayed geometric spectra can induce this arrow, since such a map would force equal supports.

The corrected statement classifies all 2-morphisms by natural transformations of the geometric lift functors, equivalently compatible neighbourhood lifts and maps into the target strict localization. Its explicit formula retains exactly the source's map on represented germs. The final assertion retains invertibility for genuine geometric-field maps; it makes no false claim that all arrows come from such maps. This is the source's intended point-arrow notion, rather than an added hypothesis hiding the counterexamples.

## Impact on existing nodes and metadata

The only direct citer found is `lem-trf-etale-point-support-fibre`. Its statement about the fixed-support subcategory may still be true, but its steps 1 and 3 use the false field-map classification and do not survive this correction. The noninjectivity example above applies even to that fixed-support situation. Step 3 also treats an etale neighbourhood of Spec kappa(s) as an etale S-scheme after composition with the residue-field inclusion; that composite need not be etale. The parent's proof needs an independent comparison of the two lift-functor categories or their strict localizations. Its use of the classification must be updated by the maintainer/owner. I did not edit that node.

The item's title and `source` are maintainer-owned and were preserved byte for byte. Suggested title: “Etale point 2-morphisms classified by compatible geometric lifts.” Suggested source place: “etale-cohomology.tex Tag 0GJ2, section-specialization; Tag 04FN, remark-map-stalks; sites.tex Tags 00YH and 00YI. The bijective converse is supplied by lem-trf-point-arrows-strict-local-lifts, not by 04FN or 04HU.” In particular the old source's phrase asserting converse uniqueness on the original geometric fields should be removed. The correct source places are already in each proof step and in `proof_origin`.

The imported blueprint ancestry contained the item itself as its sole `via` entry. I repaired it to follow its actual parent and that parent's existing ancestry, retaining the ancestor `lem-trf-local-term-locality`. The recorded place now refers to the current main-20261015 proof, paragraphs (1)--(2), and the subsidiary fixed-support calculation. Neither the chapter route nor the unit's two steps changes.

## Not duplicates

No new nodes were created. The existing reviewed `lem-trf-point-arrows-strict-local-lifts` supplies the hard classification and germ formula, and is cited rather than recreated. The present item's remaining work identifies that classification with natural lift transformations and compatible families, then identifies the genuine-field-map subcase. The existing `lem-weil-pbc-geometric-point-morphism-stalk-bijection` supplies exactly that subcase and makes no converse assertion.

Whole-DAG searches used the item id, geometric point, strict localization, compatible lifts, point morphisms and the tags 04FN/0GJ2; blueprint searches used “geometric point”, “strict localization” and “morphisms of points”. There is no imported blueprint node stating the corrected full classification. The existing strict-local arrow node was read in full, including its statement, proof and reviewed record.

## Mathlib searches

All six fresh searches ran through the prescribed msearch.py command. The log contains both semantic phrasings, a Loogle query, two greps and LeanSearch. LeanSearch was unavailable because of a rate limit and is recorded as unavailable. LeanFinder found generic point-fibre maps and fully faithful forgetful functors for etale schemes; those are different assertions. Loogle found Point.Hom.sheafFiber and related functoriality lemmas. I read Mathlib/CategoryTheory/Sites/Point/Category.lean:39–95 and AlgebraicGeometry/Sites/EtalePoint.lean:64–114. The former constructs transformations from site-point arrows; the latter constructs geometric points. Neither classifies abstract topos 2-morphisms by strict-local lifts. Thus these hits are not exact matches or one-line specializations of the corrected item.

## Review by Q03

I checked the five delivered steps against their cited statements, not the proofs hidden behind them. For step 1 I read the entire statement of `lem-trf-point-arrows-strict-local-lifts`: it explicitly gives both the Hom-set bijection and the formula using the neighbourhood projections, with arbitrary algebraically closed geometric fields. Its assumptions match ours without normality, finite type, common support or an algebraicity assumption on either geometric field. I read `lem-fix-geometric-stalk-topos-point`, whose etale case supplies the actual point with the stated stalk inverse image. The latter is declared as a generic tool from another unit.

For step 2 I checked the small representative category and inverse-limit assertion in `def-weil-pbc-strict-henselization-limit`, and the exact description of rho in `def-weil-pbc-strict-henselization-structural-map`. Maps over S are exactly cones of S-maps, because composing any projection with its structure map gives rho. The full statement of `lemma-weil-pbc-affine-neighbourhood-cofinal` supplies an affine source for every neighbourhood; it does not say overlaps are affine, and the argument never assumes that. The cofiltered-neighbourhood statement supplies common sources and equalizers of parallel pointed arrows; I checked all three clauses. Refining again to an affine source makes the two family values comparable, proves independence, and proves compatibility. This step is a routine use of those universal properties, not an unstated prorepresentability theorem. Smallness is fixed by the universe convention and the strict-local definition's representative category.

For step 3 I checked the definition of a pointed arrow in `def-weil-pbc-pointed-etale-neighbourhoods`. The two displayed equations prove both directions and both inverse identities for the family/natural-transformation correspondence. It needs no separate theorem about extending natural transformations from generators. Empty lift sets impose only the unique empty function, so no hidden nonemptiness is used.

For step 4 I checked that the existing strict-local arrow statement gives the formula for every etale U, including nonaffine U, and for every represented germ of every set sheaf. The stalk definition supplies the opposite-indexed colimit. The direct-image convention and reversed inverse-image mate are precisely the last clauses of `def-trf-geometric-morphism`. Hence no fully-faithful-Yoneda statement is being used as though it were the general Yoneda lemma, and no arbitrary abstract point-reconstruction theorem is needed.

For step 5 I read `lem-weil-pbc-geometric-point-morphism-stalk-bijection`: its hypothesis is precisely bar y composed with a equals bar x, and it gives the unique map with this germ formula and its bijectivity for every set sheaf. It does not give the false converse. Componentwise inversion gives a natural inverse, as written out, and the mate clause of the geometric-morphism definition gives an invertible 2-morphism. This other-unit theorem is declared as a generic tool, separately from classification.

I tested the corrected statement on Spec of an algebraically closed field, unequal transcendence degrees of geometric fields, the generic-to-closed specialization of the strictly henselian trait, empty fibres and empty etale objects. These tests respectively retain a unique topos arrow despite many field maps, require no field embedding between the original fields, allow noninvertible arrows, and introduce no spurious element. All twelve uses have actual statement quotations in citations.json. The three other-unit tools are declared in split_report. No new statement-only nodes, hollow definitions, renamed clauses or duplicated support lemmas were introduced. The longest step has 1158 characters, so there are no non-elementary steps over the 2000-character threshold. Traversing the current 167-node dependency closure found no path back to the item. The source route uses Stacks only; no prohibited source is cited.

## Unfinished work

The assigned corrected split is complete. The separate parent-proof repair and the maintainer-owned title/source metadata are reported above; they are outside this item's authorized files.
