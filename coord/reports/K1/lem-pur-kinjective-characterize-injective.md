Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-kinjective-characterize-injective.json`: statement split into the five-step Stacks 079G proof; no new nodes.
- `citations.json`: verbatim citations for every non-elementary dependency used by the steps.

Attachments: none.

WANTED: none.

The item had no exact sorry-free declaration in `WeilConjectures/`; the source tree search for the item id, `lemma-characterize-injective`, and generator/injective criterion terminology found no attachment. The local repository does not include the fetched Stacks tex source, but the node's imported source and place identify `injectives.tex`, Lemma 19.11.6 (Tag 079G). The proof follows that lemma exactly: the forward implication is the injective definition; the converse uses a Zorn maximal extension, exact filtered colimits for chain upper bounds, and the generator to enlarge a proper maximal subobject via an image/intersection and gluing argument.

## Review by K1

I checked the item statement against Stacks Tag 079G, including the hypotheses that the category is Grothendieck abelian, that U is a generator, and that the conclusion quantifies over every subobject M of U. I read the existing statements of `def-sp-grothendieck-abelian` and `def-sp-injective-resolutions`: the former supplies small colimits, a generator, and exact filtered colimits, while the latter supplies the Hom-surjectivity definition of injective. Step 1 uses only that injective definition. Step 2 uses the exact filtered-colimit clause to make the colimit of a chain of subobjects a subobject and uses Zorn's lemma. Step 3 uses the generator clause to choose psi and forms the image intersection N and inverse image M, then applies the item's assumed extension property. Step 4 is the elementary abelian-category factorization through an image and gluing on a sum; the vanishing on Ker(psi) follows directly because the map on M factors through psi. Step 5 invokes the injective definition to conclude from the arbitrary mono A -> B. I tested the edge cases M = 0 and M = U (both extension conditions are immediate) and the trivial category, where the criterion is vacuous and the unique object is injective. The Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; LeanFinder/Loogle/grep found no generator Baer criterion and LeanSearch was unavailable.
## Second reading by K1

- Item statement: checked against `injectives.tex`, Lemma 19.11.6, Tag 079G (`lemma-characterize-injective`); the Grothendieck abelian, generator, subobject, extension, and injectivity hypotheses agree exactly.
- Step 1: checked against Tag 079G and `def-sp-injective-resolutions`; the forward implication is precisely the injective lifting definition and is elementary.
- Step 2: checked against Tag 079G and `def-sp-grothendieck-abelian`; the poset, chain colimit upper bound, exactness of filtered colimits, and Zorn maximal pair are the stated argument.
- Step 3: checked against Tag 079G and the generator definition in Tag 079B; the required non-factoring map is now cited through the new support node, and the inverse-image/intersection objects have the stated types.
- Step 4: checked against Tag 079G and abelian-category image/kernel/sum definitions; the kernel vanishing, image factorization, agreement on the intersection, gluing, and strict enlargement are elementary categorical steps.
- Step 5: checked against Tag 079G and `def-sp-injective-resolutions`; maximality gives an extension for an arbitrary monomorphism, exactly the converse injectivity condition.
- New node `lem-pur-kinjective-generator-detects-proper-subobject`: checked against Tag 079B, label `definition-grothendieck-conditions`; it is self-contained, uses only cited abelian/Grothendieck definitions, has TeX notation, and records the three Mathlib searches (no exact match).
- Edge cases: tested $M=0$, $M=U$, the zero category, and the one-object abelian category; the criterion is vacuous or immediate in each case, as expected.
- Changes: added the generator-detection support node because `def-sp-grothendieck-abelian` names but does not state the generator's detecting property; cited it in Step 3, added its verbatim citation, and recorded its searches. No statement weakening or source change was made.

## Not duplicates

- `lem-pur-kinjective-generator-detects-proper-subobject` vs `lem-weil-pbc-ring-modules-grothendieck-abelian`: the new node is the general generator axiom for arbitrary abelian categories, while the existing node is the specialized assertion for `Mod(R)` and its concrete generator `R`; the latter does not state the general criterion needed by this item.
