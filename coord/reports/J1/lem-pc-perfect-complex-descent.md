# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-perfect-complex-descent.json` — repaired item split.
- `dag/nodes/sec-picard-framework/lem-pc-affine-perfect-colimit-descent.json` — corrected statement-only affine child; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-two-open-gluing.json` — new statement-only two-open gluing node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-perfect-descend-morphisms.json` — new statement-only full-faithfulness/descent node; no Mathlib match.
- `citations.json` — verbatim citations for every proof-step use.

2. Attachments: none; no sorry-free project declaration states the item or either new node.

3. WANTED: `literature/stacks-project/perfect.tex`, Lemma 36.29.3 (Tag 09RF) and lemma-descend-homomorphisms; `literature/stacks-project/cohomology.tex`, two-open lemma-glue; `literature/stacks-project/more-algebra.tex`, lemma-colimit-perfect-complexes. These source files are absent from this checkout; the cited places are recorded from the project metadata and returned review.

4. The returned version incorrectly assumed finite affine overlaps and a triple cocycle in a derived category. Such hypotheses are not supplied when the finitely presented scheme is only quasi-separated. I replaced that child by two-open gluing, added full-faithfulness/descent of overlap morphisms, and rewrote the item proof as the finite-affine-cover induction of Tag 09RF. I also changed the affine child so the filtered system of coordinate rings is given and only the bounded finite-projective complex is descended, as required by More on Algebra, lemma-colimit-perfect-complexes. The duplicate and false gluing statements were removed.

## Review by J1

I read the returned item and all three affected child files, the parent blueprint reference, the definitions of scheme, derived category, and perfect complex, and the source places named in the return. Step 1 uses only the finite affine reduction and the local bounded finite-projective description of a perfect object. Step 2 uses the corrected affine child with the actual coordinate-ring system supplied by the affine open; its finite coefficients and equations can be synchronized at one filtered stage. Step 3 uses the full-faithfulness node for the overlap isomorphism, its inverse, and inverse identities, then uses the two-open gluing node; no affine-overlap or triple-cocycle assertion is used. I verified that the two-open node has no separatedness hypothesis and that every non-elementary statement used by the steps appears verbatim in `citations.json`. I reran the required Mathlib searches for each new node; all returned no match.

## Not duplicates

`lem-pc-perfect-two-open-gluing` vs `lem-sc-derived-open-gluing`: the former specializes Tag 08DG to quasi-compact open subschemes and includes the nontrivial conclusion that the glued object is perfect; the latter is the generic ringed-space derived gluing statement and does not assert perfectness.

`lem-pc-affine-perfect-colimit-descent` vs `lem-pc-perfect-complex-descent`: the child concerns one given filtered system of affine rings and one bounded finite-projective complex, while the item concerns a perfect derived object on a finitely presented scheme and its finite-cover induction.

`lem-pc-perfect-two-open-gluing` vs `lem-pc-perfect-complex-descent`: the child is a conditional two-open gluing theorem for already descended perfect objects; the item additionally descends local complexes and overlap morphisms along a filtered colimit.

`lem-pc-perfect-descend-morphisms` vs `lem-pc-perfect-complex-descent`: the child only descends morphisms and finite equalities between already given perfect complexes; the item constructs a descended perfect object.

`lem-pc-perfect-two-open-gluing` vs `lem-pc-perfect-descend-morphisms`: gluing constructs an object from two local objects and an overlap isomorphism, whereas full faithfulness produces the overlap morphism at a finite stage.

`lem-pc-perfect-two-open-gluing` vs `lem-pc-noetherian-approximation-data`: the gluing node has fixed two-open perfect objects and no scheme or module approximation conclusion, while the existing node simultaneously approximates a scheme, modules, and a perfect object.

`lem-pc-perfect-descend-morphisms` vs `lem-pc-noetherian-approximation-data`: the morphism node states only full faithfulness and descent of finite equalities for given perfect complexes, while the existing node states a broader noetherian approximation package.

5. Nothing remains unfinished in the split; the dry run is the remaining verification.

## Second reading by J1

- Item statement: checked against Derived Categories of Schemes Lemma 36.29.3, Tag 09RF; the filtered-colimit, finitely presented scheme, and perfect-object hypotheses and conclusion are the stated specialization.
- Step 1: checked against the finite affine reduction and induction in Tag 09RF; finite affine covers exist for the quasi-compact finitely presented scheme, and the zero/one-open cases reduce to the affine case.
- Step 2: checked against Tag 09RF and More on Algebra Lemma 15.76.18, Tag 0BC7; only bounded local complex coefficients and differential equations are synchronized, while overlap morphisms are deferred to Step 3.
- Step 3: checked against Derived Categories of Schemes Lemma 36.29.2, Tag 09RE, and Cohomology of Sheaves Lemma 20.45.1, Tag 08DG; the overlap isomorphism, inverse, and inverse identities descend together before two-open gluing. Quasi-compact overlaps are allowed even when affine overlaps are not.
- New node `lem-pc-affine-perfect-colimit-descent`: checked against More on Algebra Lemma 15.76.18, Tag 0BC7; statement is self-contained, statement-only, and tested on the zero complex and a one-term finite projective complex.
- New node `lem-pc-perfect-descend-morphisms`: checked against Derived Categories of Schemes Lemma 36.29.2, Tag 09RE; the finite family of equalities gives the isomorphism specialization, and the statement is self-contained and statement-only.
- New node `lem-pc-perfect-two-open-gluing`: checked against Cohomology of Sheaves Lemma 20.45.1, Tag 08DG; it specializes two-open derived gluing to quasi-compact open subschemes and asserts perfectness of the glued object, which the existing generic ringed-space node `lem-sc-derived-open-gluing` does not state. The empty and one-open cases are vacuous/trivial.
- Changes: removed overlap restriction morphisms and inverse equations from Step 2 because the affine child does not provide them; corrected the source records for the retained children to include Stacks tags and labels; restored the specialized same-unit gluing node and updated Step 3 and citations to use it.
