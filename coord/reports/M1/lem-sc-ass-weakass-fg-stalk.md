1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-ass-weakass-fg-stalk.json`: item split; two proof steps; no Mathlib match.
- `citations.json`: verbatim citation for the stalk-definition step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/divisors.tex`, Tag 05AR (Lemma 31.5.8) and its cited Algebra Lemma 10.66.9, because the checked-out literature contains only citation metadata and not the TeX source.

4. The original item had no proof. I kept its statement and definitions and wrote Tag 05AR’s two implications directly as proof steps, avoiding a separate node that would merely restate a clause of this item. Mathlib searches found associated-prime declarations but no weakly-associated notion or equivalence. The non-elementary converse is recorded in the item step itself, following the finite-generator colon argument cited by Tag 05AR to Algebra Lemma 10.66.9.

5. Nothing remains unfinished in the split.

## Second reading by M1

- Item statement: checked against divisors.tex Tag 05AR, Lemma 31.5.8, including the scheme, quasi-coherent module, point, stalk, and finitely generated maximal-ideal hypotheses; verdict: agrees.
- Step 1: checked against the stalk definition node and the setup of Tag 05AR; verdict: the local ring/module translation is exactly what the cited node states.
- Step 2: checked directly from the annihilator and minimal-prime definitions; verdict: associated implies weakly associated is elementary.
- Step 3: checked against Algebra Lemma 10.66.9, Tag 058A, and the new prime/module statement; verdict: the converse now cites the finite-generator algebra theorem and adds no Noetherian hypothesis.
- New node `lem-sc-ass-weakass-fg-prime`: checked against algebra.tex Tag 058A, with the definitions of associated and weakly associated written inline and the module context cited; verdict: strict supporting statement, no duplicate found in the DAG, and Mathlib searches found no match.
- Changes: corrected the new node's `created.item`; added the Tag 058A supporting node because the finite-generator converse is not elementary; changed the converse step from an uncited "standard colon argument" to an explicit application of that node; updated `proof_deps`, citations, and the split summary.
- Edge cases rechecked: the zero module makes both predicates false for a proper maximal ideal, while over a field with maximal ideal `(0)` the module's nonzero elements witness both predicates; the equivalence does not assert existence of a witness.

## Review by M1

I checked the item against the stated Tag 05AR location and the surrounding use in `lem-sc-ass-weakass-locally-noetherian`; the item’s hypotheses are exactly a scheme, a quasi-coherent module, a point, and finite generation of the local maximal ideal. I read the existing stalk definition node and used only its assertion that a scheme module stalk is an `O_{X,x}`-module in step 1. Step 2 is the direct annihilator-to-minimal-prime implication and is elementary. Step 3 writes the finite-generation/colon argument cited by Tag 05AR to Algebra Lemma 10.66.9, with `R = O_{X,x}`, `M = F_x`, and `p = m_x`; no unstated Noetherian hypothesis is added. I tested the formulation on the zero module (both predicates are false for a proper maximal ideal) and on a field with `p = (0)` (both predicates hold for the module itself), so the equivalence does not accidentally assert existence. I searched the DAG for Tags 05AR, 02OJ, 0546, and the relevant associated/weak-association terms and found no duplicate clause node. The Mathlib searches recorded for the item found only unrelated associated-prime API declarations; LeanSearch was unavailable, while LeanFinder, Loogle, and grep ran successfully.
