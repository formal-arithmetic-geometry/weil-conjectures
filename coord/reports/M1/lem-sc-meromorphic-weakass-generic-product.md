1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-meromorphic-weakass-generic-product.json` (item, split; Mathlib no match).
- `dag/nodes/sec-abelian-varieties/lem-sc-affine-weakass-nonzerodivisors.json` (statement, unsplit; Mathlib no exact match).
- `dag/nodes/sec-abelian-varieties/lem-sc-affine-totalquotient-minimal-product.json` (statement, unsplit; Mathlib no match).
- `citations.json` (verbatim citations for every non-elementary proof dependency).

2. Attachments: none. No declaration tagged `(blueprint: lem-sc-meromorphic-weakass-generic-product)` or otherwise matching the item was found in `WeilConjectures/`.

3. WANTED: `literature/stacks-project/divisors.tex`, Tag 0EMF (Lemma 31.24.6), for `lem-sc-meromorphic-weakass-generic-product`; the local literature checkout contains only citation indexes, so I read the official Stacks page online and recorded the proof in `proof_origin.by = agent`.

4. No statement correction was made. The imported item had no proof; its existing `stmt_deps` match the objects used by the statement. The split follows the source's affine argument and does not restate a clause as a child node. The two new children are strictly smaller affine algebra inputs and were searched in the DAG and blueprint before creation; no duplicate was found.

## Review by M1

I checked the item against Stacks Tag 0EMF (official online Lemma 31.24.6, whose statement gives both the generic-point product for `K_X` and the quasi-coherent-module version). The item hypotheses are exactly the two source hypotheses: weakly associated points are generic component points, and quasi-compact opens have finitely many irreducible components. I also checked the two new statements against Algebra Tags 10.66.7 and 10.25.4: the first is the zero-divisor/weakly-associated-prime criterion, and the second is the total quotient decomposition under finitely many minimal primes and the weak-assumption.

Step 1 uses precisely those two child statements. The remaining affine observations are elementary translations: irreducible components of `Spec(A)` correspond to minimal primes, and the item hypotheses give their finiteness and the weak-assumption. Step 2 is the affine-basis identification: `j_eta^{-1}(Spec A)` is `Spec(A_q)` for the corresponding minimal prime, and equality on affine opens glues. Step 3 expands the source's tensor argument; finiteness makes tensor commute with the displayed product, and localization of the affine module is the generic stalk. I checked empty affine opens and the one-component integral case separately; both reduce to the same formulas (the empty product is the zero ring/module, and for one minimal prime the product has one factor). No cited node is used for a fact absent from its statement, and `citations.json` quotes the exact statements used by Step 1.

5. Unfinished work: none for this stage. The required dry run is the remaining mechanical check.

## Second reading by M1

- Item statement: checked against Stacks Tag 0EMF (Lemma 31.24.6), including hypotheses (a), (b), the product over generic points, and the quasi-coherent-module clause; verdict: agrees with the imported target statement.
- Step 1: checked against Tag 0EMF's affine reduction and Algebra Tags 0546 and 02LX; the two cited child statements supply the zero-divisor criterion and total-quotient product, while the affine component/minimal-prime identifications are elementary; verdict: sound.
- Step 2: checked against Tag 0EMF's affine pushforward identification and restriction/gluing argument; the inverse image of an affine open under the generic-point map is the corresponding localization spectrum, and opens are stable under generalization; verdict: elementary and sound.
- Step 3: checked against Tag 0EMF part (2); the finite product tensor calculation and localization of a quasi-coherent module give the displayed factors, with restriction compatibility; verdict: elementary and sound.
- New node `lem-sc-affine-weakass-nonzerodivisors`: checked against Algebra Tag 0546, including the definition of WeakAss and the zero-divisor conclusion; tested on a field, a domain, and the zero ring; verdict: self-contained and correct.
- New node `lem-sc-affine-totalquotient-minimal-product`: checked against Algebra Tag 02LX with Tag 0546's hypothesis; tested on a field, a domain, and a two-minimal-prime product ring; verdict: correct and strictly smaller than the item.

Changes made:

- Removed the incorrect dependency from the weak-association child: the locally Noetherian Ass/WeakAss comparison node does not define the ring notion, so the definition is now written directly in the statement.
- Replaced section-style algebra citations with the exact Stacks tags and labels (0546 and 02LX).
- Corrected the item node's `created.item` metadata, which named a different item.

## Not duplicates

- `lem-sc-affine-totalquotient-minimal-product` vs `lem-weil-pbc-popescu-reduce-to-field`: the latter is a theorem about reducing Popescu's property from general Noetherian base rings to fields; it does not state a total-quotient decomposition and only cites Tag 02LX inside its proof.
- `lem-sc-affine-totalquotient-minimal-product` vs `lem-weil-pbc-reduced-noetherian-total-ring-fractions`: the existing node assumes a reduced Noetherian ring and concludes each factor is a field, whereas this node applies to arbitrary commutative rings with finitely many minimal primes whose weakly associated primes contain all zero-divisors and concludes the product of localizations; neither statement specializes to the other under the item's hypotheses.
