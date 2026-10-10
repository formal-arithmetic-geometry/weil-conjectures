1. Files written:

   - `dag/nodes/sec-smooth-purity/lem-pur-hom-kflat-into-kinjective.json`: statement node, split; no Mathlib match.
   - `citations.json`: verbatim citations for the item proof.

2. Attachments: none.

3. WANTED: none; `/home/ubuntu/c1-stacks-review/sites-cohomology.tex` was available for the cited Stacks lemma.

## Review by C1

   I read the item statement and its source, Lemma 0A96 (`lemma-RHom-from-K-flat-into-K-injective`) in `sites-cohomology.tex`, and checked the no-sorry project source for the item tag and key notions. No exact declaration exists. I read the existing statements of `def-pc-kflat-complex`, `def-pur-kinjective-complex`, and `def-pur-hom-complex`; they provide exactly the K-flat test, the K-injective Hom-acyclicity test, and the Hom-complex differential used in the proof. The Stacks proof's signed total-complex tensor-Hom identity is kept as the explicit termwise calculation in Step 2 rather than made into a child, because it is a clause of this item and the delivery preflight rejects such a restatement as a duplicate. Step 1 invokes the K-flat definition, Step 2 expands the tensor-Hom bijection and signs, and Step 3 invokes the K-injective definition; every cited statement says the fact taken from it, and the hypotheses (site, sheaf of commutative rings, acyclic test complex, K-flat source, K-injective target) are all present. Mathlib searches found only general group-valued HomComplex/mapBifunctor and K-injective declarations, not the sheaf statement; LeanSearch for the item was unavailable and is recorded as such.

## Not duplicates

lem-pur-hom-kflat-into-kinjective vs lem-pur-rhom-global-sections: the former proves K-injectivity of a Hom complex from K-flat to K-injective, while the latter identifies global derived Hom with morphisms in the derived category and only cites the former.

lem-pur-hom-kflat-into-kinjective vs def-pur-hom-complex: the item is a K-injectivity theorem about the Hom complex; the existing node only defines its terms and differential.

5. Nothing remains unfinished in the split.

## Second reading by C1

- Item statement: checked against Stacks `sites-cohomology.tex`, Lemma 0A96 (`lemma-RHom-from-K-flat-into-K-injective`); verdict: hypotheses and conclusion match.
- Step 1: checked against Definition `definition-K-flat` and the acyclic test-complex hypothesis; verdict: valid and elementary.
- Step 2: checked against the termwise Hom-complex definition and the total tensor-complex definition, including the $(-1)^p$ total differential; verdict: valid explicit calculation.
- Step 3: checked against the K-injective definition and the source proof's $H^0(\Gamma(\mathcal Hom))=\operatorname{Hom}_{K(\mathcal O)}$ identification; verdict: repaired from the incorrect claim that the Hom complex itself is acyclic.
- New node `lem-pur-hom-kflat-into-kinjective`: self-contained, source tag and label checked, no duplicate or exact Mathlib declaration found; verdict: retained.

Changes: added the tensor-complex citation to Step 2 and its verbatim citation record; rewrote Step 3 to prove vanishing in the homotopy category via degree-zero cocycles and null-homotopies, matching Stacks Lemma 0A96.
