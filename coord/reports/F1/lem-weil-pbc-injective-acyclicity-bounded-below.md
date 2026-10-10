Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-injective-acyclicity-bounded-below.json`: split item, 1 new node, no Mathlib leaves.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change.json`: statement-only unsplit node, Mathlib no match.
- `citations.json`: verbatim statement fragments for every proof dependency.

Attachments: none. The source declaration `AlgebraicGeometry.Etale.hasTorsionBaseChange_of_hasInjectiveAcyclicity` contains `sorry`, so it is not an attachment.

WANTED: none.

The item was a Lean split of the arbitrary-coefficient theorem in `BaseChangeProperty.lean`, lines 309-323. The declaration is not sorry-free. The imported item had no proof and had an unspecified blueprint location; I filled the location and recorded the Lean split note. I did not change the mathematical statement.

The proof is split at the real boundary in the source: the arbitrary-coefficient torsion-sheaf dévissage is a separate statement-only node, while the item carries the bounded-below complex argument. This avoids treating injective terms of a resolution as torsion without proof. The new node is strictly weaker than the item because it only treats a single torsion sheaf in degree zero.

## Review by F1

I read the item declaration and docstring in `WeilConjectures/SixFunctors/Etale/BaseChangeTheorems/BaseChangeProperty.lean` and compared them with Stacks Lemma 0A4B and Lemma 0DDE in `literature/stacks-project/etale-cohomology.tex`. The hypotheses retained in the item are: a commutative coefficient ring, proper `f`, arbitrary base-change morphism and cartesian square, torsion injective acyclicity on every pullback, and bounded-below `K` with torsion cohomology. The conclusion is the specified derived exchange isomorphism. The new node has the same geometric and coefficient hypotheses but restricts `K` to one torsion sheaf in degree zero, so it is not a restatement of the item.

Step 1 cites only the new node; its statement explicitly supplies the degree-zero exchange isomorphism under arbitrary-ring injective acyclicity. Step 2 cites the hypercohomology-filtration and truncation-couple definitions, the exactness of the truncation couple, triangulated derived exchange, exact inverse image, and the derived-exchange definition. I opened each cited statement and confirmed it supplies the corresponding spectral-sequence or functoriality fact. Step 3 uses the new node for each torsion cohomology sheaf and marks the remaining observation (the item hypothesis) elementary. Step 4 cites page induction and bounded-below hypercohomology convergence; these state that an `E_2` isomorphism persists and that the abutment filtrations are finite and exhaustive. Step 5 cites the exact-couple abutment identification and finite-filtration induction. Step 6 cites the derived-category criterion that an all-cohomology isomorphism is an isomorphism.

I checked the square hypotheses at Steps 1-2 and the bounded-below hypothesis at Step 4. The small cases tested were a degree-zero torsion sheaf (Step 1) and a complex concentrated in one degree (Steps 2-3); both reduce to the new sheaf-level node. I searched the whole DAG and blueprint for the arbitrary-coefficient torsion-sheaf statement and found no existing node or blueprint duplicate. I ran LeanSearch, Loogle, LeanFinder, and Mathlib grep for both the item and the new node; LeanSearch was unavailable, while the other searches found no matching theorem. No source or statement correction was made beyond filling the blueprint location and making the coefficient dévissage boundary explicit.

## Not duplicates

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lemma-weil-pbc-property-iff-acyclicity`: the existing node compares PBC and IA only for prime coefficients; the new node gives the IA-to-exchange implication for torsion sheaves over an arbitrary coefficient ring.

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lemma-weil-pbc-torsion-assembly`: the existing node assembles a known exchange property from prime and finite torsion sheaves; the new node includes injective acyclicity as the hypothesis and concludes the exchange property.

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lem-weil-pbc-injective-acyclicity-bounded-below`: the existing item concerns arbitrary bounded-below complexes with torsion cohomology; the new node concerns only one torsion sheaf in degree zero and is the input to the complex argument.

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lem-weil-pbc-pullback-iso-prime-torsion-devissage`: the existing node is a global-sections pullback theorem assuming prime-torsion bijectivity; the new node is a derived direct-image exchange theorem deduced from injective acyclicity over an arbitrary ring.

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lem-weil-pbc-property-implies-acyclicity`: the existing node proves PBC implies IA; the new node proves the converse implication for torsion sheaves under IA.

`lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change` vs `lem-weil-pbc-inverse-image-preserves-colimits`: the existing node states colimit preservation by inverse image, which is only an ingredient of dévissage; the new node concludes the base-change isomorphism.

## Second reading by F1

- Item statement: checked against Stacks Lemmas 0A4B and 0DDE and the Lean declaration; verdict: hypotheses and bounded-below derived exchange conclusion are retained.
- New node `lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change`: checked against the dévissage paragraphs of 0A4B and the project's arbitrary-coefficient injective-acyclicity definition; verdict: strict degree-zero specialization, self-contained, and no Mathlib match.
- Step 1: checked against the degree-zero torsion-sheaf dévissage in 0A4B; verdict: uses the new node for exactly the needed exchange isomorphism.
- Step 2: checked against the truncation spectral-sequence construction in 0DDE and the cited exact-couple, inverse-image, and exchange statements; verdict: all construction and functoriality facts are cited.
- Step 3: checked against the post-`E_2` identification in 0DDE; verdict: torsion cohomology supplies the new node's hypothesis, with the remaining observation elementary.
- Step 4: checked against page induction and bounded-below convergence in 0DDE; verdict: pagewise and finite-filtration claims match the cited nodes.
- Step 5: checked against the abutment-filtration argument in 0DDE; verdict: the cited abutment and finite-filtration lemmas give the cohomology isomorphisms.
- Step 6: checked against the final derived-category criterion; verdict: all cohomology isomorphisms imply the derived exchange isomorphism.

Changes made: confirmed the two worker node files in the sandbox delivery tree and added this audit section; no mathematical statements or proof steps required repair.
