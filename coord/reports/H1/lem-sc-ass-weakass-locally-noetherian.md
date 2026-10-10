1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-ass-weakass-locally-noetherian.json` (item, split).
- `dag/nodes/sec-abelian-varieties/lem-sc-ass-weakass-fg-stalk.json` (statement-only node, Mathlib no match).
- `dag/nodes/sec-abelian-varieties/lem-sc-locnoeth-stalk-maxideal-fg.json` (statement-only node, Mathlib no match).
- `citations.json` (verbatim step citations).

2. Attachments: none.

3. WANTED: `literature/stacks-project/divisors.tex`, Tag 05AR source text is not present in this checkout; the online Stacks page confirms the cited statement and proof reference to Algebra Lemma 10.66.9.

4. The imported item was unsplit and had no proof. I retained its statement and dependencies. The split follows Tag 05AR: first establish finite generation of each stalk maximal ideal on a locally Noetherian scheme, then apply the stronger finitely generated-stalk equivalence to `O_X`.

5. Nothing remains unfinished after the dry run; the two child nodes are intentionally statement-only stage-1 leaves because their source results are not formalized in Mathlib here.

## Not duplicates

lem-sc-ass-weakass-fg-stalk vs lem-sc-ass-weakass-locally-noetherian: the new node is the first, stronger assertion of Tag 05AR for an arbitrary scheme, quasi-coherent module, and point with finitely generated maximal ideal; the item is only the locally Noetherian structure-sheaf specialization.
lem-sc-locnoeth-stalk-maxideal-fg vs lem-sc-ass-weakass-locally-noetherian: the new node states only finite generation of each stalk maximal ideal, which is a hypothesis bridge and does not assert any equivalence of associated-point sets.

## Review by H1

I checked the item against Stacks Project Tag 05AR (Lemma 31.5.8). Its first assertion states the equivalence for a quasi-coherent module whenever the local maximal ideal is finitely generated, and its final assertion gives the locally Noetherian specialization. The new node `lem-sc-ass-weakass-fg-stalk` reproduces the first assertion with all objects introduced; `lem-sc-locnoeth-stalk-maxideal-fg` records the final specialization needed by the item. The item hypotheses provide a locally Noetherian scheme and its quasi-coherent structure sheaf, so step 1 applies the second child at every point and step 2 applies the first child to `O_X`. I opened both child statements and the citation quotes are verbatim. I searched the DAG and blueprint for both statements and found no duplicate; LeanFinder, Loogle, and Mathlib grep found no weak-association declaration. The small affine case `X = Spec(A)` for a Noetherian ring reduces to the familiar fact that every ideal, in particular a maximal ideal, is finitely generated, so the hypotheses and direction of the specialization are correct.

## Second reading by H1

- Item statement: checked against Stacks Tag 05AR, label `lemma-ass-weakly-ass`; the locally Noetherian structure-sheaf specialization and both set inclusions agree with the source's final assertion.
- Step 1: checked against the statement of `lem-sc-locnoeth-stalk-maxideal-fg`; it supplies finite generation of `m_x` for every point under exactly the item's locally Noetherian hypothesis.
- Step 2: checked against the statement of `lem-sc-ass-weakass-fg-stalk`; instantiating its quasi-coherent module with the structure sheaf gives the pointwise equivalence, and the pointwise equivalence yields equality of the two sets.
- `lem-sc-ass-weakass-fg-stalk`: checked against Tag 05AR's first assertion, including the scheme, quasi-coherent module, point, and finitely generated maximal-ideal hypotheses; no DAG or blueprint duplicate was found and recorded Mathlib searches found no declaration.
- `lem-sc-locnoeth-stalk-maxideal-fg`: checked against Tag 05AR's locally Noetherian final assertion; its scheme, point, and finite-generation conclusion are self-contained, with no DAG or blueprint duplicate and no matching Mathlib theorem.
- Small cases checked: `Spec(A)` for a Noetherian ring, a field (zero maximal ideal), the empty scheme (vacuous pointwise assertion), and the zero module for the child equivalence.
- Changes: corrected the split item's `created.item` to this item so delivery ownership is accurate; added `pqf-def-coherent` to the finitely generated-stalk node's statement dependencies because it explicitly quantifies a quasi-coherent module.
