1. Files written:

- `lem-sc-cech-h1-injective.json`: statement item, split into two proof steps.
- `lem-sc-cech-torsor-gluing.json`: new statement-only node; Mathlib search verdict no match.

2. Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator` states this item exactly.

3. WANTED: none. The Stacks source was available in the local review checkout at `/home/ubuntu/weil-sandbox/C1/lem-weil-pbc-field-tensor-irreducible/stacks-review/cohomology.tex`.

4. What was checked and changed: the item source is Cohomology Lemma 0B8R (`lemma-cech-h1`), whose statement is the injectivity assertion for an abelian sheaf on a topological space; the item specializes this to the underlying abelian sheaf of an O_X-module on a scheme. I also read the existing `lem-sc-torsor-h1` statement: it supplies the canonical H^1 classification of torsors and identifies the zero class with the trivial torsor. The new node records the source's omitted construction: transition sections from local trivializations, gluing of trivial torsors, and the coboundary/isomorphism criterion. Step 1 cites exactly that gluing statement. Step 2 cites the H^1 torsor classification, the gluing node for recovery of the transition cocycle, and `lem-sc-cech-h1-map-natural` for the canonical map c_H; these statements provide the facts used. The hypotheses checked are an abelian sheaf, an open cover, and local sections on every U_i. The one-open-cover case has zero Cech H^1, and the zero sheaf gives the trivial torsor, so both edge cases are consistent. I removed an inappropriate scheme dependency from the topological gluing node. Mathlib searches for the new node used LeanSearch, LeanFinder, and a source grep; no matching theorem was found. The blueprint ancestor is `lem-sc-pic-proper-ntorsion`, and the split report records the inherited 0B8R proof place.

## Review by H1

I read the full 0B8R statement and proof in `cohomology.tex` and checked the existing torsor-classification node before writing the split. Step 1 uses only the new node's explicit gluing, local-section, and coboundary statements. Step 2 uses the existing classification statement for the zero class/trivial torsor implication, the new node to identify the resulting transition cocycle as a coboundary after choosing a global section, and the natural-map node for the meaning of c_H. I checked that each cited statement contains the fact quoted in `citations.json`; no proof relies on a cited node's hidden proof. The child node is statement-only and strictly records the cocycle-to-torsor construction rather than restating injectivity. Small cases checked were a one-member cover and the zero sheaf. No source error or Lean attachment was found.
