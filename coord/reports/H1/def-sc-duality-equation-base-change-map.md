Files written:

- `dag/nodes/sec-picard-framework/def-sc-duality-equation-base-change-map.json` (definition, split; no new nodes).
- `citations.json` (verbatim statement excerpts for every step citation).

Attachments:

- None. No sorry-free project declaration carries the exact blueprint tag or statement.

WANTED:

- None. The cited Stacks source is available in the source collection used for the imported node.

What I checked and corrected:

- The imported definition was compared with Stacks Project `duality.tex`, Tag 0AA8, the `equation-base-change-map` display and the setup of Lemma 48.6.2. The Lean source checkout contains no declaration tagged `def-sc-duality-equation-base-change-map`, so this is not an attachment.
- I retained the fibre-product, derived-category, derived-direct-image, derived-pullback, and qcqs right-adjoint dependencies, and added the existing `lem-pc-ringed-spaces-derived-adjoint` dependency because the statement explicitly uses both derived pullback/direct-image adjunctions. The existing Mathlib-backed `def-weil-pbc-adjunction-conjugate` is also cited for the conjugate and its preservation of isomorphisms.
- Step 1 checks the cartesian square and ambient derived categories. Step 2 checks right adjoints and both pullback adjunctions. Step 3 constructs the canonical comparison `beta` by transposing the unit map through the square. Step 4 checks that its conjugate `theta` is an isomorphism. Step 5 expands the unit, inverse-conjugate, and counit composite exactly as Stacks' equation. Each citation was checked against the cited node's statement and copied into `citations.json`.
- The small sanity check is the identity square: `beta` and `theta` are identities by the mate identity law, and the displayed composite reduces to the identity by the two triangle identities.

## Review by H1

I read the item source and the relevant Stacks passage, then read every cited node in full. The fibre-product statement supplies the square and projections; the derived-category/direct-image definitions supply the ambient categories and functors; the qcqs right-adjoint statement supplies `a` and `a'`; and `lem-pc-ringed-spaces-derived-adjoint` supplies the units and counits for `Lg^*` and `Lg_X^*`. The conjugate node explicitly states the mate bijection and that isomorphisms are preserved, which is exactly what Step 4 takes. I verified that the hypotheses used in each step are present in the item, including the assumed invertibility of `beta`, and that the final composite has the stated source and target. I corrected the imported dependency list by adding the derived-adjunction node; no child node was necessary and no statement was weakened.

## Second reading by H1

Step 1 was checked against Stacks `duality.tex`, Tag 0AA8, the cartesian-square setup, and the statements of `def-pc-fibre-product`, `def-pc-derived-category`, and `def-pc-derived-direct-image`; the square, projections, and ambient categories are supplied; verdict pass.
Step 2 was checked against Tag 0AA8 and the statements of `lem-pc-qcqs-derived-direct-image-right-adjoint`, `lem-pc-ringed-spaces-derived-adjoint`, and `def-pc-derived-pullback`; both right adjoints and both pullback adjunctions are available; verdict pass.
Step 3 was checked against Tag 0AA8's mate construction and the statements of `def-pc-derived-pullback`, `def-pc-derived-direct-image`, `lem-pc-ringed-spaces-derived-adjoint`, and `def-pc-fibre-product`; the unit, square identification, and transpose defining `beta` are explicit; verdict pass.
Step 4 was checked against Tag 0AA8's invertible middle arrow and `def-weil-pbc-adjunction-conjugate`; the conjugate has the stated direction and preserves isomorphisms; verdict pass.
Step 5 was checked against the displayed equation `equation-base-change-map` in Tag 0AA8 and the unit/counit clauses of the cited adjunction and conjugate statements; the three arrows and their source and target are exactly the equation; verdict pass.
The item node was checked as a self-contained definition against Tag 0AA8, including the explicit hypothesis that `beta` is an isomorphism; verdict pass.
There are no new child nodes to audit: the proof facts are either supplied by existing cited nodes or are the elementary mate/composite unpacking in the five steps; verdict pass.

Changes made: none. The existing statement, citations, dependencies, and proof steps are accurate and the dry-run preflight passes.
