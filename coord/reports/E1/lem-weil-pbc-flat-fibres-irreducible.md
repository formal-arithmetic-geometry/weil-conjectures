1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-fibres-irreducible.json`: statement node, split; Mathlib search found no exact match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-finite-presentation-open.json`: statement node, Mathlib leaf via `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation` in `Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-irreducible-on-top.json`: statement-only node; no exact Mathlib match.
- `citations.json`: verbatim statement quotes for both proof steps.

2. Attachments: none.

3. WANTED: none.

4. What was checked and changed:

- The item source was read in `/home/ubuntu/c1-stacks-review/algebra.tex`, Lemma 00I6 (`lemma-flat-fibres-irreducible`), including its proof. Its proof has exactly two substantive inputs: Proposition 00I1, that flat finite-presentation maps induce open maps on spectra, and Topology Lemma 004Z, that an open map from a space to an irreducible target with irreducible fibres over a dense set has irreducible source.
- The 00I1 input was checked in `/home/ubuntu/c1-stacks-review/algebra.tex` at `proposition-fppf-open`; the new node states the ring-map specialization and records the Mathlib declaration and source lines supplying it.
- The 004Z input was checked in `/home/ubuntu/c1-stacks-review/topology.tex` at `lemma-irreducible-on-top`; the new node states every hypothesis and conclusion explicitly. The existing `lem-sc-open-map-irreducible-fibres-components` node was inspected and rejected as a citation because it assumes irreducibility of every fibre and gives component bijections, so it does not state the dense-fibre criterion used here.
- Step 1 cites only the new open-spectrum statement, and its hypotheses are exactly the item's flatness and finite-presentation assumptions. Step 2 cites only the new topological criterion, checks the irreducible target from the item's hypothesis, and identifies the affine fibre with `Spec(T tensor_R kappa(p))` from the item's fibre hypothesis. Both steps are marked non-elementary and have their source places recorded.
- I searched the pinned Mathlib checkout with LeanSearch, LeanFinder, and source grep for both new statements. The open-map node is a Mathlib leaf; the dense-fibre criterion has no exact declaration. Small cases checked: identity map (one-point and irreducible affine spectra), a polynomial extension with geometrically irreducible fibres, and a product over an irreducible base with constant irreducible fibre.

5. What could not be finished: nothing.

## Review by E1

I reread the item and the full proof of Stacks Algebra Lemma 00I6, then read the exact source passages for Proposition 00I1 and Topology Lemma 004Z. I checked each cited node's statement rather than relying on its proof: the first node explicitly says flat finite-presentation ring maps induce open spectrum maps, and the second explicitly says an open map over an irreducible target with irreducible fibres on a dense set has irreducible source. I verified that Step 1 supplies the first node's flatness and finite-presentation hypotheses from the item, while Step 2 supplies the second node's target and dense-fibre hypotheses and uses the stated affine fibre ring. I also checked the existing component-bijection node and did not cite it because its stronger all-fibres hypothesis does not cover 004Z. The new Mathlib leaf's declaration and file were read at the recorded lines; the other node was tested against the three required searches and remains unsplit. I corrected the initial empty proof by adding these two explicit steps, their proof dependencies, blueprint references, and exact citation quotes.
