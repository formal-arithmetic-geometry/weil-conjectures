## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-flat-projective-hilbert-polynomial-locality.json — statement, split into eight proof steps; not a Mathlib leaf.
- citations.json — all fourteen step-to-node citations, with verbatim statements.
- No new DAG nodes and no Mathlib leaves were created. No unit record was changed: this is a prerequisite, not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures for the exact item id and for Hilbert-polynomial names and docstrings. Modules/HilbertPolynomial.lean and Modules/Ample.lean address individual proper schemes; no project declaration found gives this item's family-locality, arbitrary-base-change, coordinate-polynomial and empty-fibre clauses together. Existing closed nodes are cited where applicable.

## WANTED

None. All mathematical sources used for this split are present in literature/stacks-project/.

## Findings and changes

The item was statement-only, and its sandbox contained no earlier split, report or searches. Its statement is correct and is retained verbatim. I added statement dependencies for the projective-space, geometric-fibre, residue-field, twist, pullback, Proj and Euler-characteristic notions that its text already uses. I preserved all existing fields and searches, then appended the actual NR msearch results in searches.jsonl. No Lean was written and no compiler/build tool was run.

The whole-DAG search for 0B9T, 08AC, 08AE, Hilbert polynomial and Euler local constancy found the existing proper-flat Euler node, coordinate/Euler comparison node, homogeneous-ideal node and numerical-polynomial nodes. The blueprint searches for Hilbert polynomial and projective proper were read. The imported blueprint Hilbert-polynomial lemma concerns one proper scheme with an ample line bundle, not families. I reuse the stronger existing Snapper node instead of introducing a projective-field-polynomial node. All supplementary facts in steps 2, 5--8 are direct arguments, not new nodes.

The source place of existing lem-sc-snapper-numerical-polynomial incorrectly calls its theorem Tag 0BEL. The local Stacks tag map makes 0BEL the section and 0BEM the lemma-numerical-polynomial-from-euler theorem. I read and use that theorem at varieties.tex:10195. Its mathematical statement matches the cited node exactly; I have not edited the other worker's node.

The inherited blueprint.from.node is null, and blueprint_refs.py ancestor reports None. I retained the existing via chain and its explicit Hilbert-construction place rather than inventing an ancestor. The current unit text was read at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and the stored chapter/unit records were read. This split remains the numerical prerequisite under the existing Hilbert-representability branch, without changing a unit or chapter route.

## Not duplicates

No new nodes. The reused coordinate/Euler comparison is narrower than the item: it gives eventual equality for a single homogeneous quotient, without numerical-polynomial existence, local constancy or family base change. The reused Euler theorem is broader in sheaves but does not itself construct or identify Hilbert polynomials.

## Review by NR

I read perfect.tex, Tag 0B9T, lemma-chi-locally-constant-geometric, including its proof through perfect direct images. Its hypotheses are proper finite presentation and a finitely presented sheaf flat over the base; the base is arbitrary. I read varieties.tex, lemma-numerical-polynomial-from-euler (actual Tag 0BEM), the statement and proof setup of 08AC and the Serre-vanishing proof of 08AE; constructions.tex 03GL, lemma-closed-in-projective-space; and coherent.tex 0AG7, lemma-recover-tail-graded-module. These give the fibre polynomial and its comparison with the homogeneous coordinate ring. I also read morphisms.tex lemma-locally-projective-proper (01WC), lemma-finite-type-noetherian (01T6), and coherent.tex lemma-coherent-Noetherian (01XZ) for the auxiliary hypotheses. There are no new node statements to check against sources.

For step 1 I opened all five cited nodes. The projective definition requires an embedding and quasi-compactness, supplied by the item; for a field fibre its finite standard affine chart cover also supplies quasi-compactness. The projective-proper node actually asserts properness. The closed-immersion base-change node supplies the fibre embedding. The finite-type-over-Noetherian node applies only to the field fibres, not to arbitrary T. The coherent/finite-type equivalence then applies to the structure sheaf on that Noetherian fibre. A field has just two ideals, which verifies the Noetherian base hypothesis here.

For step 2 I checked the full statements of the twist, flat-morphism and module-pullback nodes. The twist node really gives the local free bases and transition functions, so the argument multiplies or tensors those functions explicitly to obtain powers, dual powers, and arbitrary base-change compatibility. Local free rank one makes the sheaf finitely presented; its stalk is the structure stalk, which is flat over the base by the given flat morphism. No coherence or Noetherian assertion about the total Z is used.

For step 3 I opened lem-sfb-proper-flat-sheaf-euler-local-constancy and checked both clauses, verbatim in citations.json. Step 1 gives proper finite presentation and step 2 gives the required sheaf finite presentation and base flatness. The base-change clause applies directly to any field-valued point, including its algebraic closure, giving the asserted geometric Euler values. There is no assumption that coherent cohomology dimensions individually remain constant.

For step 4 I checked each of the three cited statements: Snapper gives a numerical polynomial at all integers for a coherent module and invertible powers on a proper field scheme; 03GL gives a homogeneous ideal for every closed subscheme; the coordinate/Euler node gives eventual equality for any such homogeneous ideal, even an unsaturated ideal. The structure sheaf coherence comes from step 1, and invertibility/power identification comes from step 2. The infinite-root argument establishes uniqueness and presentation independence explicitly. This step takes only the statements of its citations, not their internal constructions.

Step 5 is the elementary monomial count and a written leading-coefficient comparison. It proves the uniform degree bound n without needing dimension theory or a new polynomial-growth lemma. Step 6 uses exactly the standard chart description in def-pc-proj. Vanishing of every high graded piece forces a power of every coordinate to vanish; every localization chart is therefore zero. This proves the nonempty direction without importing positivity of ample Hilbert degree. The empty direction follows from zero cohomology of the empty scheme.

Steps 7 and 8 use results already established in this item's preceding steps. Step 7 takes the finite intersection of the n+1 Euler-constant neighbourhoods, and the root bound then proves equality of the polynomials. Step 8 cites the fibre-product universal property, and applies step 3 to the composite geometric field point over T, giving equality of all polynomial values. It neither assumes an embedding between chosen algebraic closures nor needs a separate flat-field-extension comparison theorem. I checked that the fibre-product node supplies precisely the needed universal property.

Small cases checked: n=0 needs one value and gives a constant polynomial; the empty scheme and unit homogeneous ideal give the zero polynomial; a nonempty zero-dimensional nonreduced fibre has positive eventual graded dimensions and cannot be declared empty by the argument; unsaturated ideals are allowed by the coordinate/Euler statement; nilpotents and disconnectedness in T do not enter the finite-neighbourhood intersection; T and T' may be empty, non-Noetherian, nonreduced, or non-quasi-compact. All steps are shorter than 2000 characters. No step hides a separate comparison or standard-lemma invocation. Generic off-unit statement tools are declared in split_report.tool_uses.

The actual search results were read: Polynomial.hilbertPoly and preHilbertPoly are constructions from rational power-series coefficients (Mathlib/RingTheory/Polynomial/HilbertPoly.lean:18--44), whose TODO still excludes graded-module Hilbert polynomials; they do not assert the scheme-family theorem. Module.isLocallyConstant_rankAtStalk (Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:224--228) concerns a finitely presented flat module, not proper coherent cohomology. Other hits concern flatness/base-change permanence or unrelated Euler characteristics. A second LeanFinder wording returned the same rank theorem and unrelated condensed-module results, so there is no item-level Mathlib match in these results. I did not create leaves from partial matches.

## Unfinished work

None in the requested one-level split. The existing unsplit input nodes remain their owners' work; no existing dependency was modified.
