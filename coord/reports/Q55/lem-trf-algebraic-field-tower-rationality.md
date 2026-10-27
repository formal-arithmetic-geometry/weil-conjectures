## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-algebraic-field-tower-rationality.json`: statement item, split into three steps; no exact Mathlib match for the whole disjunctive specified-map assertion.
- `citations.json`: verbatim statement quotes for both cited nodes, assigned to their proof steps.
- `report.md`: this report. The search command generated `searches.jsonl` in this sandbox.

New nodes: 0. New Mathlib leaves: 0. Reused Mathlib leaf: `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`.

Attachments: none. Searching the entire project source by the item id and the tower/algebraically-closed/bijectivity notions found no declaration stating the item. The project uses the Mathlib algebraMap bijectivity lemma elsewhere, but those uses do not prove this item.

WANTED: none.

No statement correction or dispute. The statement, statement dependencies, inherited provenance and historical searches are preserved. The source really distinguishes the actual structural maps; replacing them with abstract field isomorphisms would not establish it. Nothing remains unfinished.

## Sources and searches

I read `literature/stacks-project/fields.tex`, Definition `definition-algebraically-closed` (Tag 09GQ, lines 900–904) and Lemma `lemma-algebraically-closed` (Tag 09GR, lines 910–943), including the proof of the equivalence of polynomial and extension definitions. I also read the chapter and `sk-i-curve-zero` unit and the current ancestor `lem-trf-local-term-locality`. This item already records its historical auxiliary-branch provenance; the elementary field argument does not change the current unit or chapter route.

The DAG search by 09GR and algebraic-extension keywords located the existing elementwise leaf, the finite-extension leaves `lem-weil-pbc-alg-closed-finite-extension-trivial` and `lem-pc-finite-extension-alg-closed`, and other users. The elementwise leaf applies without a finiteness hypothesis, so it is the correct reuse. Blueprint searches for algebraically closed, algebraic extension, tower, algebraically closed subfield and rational endpoint found no blueprint node equivalent to the full item. No new node is needed.

Q55 ran LeanFinder twice with the full tower assertion and a second formulation using a surjective composite, Loogle `IsAlgClosed, Algebra.IsAlgebraic`, LeanSearch for algebraic extensions of an algebraically closed field, and the logged Mathlib grep in `FieldTheory`. All returned successfully. The inherited search records remain as historical evidence; the new entries are copied from the actual Q55 log. I read Mathlib `FieldTheory/IsAlgClosed/Basic.lean` lines 207–249 and `RingTheory/Algebraic/Basic.lean` lines 501–515. `IsAlgClosed.algebraMap_bijective_of_isIntegral` is an ingredient, not the two-alternative statement. The scalar-tower bijectivity lemmas require a reverse algebra map. Neither discharges our item by a one-line specialization without constructing further data and dividing into the alternatives.

## Review by Q55

For B, there are no new nodes and no new definitions to audit. The unchanged statement introduces all fields and all maps, retains unitality, algebraic closedness, algebraicity of L over K through alpha, and the exact disjunction. The source tags were checked against `tags/tags` and their actual TeX labels. Each step is below 2000 characters; the total assembly is below 3000. The algebraic-closedness result already has a searched Mathlib leaf, so I did not create an unnecessary finite-extension or triviality node.

For C and D, I opened both cited node statements. Step 1 takes injectivity from `def-pc-field-extension`, whose statement explicitly says that field homomorphisms are injective; I also wrote the inverse argument, so the elementary classification is justified independently. Step 2 uses exactly the statement of `lem-weil-pbc-algebraic-over-algebraically-closed-subfield`: a root of a nonzero polynomial over the image of an algebraically closed field belongs to that image. I checked its hypotheses with source field our k, target field our L and homomorphism our j. Before applying it, the step constructs each coefficient preimage using surjectivity of i, writes P as the image of Q through j, verifies Q is nonzero, and records its vanishing at z. It concludes surjectivity of the actual j and alpha by giving preimages. Step 3 cites no additional fact: it chooses preimages under j and cancels alpha using Step 1. Both clauses are proved within the item rather than restated as new lemmas. `citations.json` contains the exact quoted substrings for every node cited by each step. The sole cross-unit statement citation is an existing Mathlib leaf, used as a generic algebra tool, so no route replacement is involved.

For E, all rings involved are fields, so injectivity excludes the zero-target exception. The first case requires no finite-dimensionality: each individual algebraicity witness is enough. Its coefficient substitution preserves the actual map identity j = alpha i. The second case does not infer surjectivity of i merely from surjectivity of a composite; it additionally cancels the injective alpha, explicitly. I tested identity maps (including positive characteristic algebraically closed fields), the case where both alternatives hold, and the case with j bijective without using either algebraicity or algebraic closedness. Removing the endpoint hypothesis would fail for k algebraically closed, K = k(t), L = K and alpha the identity; removing algebraic closedness in the first alternative would fail for k = K = R, L = C. These checks support precisely the stated hypotheses. I made no mathematical corrections; the repair during writing only corrected the path used to locate an existing definition for the citation file, then regenerated and checked both verbatim quotes.

## Not duplicates

No new nodes, so no new/existing pairs arise. The item concerns an entire specified tower with either endpoint map bijective; the existing elementwise leaf concerns one algebraic element in a single extension and is cited as its ingredient.

## Dry-run repairs

The first dry run required a citation quote of at least 40 characters. The injectivity substring was verbatim but shorter, so I replaced it with the entire statement of `def-pc-field-extension`; the proof did not change.
