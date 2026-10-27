# Q88: lem-sfb-space-invertible-open-coherent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-invertible-open-coherent.json: statement, split following Stacks Tag 0D03, with its statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-relative-finite-free-locus-base-change.json: statement-only input, unsplit; no Mathlib match after two semantic phrasings, Loogle, LeanSearch and source grep.
- citations.json: verbatim statements for every node citation in each numbered proof step. Searches are retained in searches.jsonl and search-0.txt through search-4.txt.

## Attachments

None. Searched the live WeilConjectures source for the blueprint id, PicardStack/picardStack, invertible/coherent terminology and free-locus declarations. None gives all the clauses on algebraic spaces. The upstream sorry-bearing declarations are not attachments. Mathlib's Module.isOpen_freeLocus (Mathlib/RingTheory/Spectrum/Prime/FreeLocus.lean:171, read lines 155-181) concerns a module on an affine spectrum, with no relative-base-change assertion or algebraic-space sheaf assertion; it is not an exact match or a one-line specialization to this input.

## WANTED

None. The item and new input are present in the local Stacks sources.

## Findings and provenance

Read GOAL.md, the stage-1 brief, stage-1 document, the worker role, SETUP.md including all three blueprint levels, and delivery-errors B-E. The item is not the unit key theorem, so no unit realization record is changed. The sandbox had no prior item, report or searches.

Read quot.tex, lemma-picard-stack-open-in-coh (Tag 0D03), its statement and entire proof, and spaces-more-morphisms.tex, lemma-finite-free-open (Tag 0CZT), its statement and entire proof; checked the labels in tags/tags. The first source explicitly treats algebraic spaces. It uses relative flatness and finite presentation for arbitrary-base-change compatibility of the free locus; mere openness of an absolute free locus is insufficient. The source then removes non-free and wrong-rank fibres. My proof combines these removals into the closed complement of the rank-one open locus. This is the same route, with the two elementary identifications written out. In particular it does not assume that pullback by an arbitrary morphism reflects local freeness without relative flatness.

The source parent chain has a pre-existing provenance defect: following created.item ends with lem-sfb-admissible-direct-image pointing at Sheaf.SixFunctors.CtfStabilityDirectImages, which is not a DAG node. Accordingly tools/blueprint_refs.py ancestor prints blueprint.from.node = None. The item's existing null ancestor is retained, and the new input uses that exact computed value, with the inherited via chain preceded by this item and a precise source sentence added to from.place. The latest blueprint unit was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md; the item's chapter/unit and all inherited import/provenance metadata are preserved. This delivery does not repair other workers' ancestry records or change the unit route.

## Not duplicates

lem-sfb-space-relative-finite-free-locus-base-change vs lem-sfb-relative-finite-free-locus-base-change: the existing node assumes schemes for source, base and changed base; the new statement is for algebraic spaces, with etale local freeness on their small ringed sites and arbitrary algebraic-space changes of base. A scheme-only theorem cannot be applied directly to this item's possibly nonschematic X. It is not a special case of that existing statement. Both source records mention 0CZT, but the existing one explicitly calls it the space version of its own scheme theorem.

The DAG occurrences of 0CZT outside source fields were also read: lem-sfb-invertible-open-in-coherent-stack is the scheme-only moduli assertion; lem-sfb-fibrewise-module-flatness-criterion, lem-sfb-pointwise-module-flatness-base-change and lem-sfb-relative-module-flat-locus-base-change all have scheme hypotheses and different flatness conclusions. None states the new input. Whole-blueprint searches for 0CZT, finite free locus, locally free, invertible modules and Picard stack found no blueprint node for the new statement or the item. No extra node is made for rank strata, proper closedness, the groupoid equivalence, or eligibility of line modules: these are written as elementary steps from the cited statements and definitions.

## Review by Q88

I checked B-E against the source text and the actual statements of every cited node. The new node has all objects and hypotheses, defines finite presentation and relative flatness inline on charts, uses existing nodes for algebraic spaces, chartwise local finite presentation, quasi-coherence, pullback and fibre products, and carries no proof or hidden proof sketch. Its source is precisely 0CZT, lemma-finite-free-open, whose arbitrary-base-change clause is what step 2 needs. It does not restate the item's base representability assertion: it has no properness or moduli stack, and its conclusion lives on the total space.

Step 1 uses the base-change clauses of lem-sfb-space-flat-proper-fp-locality and the actual coherent-stack object's presentation, flatness and support conditions in lem-sfb-space-coherent-stack-general. Identity of X_T supplies the proper support witness, and a local rank-one presentation supplies finite presentation and quasi-coherence. The tensor formula and local generator calculation use def-trf-space-etale-module-functors; the functor is fully faithful because the subcategory is full, not because of a descent theorem left unstated.

Step 2 uses exactly the finite presentation and relative flatness clauses of the coherent-stack node, the locality node's base-change and finite-presentation clauses for p, and the new 0CZT statement. All hypotheses hold for every test scheme T, without a Noetherian assumption. Step 3 uses that free-locus base-change equality and the definition of line module in def-trf-algebraic-space. The open-image clause of lem-a1-space-affine-etale-cover turns the trivializing chart images into opens; I read that clause and cited it explicitly. I wrote out finite-rank independence on overlaps and invariance under field extension rather than introducing another node for an elementary rank calculation. Distinct ranks stay distinct even over nonreduced bases, as geometric residue fields detect them.

Step 4 uses properness only for the closed image of the complement, explicitly part of the locality node's statement. The pointwise reverse implication explicitly cites the statement of lem-weil-common-extension-fields for two arbitrary extensions of the same residue field, and uses the fibre-product universal property in lem-trf-space-fibre-products-etale-covers, not an unjustified equality of arbitrary underlying topological fibre products. Thus a bad point survives any base extension over its image. These field and topology lemmas, and the fibre-product lemma, are generic tools outside the unit, declared in split_report.tool_uses rather than used as replacements for its route. The factorization criterion is the defining property of an open subscheme. Step 5 uses the full-subcategory and 2-fibre-product conventions in def-sfb-open-moduli-substack and displays the unique arrow between two trivialized objects. No gerbe or automorphism group is silently discarded.

Small cases checked: if X_T is empty, every pullback module is vacuously a line module and U_F=T; for F=0 and a nonempty fibre, rank zero is excluded; for constant rank two, every nonempty fibre is excluded; for mixed ranks, the closed bad subset detects exactly the unwanted fibres. For a nonflat test change, freeness is controlled by relative flatness through 0CZT, not by a false reflection claim. No surjectivity of f is used. Each non-elementary step is short and directly cites its needed theorem; no proof step exceeds 2000 characters. There is no statement correction, route change, unsupported source tag, or new node that simply restates a clause of the item. Search results were read as returned and recorded verbatim; no service failure is claimed to prove absence. No Lean was written or compiled and the repository was not modified.

## Unfinished work

The new node is intentionally statement-only, as required for a one-level split. No part of the item's natural-language argument remains unfinished. The first server dry run passed at eb28f96d0d2. After that check I made the common-field and etale-open-image citations explicit to ensure C1, and regenerated citations.json; the final dry run tests these refinements before push.
