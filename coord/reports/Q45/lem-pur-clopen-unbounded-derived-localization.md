## Files written

- dag/nodes/sec-smooth-purity/lem-pur-clopen-unbounded-derived-localization.json: statement item, split; no item-level Mathlib match. The mathematical statement and all statement dependencies are unchanged.
- citations.json: 24 checked verbatim statement quotations for the nine proof steps.
- No new nodes; no new Mathlib leaves.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for clopen/derived equivalences. The finite-coefficient ClopenIdempotent module proves individual clopen identities for a coefficient-category setup, not every clause here for an arbitrary ring sheaf. EtaleSheafClopenProduct is an etale sheaf-level result, not this pro-etale unbounded assertion. Neither supplies a complete attachment.

## Wanted literature

None. Read the local Stacks sources derived.tex, definition-unbounded-derived-category (05RU), and lemma-right-derived-exact-functor (015F), including the latter's explicit 'Details omitted'. Those missing details are written out here rather than treated as a theorem statement. The supporting exact homology fact is homology.tex lemma-exact-functor (010N), as recorded in the existing exact-functor cohomology node. The natural-transformation form of the localization universal property is the existing Mathlib leaf, not an assertion falsely attributed to the text of Stacks. Read Mathlib DerivedCategory/ExactFunctor.lean lines 24–105 and Localization/Pi.lean lines 26–48 to check the generic exact functor and finite product inputs. All proofs remain agent-origin, since Stacks does not itself state this normalized clopen assembly.

## Problems found and changes

The input was statement-only and was not false. Its hypotheses allow arbitrary, possibly zero ring sheaves, empty components, an empty index set and unbounded complexes; none may be replaced by finite constant coefficients or a bounded-below framework. Kept them all. Avoided both treating the exact-derived-functor definition as a theorem and treating a localization of a product as automatic: cited the existing generic Mathlib leaves instead.

The present main-20261015 blueprint section-invariant definition was read at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-def-purity-conv/def-pur-section-invariant.md. The item serves its invertibility clause through the recorded finite-clopen decomposition and tensor-calculus ancestors. No chapter or unit route changes, and no SGA sources.

DAG search: searched all node statements/titles for exact functor, homology, exact equivalence, localization, clopen, and finite-product derived assertions; searched the Stacks tags 015F and 05RU; ran blueprint_refs ancestor and searches for clopen, exact functor, product localization, localization, homotopy and derived categories. Found and reused lem-weil-pbc-exact-functor-complex-cohomology, lem-weil-pbc-exact-functor-derived-factorization, lem-sfb-product-localization, lem-weil-pbc-localization-universal-property, lem-galois-equivalence-preserves-limits and lem-sfb-derived-localization-additive. The more elaborate unsplit lem-pur-exact-derived-cohomology-coherence is unnecessary: only its basic one-functor comparison is needed, and that is explicitly descended here from the existing complex comparison. The ancestor finite-product tensor node depends on this item and is not cited back.

Mathlib searches ran only through the required msearch.py command and are preserved in searches.jsonl and search-1.txt through search-5.txt. Both semantic phrasings, Loogle, grep and LeanSearch were read. The generic mapDerivedCategory hit is a useful ingredient already represented by a Mathlib leaf, not a complete one-line identification of this item.

## Not duplicates

No new nodes were created. The generic localization, exact-functor, cohomology and equivalence tools already exist and are cited. No same-tag pair requiring a new-node distinction is introduced.

## Review by Q45

I read the item against Stacks 015F and 05RU, the current blueprint section-invariant definition, the chapter and unit records, and the statement of each node cited in the proof. I retained the specified sectionwise product gluing functor, with its original restriction unit and projection counit, rather than choosing an unrelated inverse equivalence. I checked delivery-errors B–E as follows in the actual steps.

Step 1 takes exact additive module gluing from lem-pur-clopen-ringed-module-gluing. Its statement supplies both exact functors, their explicit unit/counit and the coordinate decomposition. Zero insertion is proved exact by coordinate kernels and cokernels, not by surjectivity on sections. This works for arbitrary ring sheaves, using exactly the module categories already in the statement.

Step 2 uses that same specified module equivalence and the complex definitions in def-weil-abstract-derived-category. The degreewise naturality equations are the chain-map equations; the displayed dh+hd calculation proves passage to homotopies. The module triangle identities hold in each degree, so no new coherence lemma is hidden here.

Step 3 uses the actual statement of lem-weil-pbc-exact-functor-complex-cohomology: it gives the natural kernel/image-normalized comparison for every integer, without boundedness. This applies to r_i, e_i and G because step 1 established their exactness. Coordinate kernels and images and inversion of tuple maps give the detection result in a few lines; no geometric-point conservativity is assumed.

Step 4 uses lem-sfb-product-localization precisely for a finite index set with arrow classes containing identities, and def-weil-abstract-derived-category for each Q_i. I checked both inversion requirements for the two applications of lem-weil-pbc-localization-universal-property: restriction preserves quasi-isomorphisms and so does exact G on product complexes. These are the statements of the nodes, not claims borrowed from their proofs.

Step 5 uses clauses (2) and (3) of that same universal-property node. It really states lifting of natural transformations, preservation of identities/composition, and equality detected on the localization image. This gives the specified unit and counit, lifts their inverses and checks both triangle equations after the right precomposition. The precise source for normalization is also the module-gluing statement.

Step 6 uses lem-weil-pbc-exact-functor-derived-factorization, which states the triangulated structure and shift-compatible termwise factorization, not merely existence of an unstructured functor. The universal property identifies it with the chosen restriction and insertion. For G_D I explicitly checked a tuple of cone representatives against the cone formula stated by def-weil-abstract-derived-category, including the negative projection and shift sign. The additive exact G comes from the module-gluing node. Thus the product target is given its component triangulation and both directions preserve it; no product-triangulation theorem with a missing hypothesis is invoked.

Step 7 uses the natural comparison of the complex cohomology node and the cohomology factorization clause of def-weil-abstract-derived-category. The universal property's transformation clause descends it and its inverse on all morphisms, so this is an actual derived natural isomorphism, not merely an assertion on cohomology groups of selected representatives.

Step 8 descends the restriction/insertion identities stated by the module-gluing node, using transformation uniqueness. Zero insertion J_i into the product derived category gives G_D J_i=e_D,i up to the uniquely normalized isomorphism. A tuple is its finite coordinate coproduct by the product-category morphism formula. The statement of lem-galois-equivalence-preserves-limits supplies preservation by G_D. The existing additive/essentially-surjective localization leaf verifies the finite biproduct equations on representatives. This gives the sum formulas for arbitrary derived objects, not just sheaves in degree zero.

Step 9 uses the equivalence already constructed to detect zero objects and isomorphisms directly: a tuple of inverses is an inverse. For the edge clauses, the module-gluing statement supplies the empty-site module category. For a zero coefficient sheaf the equation 1x=0x is a direct sectionwise proof that all modules are zero. I then apply the localization universal property to the already invertible arrows in a zero category; this proves the derived zero-category assertion without using the generally false claim that localization adds no arrows. The covering condition forces X empty when I is empty.

Small cases checked: I a singleton (the original module gluing and its normalization localize), two components (off-diagonal insertions vanish and each diagonal is identity), an empty component, the all-zero ring sheaf on a nonempty X, and I empty with X empty. Finiteness is used exactly in product localization and the coordinate sum. No boundedness, enough-injectives, constructibility, flat resolution or coefficient-constancy hypothesis was introduced. Every step is below 2000 characters, and I checked that none hides a new source-standard lemma: the non-elementary inputs all have existing cited nodes. No new nodes means B1/B2/B3/B4/B6 and new-statement tests create no extra obligations; checked the item's TeX and kept its full statement unchanged. citations.json quotes are verified as substrings of the current cited statements. The dependence on ancestor nodes was checked to avoid a cycle. No independent reviewer was used, as required by this direct-delivery brief.

## Unfinished work

No mathematical clause left open in this split. The required server dry run and delivery are recorded by deliver.py; no local compiler or DAG-checker was run.
