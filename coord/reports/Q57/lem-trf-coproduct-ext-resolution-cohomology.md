# Q57 stage-1 delivery: lem-trf-coproduct-ext-resolution-cohomology

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coproduct-ext-resolution-cohomology.json`: existing statement, now split into six steps. No new nodes, no new Mathlib leaves, and no statement or statement-dependency change.
- `citations.json`: five verbatim statement quotations, one for each step/node citation.
- `searches.jsonl`: the six new Mathlib searches run through the required msearch.py command. The item's earlier seven search records were preserved unchanged.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and for coproduct/Ext terminology found no declaration proving the complete item. The project file `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean` proves a finite-coproduct vanishing result only. The already recorded `SheafOfModules.isGrothendieckAbelian` belongs to the existing node `lem-weil-pbc-ring-sheaves-grothendieck`; no duplicate is created here.

## WANTED

None. All sources needed are present locally.

## Findings and corrections

The item was unsplit and the sandbox had no item, split, report or search log. The statement is correct; I kept it unchanged. Its Hom complex is a complex of abelian groups, and the product in the calculation is a product in Ab. No exactness of products of module sheaves is assumed. The cochain notation cited in the item can be read on the one-object trivial site with coefficient ring Z for this Hom complex; no internal sheaf Hom is used.

I expanded the two details suppressed in the Stacks direct-sum assertion: the inverse to restriction is the coproduct universal property, and cohomology commutes with products here by exactness of products in Ab. I used the existing general resolution comparison rather than an extra resolution-independence node. The degree-zero proof gives its actual map and its naturality under every source map, not merely under maps preserving summands.

Mathlib discovery used LeanFinder twice, LeanSearch, Loogle, and two scoped greps, all successful and logged. I read `Mathlib/CategoryTheory/Abelian/Injective/Ext.lean:35-83`, especially `extEquivCohomologyClass` and `extAddEquivCohomologyClass`, and `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean:474-490`. The former is precisely an existing input; the latter requires Fintype and does not discharge arbitrary small coproducts. `Mathlib/Algebra/Category/Grp/AB.lean:69-99` supplies exact arbitrary products. These hits do not state all the clauses of this item in one-line specializations, so the item remains split rather than a Mathlib leaf.

## Not duplicates

No new nodes. Whole-DAG searches by title and statement for injective resolutions, comparison, Grothendieck module sheaves and exact products found all the inputs already present. Whole imported-blueprint searches with blueprint_refs.py for injective resolution, resolution comparison, product cohomology, coproduct, Ext, and products of abelian groups found no blueprint node stating this complete item; the item keeps `same_as: []`. The blueprint ancestor command confirmed `lem-trf-local-term-locality`.

## Review by Q57

I read delivery-errors.md B--E in both its current and archived versions, the stage-1 brief, GOAL.md, SETUP.md's three-level rule, the trace-formula chapter and the sk-i-curve-zero unit. I also read the actual current blueprint files in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/`, including the ancestor proof. This is a generic homological supporting item deep in the inherited derived-shriek dependency chain, not a replacement for the ancestor's contracting-correspondence argument. Chapter and unit records are unchanged.

For the item's source I read Stacks `sites-cohomology.tex`, Tag 07AA (`example-hom-complex-into-sheaf`) and Tag 07AC (`lemma-existence-derived-lower-shriek`), through the paragraph passing from Ext vanishing on generators to their sums. That passage is terse, so proof_origin is explicitly agent: my expansion follows its injective-resolution argument. I read `injectives.tex` Tag 079Q (`remark-existence-D`), which names ringed-site module sheaves as Grothendieck examples, and Tag 079H (`theorem-injective-embedding-grothendieck`), and `derived.tex` Tags 013K, 06XR and 05TD at their actual labels. There are no new nodes needing additional sources.

Step 1 cites the full statements of `lem-weil-pbc-ring-sheaves-grothendieck`, `lem-sp-grothendieck-enough-injectives`, and part (1) of `lem-weil-pbc-left-exact-injective-resolution-degree-zero`. I opened all three files. The first explicitly gives Grothendieck abelianness and every small colimit for arbitrary ring sheaves in the site's universe; the second gives enough injectives; the third gives a resolution zero in negative degrees. Our site is small and our commutative ring is a special case of their ring hypothesis. The coproduct index A, unlike the unused size of the family index I, is small in that universe. The first node is declared as a generic tool use, since it is outside the unit and not a route substitution.

Step 2 uses the statement of `lem-weil-pbc-ext-via-injective-resolution`, which I opened in full: it describes exactly the Hom complex, the quotient by boundaries and its resolution-independent Ext interpretation for any abelian category. Its nonnegative resolution hypothesis is exactly step 1. No projective objects or projective resolutions of sheaves are assumed. I checked its Mathlib match in the actual source and read Stacks 06XR.

Step 3 is an elementary use of the actual coproduct universal property, with both inverse and differential identity written. It does not invoke an unstated theorem that Hom preserves a colimit; the argument proves that particular assertion directly. Restriction is additive because both addition of sheaf morphisms and composition are additive.

Step 4 cites only `lem-pc-abelian-groups-exact-products`, whose statement I read: despite the parenthetical word countable, its displayed quantifier explicitly ranges over every family indexed by I, and its Mathlib AB4Star match confirms arbitrary products. I use it on two explicitly displayed short exact sequences of abelian groups. The first computes boundaries and the second computes the quotient of cycles by boundaries, so the elementary inference after that input is a few lines. It is not an assertion of exact products in Mod(R), nor an application of the existing finite-product-complex node beyond its hypotheses.

Step 5 needs no further theorem: exactness in the supplied resolution makes iota a kernel and therefore gives the unique factorization of each zero-degree cycle. The vanishing negative term removes all boundaries. The formula (iota h) f = iota (h f) proves the actual naturality claimed, including maps mixing summands. Step 6 only substitutes the earlier results and gives explicit mutually inverse precomposition maps for a specified isomorphism.

For the small cases I checked A empty (all groups zero and the empty product is the zero group in Ab), one summand, repeated indices, q=0 (no incoming boundaries), arbitrary positive q, and F=0 (any allowed injective resolution is still handled by the general comparison). No distinctness, finiteness of A, projectivity, exact sheaf products, or extra Ext-vanishing assumption enters before the final conditional assertion. There is no false source statement or statement dispute. I checked that none of the five cited nodes depends transitively on the item, so the proof introduces no cycle. Every non-elementary invocation has a node quotation in citations.json. No proof step exceeds 2000 characters, and the entire assembly proof is 2596 characters, so it hides no long comparison or lemma. No new clause-relabeling nodes or elementary-fact nodes were created.

## Unfinished work

None in this one-level split. Existing unsplit inputs remain existing queued items; they were not re-split or changed by this delivery. No Lean was written and no compiler, Lake or local DAG/preflight checker was run.

## Validation

The mandatory dry run and push are executed using the launcher's deliver.py; their final output is the delivery evidence.
