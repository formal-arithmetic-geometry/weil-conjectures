# Q25 stage-1 delivery: lem-trf-cotangent-bar-term-identifications

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-cotangent-bar-term-identifications.json`: item, split, five proof steps; not a Mathlib leaf.
- `citations.json`: twelve verbatim statement excerpts, one for each step/node pair.
- `searches.jsonl`: actual five search results from the prescribed command.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaf reused: `lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`.

## Attachments

None. Searched the project source under lean/WeilConjectures for the exact blueprint tag and cotangent/bar/colimit concepts. No declaration states these three derived isomorphisms with their specified comparisons. The local Sheaf cotangent-model module is source material, not a finished attachment.

## WANTED

None. All sources needed are present locally.

## Corrections and scope

The item statement is unchanged. The initial proof was empty; its dependencies already give the hard comparison results. No clause is moved to a new node. The proof now checks flatness at every polynomial value, the equality of presheaves including their restrictions, the types and orientation of each comparison, and the standard free representative after arbitrary scalar extension.

The published local Stacks text of sites-cohomology Tag 08Q8 has an ill-typed displayed functor order (and says right adjoint in its proof). I use the explicitly corrected, typed statement of the existing `lem-trf-derived-colimit-change-rings`, not that display literally. This existing source correction requires no change to this item. The common small skeletons and size convention come from the existing lower-shriek statement. The historic blueprint support chain is preserved: this is the old transitivity Step 4 auxiliary input, not a replacement proof of the current curve-local-term unit. The current main-20261015 ancestor and the chapter/unit records were read.

## Not duplicates

No new nodes were created. Whole-DAG searches for 00RX and polynomial differentials found the arbitrary-variable polynomial-basis Mathlib leaf, which is reused. Whole-blueprint searches `cotangent` and `bar term` found no exact statement of the item; same_as remains empty. The lower-shriek, sheaf-model and change-of-rings statements are separate general tools already in the DAG, rather than newly named clauses of this item.

## Review by Q25

I read cotangent.tex Tag 08PU (lemma-compute-cotangent-complex), Tag 08QW (lemma-triangle-compute-lower-shriek), and the full three-term identification in Tag 08QX (proposition-triangle), together with sites-cohomology.tex Tag 08Q8 (lemma-change-of-rings), Tag 06YQ (lemma-bounded-flat-K-flat) and the ordinary-ring version more-algebra.tex Tag 064K. There are no new-node sources to review. I read the full statements of all eight cited nodes, rather than using constructions hidden in their proofs.

Step 1 uses the arbitrary-variable polynomial-basis statement, whose last sentence explicitly supplies the basis after any scalar extension P to B. The direct-sum argument for preservation of short exact sequences is written out; it covers infinite sets by finite support. No flatness of B to C is used. The existing differential-presheaf-ses statement supplies the setting but is not used to infer flatness from a coordinate decomposition involving Q.

Step 2 cites the lower-shriek statement for the small pair/presentation categories, precomposition inverse image and the actual natural comparison isomorphisms with their chain formula. The bar theorem states that its complex represents derived colimit; the definition of bar-system data alone would not assert existence, so I cite the theorem. Evaluating at an object and at an arrow proves the tensor/precomposition equality without invoking an uncited tensor-exactness theorem.

Step 3 reads c_2 and c_3 with coefficient C and theta for A to C and B to C. The lower-shriek theorem covers arbitrary degree-zero module presheaves, and the sheaf-model theorem's theta has exactly the source L pi_! F and target the standard cotangent complex. Their composite therefore has the asserted source and target; this is composition of the stated maps, with no map-transport claim hidden in it.

Step 4 uses c_1 with the C-module presheaf F_1 tensor_B C, then the flat-presheaf clause of change-of-rings on C_1 with R=B and S=C. Its hypotheses require flat values of F_1, already proved, and impose no flatness on C. Its statement explicitly gives the generator identification, the bounded-above flat bar model and derived scalar extension. Finally theta_{B/A} is taken through the derived scalar-extension functor. No appeal to the transitivity triangle being proved above this item is made.

Step 5 uses resolution-coherence for the actual standard complex, polynomial terms, and zero positive degrees. The arbitrary-variable basis leaf proves those terms free. The bounded-above-flat K-flat theorem applies on the one-object identity-cover site: this is a small site, its ring sheaf is B, and its module sheaves are ordinary B-modules. The derived-change-of-rings theorem then says exactly that K-flat models compute extension of scalars; applied to the identity resolution of this standard complex it proves the specified termwise representative. These two off-unit citations are declared as generic tool uses in split_report. Neither replaces any unit proof step.

I checked delivery-errors B through E: no new statement-only files or duplicated clauses; no unstated object or extra hypothesis; no added Lean data; all non-elementary inputs are cited by statement; the elementary finite-support argument is explicit; no circular dependence on transitivity; all isomorphisms are stated in derived categories, not merely on homology. Every citation quote was checked as a literal substring of the current cited statement. No individual step exceeds 2000 characters. Statement dependencies remain those used by the unchanged statement, and proof_deps is exactly the union of uses.

Small cases checked: zero coefficient rings and the empty variable set give zero differential modules and no flatness exception; infinite variable sets give direct sums, not products; A=B or B=C is allowed throughout; the non-flat map B=Z to C=Z/pZ still uses a free B-model, so ordinary tensor of that model is valid without claiming that tensoring arbitrary quasi-isomorphisms preserves them. The construction never chooses polynomial coordinates naturally: coordinates prove freeness, while the comparison maps are the canonical maps of the cited statements.

The five actual Mathlib searches (two semantic phrasings, Loogle, grep, LeanSearch) were read. Extension.cotangentComplex and its scalar-extension identities are maps from a conormal module to a cotangent space, not the full derived cotangent object or category-colimit comparison. I read Extension/Cotangent/Basic.lean:53-117 to check this. The polynomial-basis hit is already represented by the existing leaf; its source Kaehler/Polynomial.lean:60-105 was read. No new leaf or lemma is warranted by these results.

## Unfinished work

None in this one-level split. The existing cited unsplit nodes remain their own independent stage-1 tasks.
