# Worker report: lem-trf-field-complex-cohomology-splitting

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-field-complex-cohomology-splitting.json`: existing statement node split into ten proof steps, statement unchanged; no whole-item Mathlib match.
- `citations.json`: verbatim statement quotations for every citation of every step.
- `searches.jsonl`: actual searches made with the prescribed msearch command; six successful queries, including two different semantic phrasings. The node retains its inherited search records and adds these current searches.
- `report.md`: this report and signed self-review. `write_split.py` is sandbox-only preparation material, not a delivered project file.

New nodes: 0. New Mathlib leaves: 0. No Lean files or unit records written, and no compiler, Lake or build tools run. No direct git command or write in either reference repository.

## Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the exact item id, cohomology/splitting terminology and homotopy-equivalence terminology. There is no declaration stating the whole item. Existing contractible-cone and K-injective infrastructure is not an attachment to this theorem. The exact upstream master is not treated as completed proof evidence.

## WANTED

None. The relevant blueprint and Stacks source files are present. The detailed contraction and retract proof is an agent-written expansion, explicitly recorded with `proof_origin.by = agent`; the short blueprint paragraph does not itself contain that proof.

## Problems found and changes

The imported item was a statement-only extraction from the returned Step 2 of `prop-trf-karoubi-independence`; it had no proof or proof dependencies. Its statement is true, including for unbounded complexes in its first paragraph, and no correction or added hypothesis is needed. The original source paragraph asserts trace independence, whereas this item provides its field-complex input. The current main-20261015 paragraph, the item's extraction place and the parent node's Step 2 were read together, so the split does not claim that the whole field lemma is literally printed in that paragraph.

The proof now supplies the actual degree -1 contraction, the homotopy reducing a chain map to its cohomology map, the inverse of each quasi-isomorphism, and the localization argument. In particular it does not silently pass from bounded finite complexes to arbitrary unbounded complexes, or invoke a full-faithfulness assertion valid only on single-degree complexes. It constructs image/kernel summands and proves the inverse and intertwining identities for arbitrary alternative splittings.

The chapter/unit records `sec-trace-formula` and `sk-thm-trace-transport` were read. This field-complex tool lies below the trace-transport field-stage argument and the first sentence of the parent proposition, and replaces no unit-level route. The item is not the unit's key node, so no unit realization record is changed. The existing blueprint ancestry already has a precise place and is retained; `same_as` is empty after the whole-blueprint searches.

## Existing-node and Mathlib comparison

Searched the whole DAG for complements, homotopy categories, cohomology splitting, vector-space projectivity, finite-dimensional modules and localization at isomorphisms, and used `tools/blueprint_refs.py ancestor` and its searches for `cohomology splitting`, `homotopy`, `complement`, `homotopy category`, `graded cohomology`, and `vector space is a projective`. No blueprint node states the whole item. `lem-pod-cohomology-of-dual-over-field` proves perfect duality of bounded finite complexes, not the unbounded cohomology Hom bijection or the idempotent comparison; its proof also uses the existing vector-space projectivity node. It is not used as a substitute for the item. The existing `lem-weil-pbc-vector-space-projective` and `def-weil-pbc-projective-module` already supply exactly the lifting fact needed, so no complement or split-sequence node was created.

The six current Mathlib queries are copied verbatim from `searches.jsonl` into the item's `mathlib_searches`. Both LeanFinder responses, the LeanSearch response, the Loogle response and the grep hits were read. `Submodule.exists_isCompl` is a complement theorem only. `DerivedCategory.instFullSingleFunctor` and its faithful companion concern a fixed single-degree embedding; source `Mathlib/Algebra/Homology/DerivedCategory/FullyFaithful.lean` was opened. The K-injective and K-projective results require those additional complex properties, which are not hypotheses of the item; source `DerivedCategory/KInjective.lean` was read, including `Qh_map_bijective` and `quasiIso_iff`. A degreewise projective unbounded complex cannot simply be declared K-projective over an arbitrary ring. Here the explicit contraction proves what is needed over a field. `ShortComplex.Splitting` concerns a short complex, and its source `ShortComplex/Exact.lean` was opened; it does not state this unbounded result. The Karoubi/cochain equivalence is completion infrastructure, not the cohomology model theorem. These are useful neighboring results, but none gives every clause by a one-line specialization. The inherited earlier search entries are retained as inherited records; no claim is made that those earlier queries were executed during this session.

## Not duplicates

No new nodes. The projectivity and finite-generation notions are reused from existing nodes. Complement existence follows immediately from the cited lifting property. The localization calculation consists of two applications of its defining universal property. Neither warrants a new node. The cohomology-model and idempotent clauses remain proved in the item rather than being repackaged as new statements of those clauses.

## Review by Q11

I read the current main-20261015 `prop-trf-karoubi-independence.proof.md`, the existing extracted statement and the parent proposition's field step. For the linear algebra I opened `literature/stacks-project/fields.tex`, labels `lemma-vector-space-is-free` and `lemma-field-semi-simple` (Tags 09FN and 09FP), and `algebra.tex`, `lemma-characterize-projective` (05CF). For the passage to the derived category I opened `derived.tex`, `definition-unbounded-derived-category` (05RU), where the localization is explicitly of the homotopy category. No SGA source is used. All eight cited node statements were opened, not inferred from their titles.

Step 1 uses the actual definitions of complexes, cycles and boundaries in `def-weil-abstract-derived-category`, the assertion that every vector space is projective in `lem-weil-pbc-vector-space-projective`, and the explicit lifting-along-surjections equivalence in `def-weil-pbc-projective-module`. Both targets of the surjections are vector spaces, so the hypotheses hold without finite dimension. The sections are lifted identities; subtracting their values proves the direct-sum decomposition and its uniqueness. This is the one step marked non-elementary because it invokes vector-space projectivity.

Step 2 is a direct block calculation, with the cohomology quotient formula from `def-weil-derived-category-cohomology-functor`. The inverse differential is defined only on the boundary block, where the previous step proves it invertible. On the boundary block `dh` is identity, on the transverse block `hd` is identity, and on the cohomology block both vanish. The maps induce identity on cohomology. This proves the assertion for any given complements as well as the existence of choices.

Step 3 again uses the cited cohomology functor's cycle formula: a homotopy difference on a cycle is an actual boundary. Its displayed homotopy `h_Q f + A_Q f h_P` expands to `f - A_Q f A_P`, since every factor other than the homotopies is a chain map. Consequently maps with the same cohomology are homotopic; this is proved here, not assumed from a cited definition.

Step 4 uses the quasi-isomorphism definition in `def-weil-abstract-derived-category` and cohomology functoriality in the cited cohomology node. The map `a_P H(f)^{-1} b_Q` is well typed and both composites induce identity, so the preceding step proves its two homotopies. This avoids assuming that a derived inverse has a chain-map representative before proving it.

Step 5 uses exactly the localization description included in `def-weil-abstract-derived-category`. Because all inverted arrows already have inverses in `K(F)`, the identity factors back through the localization. The fully faithful restriction part of that same universal property descends the other inverse natural isomorphism. This is a two-application defining-property calculation, not an uncited theorem about derived Hom. It does not require a calculus-of-fractions or small-roof assumption.

Step 6 uses the chain-map definition from the abstract derived-category node and the functoriality from the cohomology node. Between zero-differential complexes chain maps are precisely degreewise families, and the homotopy relation is equality. Conjugation by the already constructed maps and Step 5 proves the asserted bijection. Since the conjugating maps induce identity, this is the canonical cohomology map in the statement. The product is over all integers and is not replaced by a finite sum.

Step 7 opens and uses each of `def-weil-point-fd-complexes`, `def-weil-finite-dimensional-subspace`, `def-weil-finitely-generated-module`, `lem-weil-pbc-vector-space-projective`, and `def-pc-perfect-ring-complex`. The first says bounded finite-dimensional cohomology, not termwise finite dimension of an arbitrary representative. The second and third identify the finite spanning condition. Projectivity holds for each cohomology term, and the last defines perfection by the bounded projective model just constructed. No finite Tor assumption or sheaf comparison enters.

Step 8 uses functoriality in the cohomology node, the stated cohomological support condition in the point-complex node, and the finite spanning definition in the finite-dimensional node. For an idempotent `E`, `x = E x + (1-E)x`, its two terms lie in image and kernel, and applying `E` proves that the sum is direct. The finite spanning sets project to spanning sets of both summands. This checks finite dimension without hiding a submodule-finiteness theorem.

Step 9 uses the cohomology functor node for preservation of compositions. The splitting equations follow from Step 6's injectivity. Commutation with the idempotent proves preservation of image and kernel by the two element formulas written in the step, so the block of `ve` on the kernel is zero and the image block is the restriction `rvi`. This transports a verified equality via an already proved faithful functor; no comparison theorem is left implicit.

Step 10 uses only the category supplied by `def-weil-abstract-derived-category`. I checked the domains of `r'i` and `ri'` and both inverse products. The identities `r'e=r'` and `ei=i` reduce both sides of the intertwining equation to `r'vi`. This applies to arbitrary splittings, as the statement requires, and is independent of how the cohomology model was chosen.

For delivery-errors B--E I checked that there are no new nodes with hidden proofs, undefined data, duplicate statements or unrun search records. Every step's `uses` is supported by a verbatim quotation in `citations.json`, and the proof-dependency list is exactly their union. All proof steps are shorter than 2000 characters (the largest has 818), and none hides a separate comparison lemma: the chain homotopy and the localization inverse are written explicitly. No statement clause is moved into a new node. The only substantive external fact is vector-space projectivity, supplied by the existing leaf and its lifting definition.

Small cases checked by the formulas: the zero complex; a complex concentrated in one degree; a two-term complex with identity differential (cohomology zero and `dh+hd=1`); arbitrary zero-differential complexes with infinitely many nonzero degrees; and a zero-differential graded space with infinite-dimensional terms. None of Steps 1--6 uses boundedness. For the retract part, `e=0` yields zero image and full kernel, `e=1` yields full image and zero kernel, and `E=diag(1,0)` with a commuting block-diagonal endomorphism gives the advertised blocks. The formulas work in characteristic two as well: `1-E` remains an idempotent and `E(1-E)=0`. Finite support and finite dimension are used only where supplied by the hypothesis in Steps 7--9. No statement dispute or source correction was necessary.

## Unfinished work

None in the one-level split. The proof is natural language only, as required. Server dry-run validation and direct push are the remaining delivery operations.
