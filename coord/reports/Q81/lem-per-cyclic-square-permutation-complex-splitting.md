## Worker report

Files written:
- dag/nodes/sec-deligne-laumon-a1/lem-per-cyclic-square-permutation-complex-splitting.json: existing statement, now split in six steps; not an exact Mathlib match.
- citations.json: a verbatim statement excerpt for every node used by each numbered proof step.
- report.md: this report. searches.jsonl was written by the required search command.

There are zero new nodes and zero new Mathlib leaves. No unit record changes: this is not the unit's key node.

Attachments: none. Searches under lean/WeilConjectures by the exact blueprint tag, cyclic/square/permutation, generator-minus-one, and the relevant representation directories found no declaration stating this item. The procyclic cohomology file computes group cohomology, not this derived splitting.

WANTED: none.

The item statement and its statement dependencies are unchanged. There was no earlier sandbox split or report to preserve; the inherited six Mathlib-search records remain intact. The item source explicitly describes an agent-formulated finite-level replacement for the permutation-module argument, rather than a verbatim theorem of ILO. I read ILO XVI Proposition 3.4.5 and its proof, printed pp.246--248, especially the root tower on p.247 and the paragraph after Lemma 3.4.9 on p.248. The proof here is consequently marked by=agent. It proves exactly the finite-level homological input already requested by the parent's Step 6. It needs no assertion about the relative functor F or its first nonzero cohomology, and no SGA result.

The new proof constructs the roof itself. Put R=Map(C,A), use the fibre-sum p:R -> Map(Q,A), and take Z in degrees -1,0,1 with terms A, A direct-sum R, R. Its differentials are (0,constants) and (0,tau-1). The map Z -> K has components constants+p and p; the map Z -> A[0] direct-sum A[-1] has components projection and summation. Both induce identities on H^0 and H^1. The reason the first chain map exists is precisely p(constants)=ell*constants=0.

Nothing remains unfinished in this one-level split.

## Not duplicates

No new node was created, so there are no new/existing pairs to distinguish. Whole-DAG searches for cyclic permutation, square-order, fibrewise summation, and permutation modules, and blueprint_refs.py searches for cyclic, permutation and quasi-isomorphism found no blueprint statement equivalent to the item. In particular det-base-field-cd-inflation concerns inflation on cyclic group cohomology, not a derived isomorphism between the two displayed complexes. Existing discrete-module structural and abstract-derived-category nodes provide exactly the generic tools used here.

## Mathlib searches

All new searches ran through msearch.py Q81 lem-per-cyclic-square-permutation-complex-splitting, and their exact query strings and output summaries are recorded in the item and searches.jsonl. Both semantic phrasings returned the finite cyclic periodic resolution and its augmentation; LeanSearch also returned finite cyclic homology/cohomology formulas. I read Mathlib/RepresentationTheory/Homological/FiniteCyclic.lean, especially lines 101--125 and 193--246. Its resolution_quasiIso concerns the entire augmented periodic chain complex, not the two-term inflated complex in this statement; a fibre-sum roof is additional work, so the item is not a one-line specialization. The mapping-cone degreewise splitting hit only splits the underlying short complexes of a cone triangle and does not assert formality of this complex. The first Loogle query gave no hits; the namespace-only norm query was rejected as an unknown identifier (recorded as such), and the subsequent quoted-name query returned the six periodic-resolution declarations. The two source greps returned unrelated splitting-field facts and the expected resolution/augmentation lemmas, respectively. No unavailable service was recorded as a negative match.

## Review by Q81

I checked the live item and its parent lem-per-kummer-root-regular-divisor-purity, the chapter and unit records, the current latest blueprint unit/section and ancestor proof, and the three cited node statements in full. The historical Step 3 ancestry is retained. This is a finite algebra calculation below the unit, so neither the chapter statement nor the unit proof route changes. ILO provides the provenance just described; the finite roof is an agent-written argument, not attributed to an unproved sentence in the source. There are no new-node sources to check.

Step 1 uses def-exc-discrete-modules-category for objects and equivariant maps, and lem-exc-discrete-modules-abelian-structure for underlying-module kernels, cokernels and biproducts. The latter's hypotheses really hold: C is finite discrete, hence profinite, and A=F_ell is finite. I read the Stacks 04JP definition-G-module-continuous and 0A2H section-group-cohomology paragraphs. This structural lemma is declared as a generic off-unit tool, rather than silently used as a replacement geometric route.

Step 2 is an elementary calculation, written out rather than cited: a cyclic difference vanishes exactly on constants, summation kills differences, and the displayed partial-sum recurrence produces a preimage of every zero-sum function, including the cyclic wrap at zero. A delta function proves summation is onto. The calculation works in characteristics dividing the cycle length; it never divides by ell. The induced actions on both kernel and cokernel are trivial.

Step 3 checks the precise equivariance of p with the action h(q-c), the chain identity pD_C=D_Qp, the vanishing p i_C=0, and epsilon_Q p=epsilon_C. All follow by reindexing finite sums over the actual fibres of C -> Q, each of cardinality ell. This checks the square-order hypothesis at its only essential use.

Step 4 cites def-weil-abstract-derived-category for cochain complexes, morphisms and cohomology, and explicitly constructs every nonzero component of both maps. I checked the two adjacent chain equations for each map; especially the equation out of degree -1 is p i_C=0, not a presumed splitting of modules. Step 5 uses that same node's definition of quasi-isomorphism after computing ker/im and both induced maps. The H^0 contribution from R is removed by the preceding differential, and H^1 is the summation quotient. This avoids confusing a degreewise vector-space splitting with an equivariant chain splitting.

Step 6 takes only localization from def-weil-abstract-derived-category: the two already-verified quasi-isomorphisms invert and compose in the stated direction. I read Stacks 05RR section-derived-categories and 05RU definition-unbounded-derived-category. The target complex has degree one A for A[-1], so no shift-sign or indexing convention is suppressed. This is an isomorphism in the ordinary derived category.

For delivery-errors B--E: the statement is self-contained and unchanged, all definition citations already exist, all quoted text was checked as a literal substring of the corresponding statement, and no fact is taken from a cited node's proof. No new-node form, Mathlib-leaf, duplicate or restated-clause issue arises. The non-elementary categorical fact is cited; the remaining steps are explicit finite sums, kernels/images, chain equations and the definition of localization. No proof step exceeds 2000 characters or hides a standard comparison/Ext lemma. I corrected the source label for 05RU after checking the Stacks tag map; I also changed the rejected Loogle query's verdict so it is not represented as evidence of absence.

For small cases I checked ell=2 explicitly: the four-point constant function sums to zero in each two-point fibre, while the delta function still has total sum one. I also checked ell=3 and ell=5 by modular linear calculations on every delta basis vector: pD=Dp, epsilon p=epsilon, and p(constants)=0, together with explicit primitives of every zero-sum basis vector for both cycle lengths. At ell=2 the negative signs reduce correctly. The zero-cohomology degrees -1 and outside [-1,1] are accounted for in the proof. Without the extra root level the fibre cardinality would be one, so the degree -1 chain equation would fail, as expected.
