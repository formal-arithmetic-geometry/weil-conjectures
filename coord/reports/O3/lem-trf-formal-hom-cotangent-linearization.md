## Worker report

Item: lem-trf-formal-hom-cotangent-linearization. Stage 1 only, direct delivery by O3.

Files written: dag/nodes/sec-trace-formula/lem-trf-formal-hom-cotangent-linearization.json (statement unchanged; complete five-step split), citations.json (one verbatim statement quote for every step citation), and this report. Searches are recorded in searches.jsonl. No Lean was written and no compiler, Lake, build, local preflight or git command was run.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves. The existing lem-weil-pbc-power-series-quadratic-ideal supplies the only non-elementary coefficient fact needed by the argument.

## Attachments

None for the item. Searched the project source for the exact blueprint tag and for cotangent, formal-hom and MvPowerSeries notions. MvPowerSeries.exists_firstOrder_coordinates in WeilConjectures/RingTheory/PowerSeriesFirstOrderCoordinates.lean:49 states existence of a ring isomorphism to a square-zero extension and an ideal-membership criterion. Its statement does not specify its coefficients and does not give arbitrary homomorphism linearization or composition. It is not an attachment to this item; its implementation is not used as an unstated strengthening. MvPowerSeries.mem_span_X_sq_of_coeff_eq_zero in PowerSeriesQuadraticIdeal.lean:45 already belongs to lem-weil-pbc-power-series-quadratic-ideal, which is reused unchanged.

## Literature

WANTED: none.

Read Stacks curves.tex, Tag 0C4B, lemma-fitting-ideal-well-defined, especially the final paragraph asserting invertibility of the coordinate Jacobian and the chain rule, with details omitted. Also read more-algebra.tex, Tag 07EI, lemma-fs-implies-regular, the construction of f_1 and the displayed first-order quotients. The former motivates this auxiliary statement; the latter supplies the source context of the existing quadratic-ideal lemma. The proof here expands the missing coefficient argument and is marked proof_origin.by = agent; it is not presented as a verbatim proof supplied by Stacks.

Read GOAL.md, SETUP.md's three-level rule, the stage-1 brief and stage document, delivery-errors B through E, the recorded unit/chapter, and the current literature/blueprint/latest trace-formula chapter, sk-i-curve-zero unit, and lem-trf-local-term-locality statement/proof. This is an auxiliary of the existing formal-Jacobian coordinate-change argument below that blueprint ancestor, not a change to the unit or chapter route. Blueprint searches for power series, cotangent, linear coefficient, linearization and 0C4B found no imported node stating this item. DAG keyword searches located the quadratic-ideal and first-order-coordinate nodes, avoiding redundant new nodes.

## Mathlib searches

Retained the inherited 2026-10-22 searches. Ran the required msearch commands for LeanFinder, Loogle, grep and LeanSearch on 2026-10-23 and read their hits. A second LeanFinder query using augmentation ideals found Ideal.mapCotangent_toCotangent and Algebra.Generators.repr_CotangentSpaceMap. Read Mathlib/RingTheory/Ideal/Cotangent.lean:211-234: the induced map exists and evaluates on representatives but provides no coefficient basis. Read Extension/Cotangent/Basic.lean:508-514: the basis there is for a polynomial-presentation cotangent space, not the ideal of variables in a formal-series ring. Read MvPowerSeries/Basic.lean:513-543 and Inverse.lean:171-183: the returned map and its locality theorem are coefficientwise maps with the same indexing set. None is an exact or one-line specialization giving all clauses of this item. No unavailable service was recorded as an absence. Exact locally executed queries and their verdicts are appended to mathlib_searches and agree with searches.jsonl.

## Problems in the imported material

No statement dispute or source error was found. The item had an empty proof and no proof dependencies. A possible tempting shortcut was rejected on its actual statement: the existing first-order-coordinate node asserts only existence of an isomorphism, not that its second coordinates are the linear coefficients. The split instead uses the precise quadratic-ideal criterion and computes the coordinates itself. The current ancestor's trace argument is not itself used as a coefficient theorem.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. Reused lem-weil-pbc-power-series-quadratic-ideal, which is strictly weaker than the item: it only implies square-ideal membership from vanishing constant and linear coefficients. Did not create a node restating the basis clause or the map clause.

## Review by O3

I checked the statement against the omitted cotangent detail of Stacks 0C4B rather than treating that tag as an already-proved coefficient theorem. The chosen finite variable sets, arbitrary field, arbitrary F-algebra maps preserving variable ideals, rectangular row convention and zero-variable cases are all retained. There is no new node whose source needs separate checking. I opened the full statements of every cited node and produced citations.json from those statements, not their proofs.

For step 1, def-weil-pbc-multivariate-power-series explicitly defines coefficientwise addition and the finite Cauchy product. Its exponent-e_i product has just two summands; the displayed formula therefore proves both coefficient linearity and vanishing on products of elements of the variables ideal. Finite sums of products suffice for ideal squares. This is an elementary calculation from the definition, including the constant-series embedding it specifies.

For step 2, lem-weil-pbc-power-series-quadratic-ideal states exactly that zero constant and all zero linear coefficients imply membership in N^2, for any commutative coefficient ring and a finite variable set, with the empty set allowed. Here F is a field and each of m,n,r is a finite natural number, so all its hypotheses apply. Subtracting the explicitly computed constant and linear terms gives precisely its vanishing hypotheses. This proves the remainder membership; the rest of the step explicitly gives both inverse linear maps, rather than assuming a basis theorem. Step 1 proves the reverse vanishing needed to descend coefficients. This node is declared a generic off-unit tool in split_report.tool_uses, with the concrete purpose stated, and no top-level maintainer tool_uses field is set.

For step 3, no external theorem is taken without a citation. The finite-product definition of the ideal square shows its image lies in the target square; this is written out. The quotient map is consequently independent of representatives. Additivity and fixing F prove scalar linearity directly. Constant preservation follows from h-c(h) lying in the source ideal, not from any continuity assumption or infinite substitution. These elementary arguments apply equally to theta and its composite.

For step 4, def-weil-matrix states what the entries and rectangular index sets mean; the multiplication formula is the explicit finite sum in the item's assertion. The image of the step-2 remainder lies in the target square by step 3 and has zero linear coefficients by step 1. Extracting a coefficient from the remaining finite sum proves the row formula with indices i in the source and j in the target. Nothing is inferred from the proof of another node.

For step 5, the same matrix-definition node provides the indexed entries; quotient composition is checked on an arbitrary representative. I wrote out the (i,k) entry of the composite as the sum over the intermediate variable j. This checks the order L_psi L_theta and proves the identity by Kronecker coefficients, without appealing to a general functoriality theorem. The elementary finite-sum definition of matrix multiplication is stated explicitly. There are no hidden comparison or basis-identification claims in long proof steps; each step is under 2000 characters.

I tested the hypotheses and edge cases on m=0, n=0, r=0, and m=n=1 with psi(t)=az+bz^2. In the latter case the matrix is (a); taking theta(z)=cw+dw^2 gives the composite entry ac in the stated order. In positive characteristic, e.g. psi(t)=z^p, the map on cotangent spaces is zero, as is its linear coefficient. For n=0, preservation of the target zero ideal forces psi to annihilate every t_i and the normal form forces it to be the constant-coefficient map; the rectangular matrix formula is still valid. For m=0 the source cotangent space is zero and the unique algebra map is the scalar embedding. For all empty cases, the statement's matrix and ideal conventions agree with the empty finite sums. No assumption of separability, characteristic zero, continuity, bijectivity or equality of m and n is introduced. No statement or inherited blueprint metadata was changed.

Against delivery-errors B-E: there are no new statement-only nodes or new leaf claims to audit; notation remains self-contained TeX; sources name actual Stacks tags and labels; every non-elementary input is the precisely quoted quadratic-ideal node; the proof carries the argument and does not rename its clauses as nodes; only finite sums are mapped by arbitrary algebra homomorphisms. No requested part remains unfinished.
