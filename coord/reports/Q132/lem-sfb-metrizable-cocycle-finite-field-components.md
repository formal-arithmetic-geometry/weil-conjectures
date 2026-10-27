# Stage-1 delivery: lem-sfb-metrizable-cocycle-finite-field-components

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-metrizable-cocycle-finite-field-components.json`: statement unchanged; six-step split, reusing four existing nodes; no new nodes and no new Mathlib leaves.
- `citations.json`: four verbatim statement quotations, covering every proof-step citation.
- `searches.jsonl`: five real item searches, with their service results; the item retains the earlier recorded searches as well.
- `report.md`: this report.

## Attachments

None. Searches in the live `lean/WeilConjectures/` for the item's blueprint tag, metrizable quotient terminology and finite-subfield projection terminology found no project declaration stating the item. Related finite-subfield declarations concern characteristic-p algebra, not norm-topological algebraic p-adic coefficients. No compiler or Lake command was run.

## Literature wanted

WANTED: an exact norm-topological reference for the combined metrizable cocycle and pointwise finite scalar decomposition in this item. The inherited source already requests one. The argument here is explicitly agent-written. The blueprint's main-20261015 direct-images proof paragraph (3) supplies the direct-image motivation only, not an analytic theorem or its proof. The existing countable-exhaustion node cites Stanford Weil II seminar L19, Proposition 1.1.9, first bullet, p. 3; I read that passage and its countability assertion. The existing projection node supplies the stronger norm-one projection assertion, without completing the algebraic closure; its own exact external reference remains wanted. No SGA source is used.

## Findings and changes

The live item was unsplit, with no prior sandbox node, report or search log. No released repair note exists. I retained its complete statement, statement dependencies, source, creation stamp and blueprint ancestry. The three main inputs already exist: `lem-sfb-profinite-metric-function-quotients`, `lem-sfb-algcl-countable-closed-finite-cover`, and `lem-sfb-norm-one-finite-subfield-projection`. Creating new nodes for their specializations would duplicate existing obligations. The noncontractive continuous-linear retraction node is insufficient for uniform approximation, so it is deliberately not used.

Whole-DAG concept searches and whole-blueprint searches for metrizable, finite subfield, and cocycle were read. None of the blueprint hits states this analytic item. The ancestor tool confirms the inherited null blueprint ancestor; the precise inherited paragraph (3) motivation and old-proof steps 4–5 are retained in `blueprint.from.place` and explained in `split_report.blueprint`. Chapter and unit routes remain unchanged. The compact-product node is a generic topology tool; its use is declared in `split_report.tool_uses` and does not replace a unit argument.

The five fresh logged Mathlib searches used two different semantic phrasings, Loogle, grep and LeanSearch. All services answered. Hits concern p-adic additive characters, locally constant finite approximations, strong operator topology, compact convergence and mapping-cone projections. They do not supply all the item's clauses or a one-line specialization proving it. They are recorded with their actual queries and results. There are no new nodes requiring further leaf searches.

## Not duplicates

No new node is created. All substantive auxiliary results are existing DAG statements, read before citation.

## Review by Q132

I read delivery-errors B through E, the worker brief, the stage-1 contract, the three blueprint levels in SETUP, GOAL, the item's chapter and unit records, and the current main-20261015 direct-images proof. I checked the item against the norm topology on the algebraic closure rather than its completion. I also read the statements of every proof dependency and the defining coefficient/size statements. No imported statement correction or statement dispute was necessary.

Step 1 uses exactly the existing metric-function factorization statement: the source is a profinite space times a positive finite power of a profinite group, and the target is an arbitrary metric space, without a completeness assumption. Its conclusion explicitly supplies continuous surjections and a group homomorphism, simultaneous use of that homomorphism in every coordinate, metrizability and empty S. These are precisely the data used. No proof-internal construction from that node is assumed.

Step 2 is the termwise differential calculation: lift the parameter and each group element, use q(ab)=q(a)q(b), and evaluate every term in the displayed differential. Thus the descended function really is a cocycle, including n=1. Composition of the two continuous surjective homomorphisms proves the finite-quotient clause. Neither assertion needs another descent or group-cohomology theorem.

Step 3 uses the countable-closed-finite-cover node for all four relevant properties: increasing fields containing E, finite degree, closedness in the given norm topology, and union equal to Omega. I checked its L19 reference and its complete DAG statement. The norm-one projection node is applied separately to each finite field, with the identical extended absolute value. Its statement explicitly gives F_i-linearity, fixing F_i, the bound one and continuity without completeness of Omega. It does not promise pairwise commutation, and the proof never assumes it. These nodes are in the item's own unit.

Step 4 uses only the already chosen data: the inclusion F_(i-1) in F_i preserves the restricted absolute value, so subtraction is continuous into F_i. Additivity commutes with each signed differential summand. No F_i-linearity of p_(i-1), or of their difference, is asserted or required. If a scalar lies in F_j, both projections fix it for i >= j+1; this proves pointwise eventual zero with the correct index, including i=0 separately.

Step 5 cites the compact-product statement, which applies to arbitrary set-indexed families of quasi-compact spaces and hence to the finite product here. I checked that its statement, not just its source, gives exactly this. Beyond that citation the proof is the explicit finite-open-cover argument: continuity makes inverse images of epsilon/2 balls open, compactness selects finitely many centres, and the exhaustive increasing fields contain all centre values at a common index. The ultrametric estimate is written out and gives a uniform bound epsilon/2, hence a strict epsilon bound on the supremum. A radius-one version proves boundedness, so no unproved compact-image or supremum-norm theorem is hidden. This is an elementary application of compactness and the contraction inequality, not a new analytic lemma requiring another node.

Step 6 is finite telescoping and the explicit maximum-of-two-errors estimate. The first component is p_0 z_0; for every later component the two uniform errors tend to zero. This supplies all convergence assertions while retaining the pointwise statement from step 4. No infinite sum in the incomplete field is formed; the given cocycle is the exhibited uniform limit of the finite partial sums.

I tested empty S (surjectivity forces empty S_0, norms are zero), singleton S, trivial K or G, the zero cocycle, n=1 and E=Q_l. A compact image need not lie in one finite field, and the proof does not claim that it does. Each value and each finite set of chosen centres does lie in some stage, which is exactly what the argument needs. In particular, pointwise eventual vanishing is not silently strengthened to a uniform cutoff. Every step is shorter than 2000 characters; the largest is the explicit compactness estimate. All four citation quotations are literal substrings of their current DAG statements and proof_deps is exactly the union of step uses.

## Unfinished work

No stage-1 obligation remains in this item. The cited nodes retain their own stage status and future formalization obligations. This delivery does not claim a Lean proof.
