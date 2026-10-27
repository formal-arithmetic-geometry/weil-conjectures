## Worker report

Q57, stage 1, 2026-10-24. Item: lem-sfb-bundle-sobolev-rellich.

The item statement is unchanged. I wrote a six-step proof, replacing the empty proof, and created three statement-only analytic prerequisites. No Lean was written or compiled. All writes are in this item's sandbox. No agents were started.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-bundle-sobolev-rellich.json: item, status split; complete finite-chart argument, exact proof dependencies and blueprint explanation.
- dag/nodes/sec-six-functors-basics/lem-sfb-euclidean-sobolev-graph-mollification.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-sobolev-chart-overlap-bound.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-euclidean-fixed-support-rellich.json: statement, unsplit, no Mathlib match.
- citations.json: one literal full-statement quote for every cited node in each numbered step.
- searches.jsonl: actual output summaries recorded by msearch.py; retained unchanged.
- report.md: this report, including the author's review below.

## New nodes

lem-sfb-euclidean-sobolev-graph-mollification: statement, unsplit. This is an analytic lemma about functions on Euclidean space: distributional faithfulness, a closed derivative graph, and smoothing inside a prescribed open set. It has neither manifold bundle completions nor compactness. It includes order zero so the item's proof can construct the measurable L2 completion from local L2 completeness.

lem-sfb-sobolev-chart-overlap-bound: statement, unsplit. It estimates one explicitly defined localization map between two charts of an arbitrary manifold. It does not assert atlas independence, identify any completion, or prove compactness. The item derives atlas independence by the actual finite sum and both inequalities.

lem-sfb-euclidean-fixed-support-rellich: statement, unsplit. It is the Euclidean first-order compactness input for a fixed compact support; no bundle or global manifold appears. The item still performs the finite subsequence extraction and reconstruction estimate. The fixed support is essential, as translations of a nonzero compactly supported function demonstrate.

All three are self-contained statements with real coefficients and weak derivatives defined by test functions. Their proof arrays and proof dependencies are empty. Each was searched by LeanFinder in two phrasings, LeanSearch, Loogle, and logged Mathlib grep. There are zero Mathlib leaves.

## Attachments

None. Searches of lean/WeilConjectures for the literal item id and Sobolev, Rellich, mollification and weak-derivative terms found no declaration. A supplementary search of lean/Sheaf found no corresponding implementation. The existing item also records no upstream declaration. No claim of completion is based on a sorry declaration.

## WANTED

WANTED: Demailly, Complex Analytic and Differential Geometry, VI §1 (1.4), VI §2 Sobolev setup and Rellich lemma (2.2), printed pp.288–289, for the item and its three new prerequisites. The path named by the existing node is absent locally. Both attempted official book PDF endpoints timed out in the browser. No missing document was downloaded or repository literature list edited.

WANTED: local copy of Demailly, Differential and pseudodifferential operators on manifolds, course on analytic geometry, §§1–2, pp.2–6, for the supplemental source used for all three analytic prerequisites. I read it online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf . Equations (1.5), (2.1), (2.2), (2.2 prime), Lemma 2.3 and the fixed-support reduction in Lemma 2.7 were inspected. This shorter primary source is actually accessible online; the report does not claim the missing book was read.

The proof_origin is agent, with the current blueprint direct-images proof as its local document. The weak graph, support-controlled smoothing, and integer-order weak chart bound are explicit agent refinements. I did not silently attribute these details to an unread page of the book. No Stacks tag supplies these real-analysis assertions, and none was invented. No SGA source is used.

## Searches and source comparisons

Before creating nodes I searched the whole DAG by id, Sobolev, Rellich, mollification, mollifier, weak derivatives, fixed support, Hilbert completion, and by the Demailly source references; the relevant neighboring nodes were opened. Whole-blueprint searches using tools/blueprint_refs.py included Sobolev, Rellich, Hilbert completion, mollifier, weak derivatives, change of coordinates, Hilbert space, Sobolev graph, chart overlap, fixed support, weak Sobolev, mollification and Rellich compactness. The two incidental coordinate hits concern algebraic geometry, not these assertions. No blueprint node states a new lemma. The ancestor command returns None; the item's inherited blueprint.from.node is already null. Each new node preserves this root and the inherited via chain, prepending this item and recording the particular analytic argument. I read the latest unit section and its direct-images proof, paragraph (3), and the DAG chapter and unit records; these are prerequisites on the existing alteration/Kodaira/Hodge chain, not a replacement for the unit's direct-image argument. No chapter or unit was edited.

I inspected Mathlib/Analysis/Distribution/Sobolev.lean, especially its definitions and description of the Fourier/Bessel model, Mathlib/Analysis/Normed/Lp/SmoothApprox.lean (the actual smooth Lp approximation results), and Mathlib/Analysis/Calculus/BumpFunction/Convolution.lean (pointwise and a.e. convolution limits). MeasureTheory.Lp.dense_hasCompactSupport_contDiff and MeasureTheory.MemLp.exist_eLpNorm_sub_le give approximation of the function in Lp; they do not give simultaneous weak-derivative approximation with all supports in one prescribed compact subset of an open set. The other hits are smooth test-function sup-seminorms or smooth Sobolev inequalities. None is the weak graph or chart-map theorem by one-line specialization. Loogle's Rellich query and whole-Mathlib Rellich/Kondrachov/Riesz–Kolmogorov grep had zero hits. The second phrasings also returned density/inequality results, without sequential compactness. All exact queries and actual result summaries are copied from the search log into the nodes, with no fabricated search. The preexisting item searches are retained and the actual Q57 item searches appended.

## Issues and corrections

The original item is mathematically consistent, but had no proof. No STATEMENT-DISPUTED is needed and no hypothesis or conclusion was changed. The source's quadratic-partition convention and Fourier norm are not identified literally with the item's ordinary partition and integer derivative norm: the item's proof uses sum chi_i = 1 directly, and the new lemmas are stated for the derivative norm itself. In particular no unproved equivalence with the Bessel-potential Mathlib model is smuggled into a leaf declaration.

During self-review I strengthened the *support description* of the smoothing prerequisite to say explicitly that the common compact K' contains the original K. This is a true part of the same support-controlled approximation assertion and ensures every error in step 4 is supported in the fixed source compact to which the overlap lemma applies. The item statement remains exactly the live statement. I did not introduce a boundary assumption on overlap domains or assume intersections of coordinate domains have regular boundary.

## Not duplicates

lem-sfb-euclidean-sobolev-graph-mollification vs lem-sfb-bundle-sobolev-rellich: Euclidean closed graphs and support-controlled smoothing are inputs; the item concerns global bundle completions and compactness.
lem-sfb-sobolev-chart-overlap-bound vs lem-sfb-bundle-sobolev-rellich: one fixed localization map on two charts is estimated; the item derives global atlas independence, realization and compactness.
lem-sfb-euclidean-fixed-support-rellich vs lem-sfb-bundle-sobolev-rellich: first-order Euclidean functions with a common compact support, rather than arbitrary-order global bundle Sobolev completions.
lem-sfb-euclidean-sobolev-graph-mollification vs lem-sfb-bundle-sobolev-embedding: closed weak derivative graphs and local smoothing, rather than continuous representatives above the dimension threshold.
lem-sfb-sobolev-chart-overlap-bound vs lem-sfb-bundle-sobolev-embedding: bounded chart transitions at every integer order including zero, rather than a C^r representative theorem.
lem-sfb-euclidean-fixed-support-rellich vs lem-sfb-bundle-sobolev-embedding: sequential L2 compactness at order one, rather than a pointwise representative theorem at high order.
lem-sfb-euclidean-sobolev-graph-mollification vs lem-sfb-elliptic-sobolev-closed-range: no elliptic operator or closed-range assertion; only Euclidean weak graph completeness and approximation.
lem-sfb-sobolev-chart-overlap-bound vs lem-sfb-elliptic-global-garding-estimate: chart localization controls the same derivative order, rather than an elliptic coercive estimate using an operator.
lem-sfb-euclidean-fixed-support-rellich vs lem-sfb-compact-remainder-coercivity: establishes a concrete compact map's local input, rather than using compactness and a priori estimates to derive coercivity.

## Review by Q57

I read the current item statement clause by clause, the three proposed prerequisite statements, the latest blueprint direct-images paragraph (3), and the online Demailly course places listed above. For the book's precise cited pages I have only the inherited reference, so I recorded WANTED and used an agent proof. The course's integer-order description and finite-chart construction support the statement's intended spaces. Its fixed-support Rellich reduction supplies the local analytic input. The completion/weak-realization details here are my argument, and the nodes leave their genuine analytic ingredients open for the next stage-1 workers.

Step 1 uses only the explicit pairings and the Cauchy-sequence definition of completion: Cauchy–Schwarz controls the limit pairing, and positivity is checked from the positive smooth metric and volume density. It does not assume a Sobolev identification. This is the only step marked elementary. It contains the argument rather than citing a definition as if it asserted completeness.

Step 2 uses lem-sfb-euclidean-sobolev-graph-mollification with s=0, whose statement explicitly includes Hilbert completeness of L2 and approximation with a fixed support inside the requested open set. Compactness and positive definiteness bound the volume and metric matrices on each fixed support. The two estimates and the finite reconstruction sum are written out. The Euclidean limits remain supported on the original closed compact: their L2 norm off that set is bounded by the approximation error. Thus putting them back into a frame and extending by zero is justified. A norm limit of the smooth integrated pairing is the integrated pairing of the resulting measurable classes, so the completion identification includes the inner product, not only an abstract vector-space bijection.

Step 3 uses the same node's closed derivative graph, not just density. Its exact statement identifies all derivative limits with the derivatives of the order-zero limit. This is why an Hs Cauchy sequence whose L2 limit vanishes has zero Hs norm. A continuous extension alone would not prove injectivity. The map is defined on Cauchy sequences using the previously proved norm bound, so no uncited extension theorem is needed.

Step 4 uses the Euclidean node's approximation in the full derivative norm, all orders simultaneously, with one enlarged compact K'_i inside each source chart. It then uses precisely the overlap node's statement with that compact source support and target cutoff chi_j. Its hypotheses match: finite rank, the same dimension, a smooth transition diffeomorphism, a smooth frame transition, and a compactly supported cutoff in the target chart. The displayed estimate sums the error from each reconstructed summand; it proves convergence in the actual chosen global norm. No assertion about density from Lp alone is used here.

Step 5 uses the overlap node's norm bound and its explicit distributional compatibility clause. Applying it to every pair of fixed compact chart supports and summing gives an inequality between the two concrete norms. Reversing the two choices is necessary and is included. The Euclidean node supplies convergence against tests and injectivity of L2 into distributions. The partition sum then proves global faithfulness. A fixed atlas identifies the same a.e. class in both realizations, so the assertion about the same subspace of distributional sections is proved as well as norm equivalence.

Step 6 uses lem-sfb-euclidean-fixed-support-rellich. Its hypothesis is first-order weak derivatives, not smoothness; step 3 supplies it for Hs elements and s>=1 supplies the bound. Each support is the image of the same K_i, compactly inside its chart, independent of the sequence index. There are only finitely many charts, so repeated extraction leaves one subsequence convergent in all components. The already proved order-zero inequality and completeness turn these component limits into convergence of the bundle L2 classes. This proves the sequence definition in the item without assuming compactness of a product or a global Rellich theorem.

For the new statements I checked the empty support and rank-zero cases: every function/section is zero as appropriate, and the approximation can be the zero sequence. At s=0 the graph lemma says ordinary L2 and the overlap estimate is just a weighted change-of-variables estimate. For s=1 the Rellich node is the minimal nontrivial compactness input. Compact support is never allowed to meet a chart boundary; the overlap itself need not have a smooth boundary. Omitting a common compact support from the Euclidean compactness assertion would fail for translated bumps; omitting positive derivative order would fail for an orthonormal oscillating sequence on a fixed bounded set. Both required hypotheses are present. The original manifold may be empty or disconnected; finite reconstruction is unchanged, and none of the arguments requires connectedness or nonzero bundle rank.

I checked B–E of delivery-errors.md against the files: new nodes contain statements only, objects and weak derivative conventions are introduced, all non-elementary analytic inputs are cited nodes, no item clause is renamed as a global black box, no dependency cycle is introduced, and every quote in citations.json is a verbatim part of the cited statement. Every proof step is shorter than 2000 characters. In particular the comparison/identification work remains in explicit finite sums, while its genuine weak coordinate-change lemma is a node. The DAG's other Sobolev and elliptic statements are not used as if they supplied these missing prerequisites.

## What remains open

The three new nodes are intentionally unsplit stage-1 work, as required by a one-level split. Their eventual proofs can use: closedness of distributional differentiation and support-controlled convolution for the graph lemma; integer chain and Leibniz rules with bounded smooth coefficients and Jacobian on compact overlaps for the chart estimate; and either Demailly's Fourier-tail argument or uniform mollification followed by compact approximation for Euclidean Rellich. These suggestions are report text, not proofs concealed in the new statements. No requested part of the current item's assembly is left open.
