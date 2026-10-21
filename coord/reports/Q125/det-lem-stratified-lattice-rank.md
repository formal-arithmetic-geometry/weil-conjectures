# Q125 stage-1 repair: det-lem-stratified-lattice-rank

## Files written

- dag/nodes/sec-six-functors-basics/det-lem-stratified-lattice-rank.json: unchanged statement and Lean record; four assembly steps, 2223 characters in total.
- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-coefficient-free-rank.json: statement, unsplit; no Mathlib match for coefficient-sheaf rank comparison.
- dag/nodes/sec-six-functors-basics/lem-sfb-fpqc-labelled-clopen-descent.json: statement, unsplit; no Mathlib match for compatible labelled partitions on an arbitrary fpqc family and their test-morphism comparison.
- citations.json: one verbatim statement quotation for each step/node citation.

There are two new independent tasks, no new Mathlib leaves. Their proof fields and proof dependency lists are empty, and their proof origins null. Source arguments are retained below for the subsequent workers, rather than embedded as proof sketches in their statements.

## Attachments

None. I searched WeilConjectures for the blueprint tag and coefficient/free-rank concepts. The local project theorem AlgebraicGeometry.ProEtale.exists_clopen_rank_decomposition_of_isLisse, lean/Sheaf/Paper/StratifiedLatticeRank.lean:83, has `sorry` as its proof and cannot be attached. Its signature agrees with the mathematical item, including the canonical finite-extension topology, arbitrary X, existential and universal rank tests, the scheme coproduct, and finiteness only under CompactSpace X. No Lean file was written or compiled.

## WANTED

None. The blueprint rank statement, its detailed proof, unit proof, HRS paper, and Stacks sources are present and were read. HRS Example 3.1, page 6, explicitly identifies the pulled-back coefficient ring with continuous functions for any scheme. Stacks descent.tex, label lemma-open-fpqc-covering (Tag 03N0), gives existence and uniqueness of the descended open for an arbitrary covering family. The base-change fact is topologies.tex, lemma-fpqc (Tag 022D), part (3).

## What was wrong and what this repair changes

This is the human's deliberate 2026-10-21 re-split of an already reviewed stage-1 item. The returned seven-step proof contains two substantial, separately implementable arguments. The sandbox initially held only dispatcher marker files, with no item, report or earlier search log. I copied the current read-only repository item, whose seven-step argument is exactly the returned long proof, and retained all fields except the proof assembly, its dependency union, its origin and the split report. In particular the statement, imported metadata, historical review records, source record, old Mathlib searches, Lean statement and declaration were preserved. The delivery tool performs the rebase against current server state; I ran no git command in the read-only repository.

The coefficient lemma is an invariant-rank statement for a single free coefficient sheaf on a nonempty scheme. It contains no descent, rank loci, decomposition or finiteness conclusion. The descent lemma has no sheaves, fields or rank at all: it takes compatible locally constant labels on an fpqc covering and constructs their clopen partition with a comparison for any compatible test morphism. It does not assert the scheme coproduct or quasi-compact finiteness. Neither is a restatement of this item or a transfer of its whole content. The assembly must identify the two coefficient models on overlaps, supply the labels, compare all further trivializations, restrict the covering, and construct the scheme coproduct and finite-rank conclusion.

## Unfinished work

No repair point remains intentionally outstanding. Both new lemmas are delivered statement-only so different workers can prove them. No compilation or stage 2/3 work is authorized here. The server dry run passed preflight, including the DAG and split review checks. The final push outcome is reported by deliver.py.

## Review by Q125

I read the chapter record sec-six-functors-basics and unit sk-lem-stratified-lattice. This repair follows the unit's second proof paragraph, which specifically descends the saturated open-closed rank fibres by fpqc descent of opens. I read the rank detail statement and proof and the current seven-step split against that route. The detailed blueprint's field-stalk shorthand was already replaced by continuous matrices in the returned proof; I retain that argument in the new coefficient task, not a false assumption that an ordinary pro-etale stalk is a field. I also retain the earlier correction of the finiteness argument: quasi-compactness is applied to the descended rank opens, without pretending that an arbitrary cover already has finitely many members.

For lem-sfb-continuous-coefficient-free-rank I read HRS Example 3.1 and the statements of lem-weil-pbc-condensed-field-continuous-realization, def-weil-pbc-lisse-lattice-coefficients, def-weil-vector-space-dimension and the coefficient definitions it uses. The first two actually give continuous E-valued sections; the dimension node actually gives equality of finite basis cardinalities. None assumes Noetherianity for the any-scheme continuous-function realization. The new statement assumes nonemptiness, which is essential: over the empty scheme all finite free coefficient modules are isomorphic even with different ranks. It imposes no additional condition on the item's scheme. Rank zero is allowed; a zero and a nonzero free E-vector space cannot be isomorphic at an evaluated point.

For lem-sfb-fpqc-labelled-clopen-descent I read Stacks 03N0 verbatim, as well as the existing open-descent and fpqc base-change statements. Open descent takes equal inverse images on the scheme fibre products, precisely the hypothesis supplied by the equal label functions. Applying it to each fibre and its complement gives clopen subsets, and joint surjectivity tests the partition and uniqueness. The test-morphism clause is justified by base-changing the same covering to V; no flatness, quasi-compactness or surjectivity is required of h:V -> X. Empty I or empty A forces X empty when the hypotheses permit it, and the only partition is empty there. Infinite labels are allowed; their complement fibres are arbitrary unions of open fibres. I checked this generalization rather than inserting a finite-cover assumption.

Step 1 uses def-sfb-lisse-coefficient-module for exactly the cover with finite free local models (zero allowed), sk-def-pe-site for its fpqc covering condition, sk-prop-sfb-cartesian-coefficients clause (1) for the untwisted pullback identification on overlaps, and the new coefficient lemma for equality of ranks on every nonempty overlap. Both projections are maps of schemes, and the coefficient comparison has no invertibility-of-ell hypothesis on its untwisted clause. The two free models are isomorphic by restricting the same L, so the coefficient lemma's hypotheses hold. No dimension or matrix fact is now hidden in this step: it is the separate first task.

Step 2 uses the new labelled descent statement for the actual clopen partition and its actual test-morphism clause; these conclusions occur verbatim in its statement. It takes A=N and constant functions n_i, which are compatible by step 1. For every further free trivialization V of rank s, the same coefficient comparison and the new rank lemma show compatibility on each U_i x_X V with the constant function s. The descent lemma then says exactly that V has whole or empty inverse image of the rank-r piece according as s=r or s differs from r. It applies to every constant-rank neighborhood and proves the some/every, all-preimages and independence assertions, not merely existence for one cover. This is the full old independence argument, exposed in the generic test-morphism task rather than dropped.

Step 3 reads the statements of lem-galois-fpqc-covering-base-change, sk-lem-pe-weakly-etale-stability, sk-def-pe-site, sk-prop-sfb-cartesian-coefficients and lem-weil-pbc-scheme-coproduct-family. They give, respectively, the restricted fpqc covering, weakly etale stability, the pro-etale covering criterion, the coefficient pullback identification, and existence with disjoint open coprojections of the scheme coproduct. Each is used for exactly that assertion. No quasi-separatedness of X or affineness of intersections is used. On nonempty restricted members the label is r by step 2; empty members have the unique zero sheaf, which is free of any finite rank. The local inverse to the coproduct map is its inverse identity on each rank open, agreeing on empty intersections, so ordinary open gluing proves the scheme isomorphism. This is a short assembly of the cited coproduct construction, not a new hidden comparison theorem.

Step 4 uses def-weil-pbc-quasi-compact-scheme's actual finite-subcover characterization. A nonempty piece not in a finite subcover would meet a covering piece, contradicting disjointness. This is elementary and remains in the item. The empty scheme, zero module, two disjoint points with ranks 1 and 2, and an infinite disjoint union of points with unbounded ranks all behave correctly. The last example explains why global finite image needs the exact quasi-compactness hypothesis.

I checked delivery-errors B1-B10: both new statements introduce their objects, cite the relevant notions, use TeX, specify the sources and blueprint places, contain no proof sketch, and were searched through the required recorded command. The searches.jsonl results were read before populating mathlib_searches. The rank searches returned ordinary invariant-basis-number and finrank results and free-sheaf pullback constructions; I read Free.lean (freeHomEquiv), Dimension/Free.lean and InvariantBasisNumber.lean. None is a one-line specialization to this sheaf claim: the sectionwise matrix and its evaluation remain work. The labelled searches returned scheme morphism-property descent and topology quotient-map clopen preimages; I read FlatDescent.lean:133-140 and Topology/Clopen.lean:136-138. Neither has the scheme-family descent hypotheses and conclusions. A Loogle query using the obsolete identifier QuotientMap returned an unknown identifier; I recorded that result and reran with Topology.IsQuotientMap, obtaining the topology lemma. No service failure was recorded as a negative match.

For C1-C8 I read every citation's statement, generated the quote certificate from those actual statement fields, and checked that proof_deps is exactly the union of uses. Both new nodes inherit this unit and descend from this blueprint item with via=[]; neither depends on the item. The direct proof tools off the unit are the same generic untwisted coefficient identification, weakly-etale stability and scheme coproduct already accepted on this item, declared with purposes in split_report.tool_uses. The old global tool_uses field was left untouched. The future first task can use the existing continuous-realization and dimension nodes, and the future second task can use existing 03N0 and 022D nodes; no duplicate of either theorem was introduced. For D1-D5 I checked the two tasks divide the old work rather than relabel the full statement, and that all remaining assembly arguments are written. For E1-E7 I checked the field, nonempty, arbitrary-cover and base-change hypotheses as above. There is no statement dispute or route departure.

## Allocation of all seven original arguments

1. Old step 1 stays in assembly step 1: choose the possibly infinite trivializing pro-etale cover, and use its fpqc condition.
2. Old step 2 is the new coefficient task, with the coefficient pullback to the overlap left explicitly in assembly step 1. The matrix, inverse identities, evaluation and basis comparison are retained below as the exact old text.
3. Old step 3 is the labelled-clopen task, applied in assembly step 2. Descend both fibres and complements using 03N0; test complements by joint surjectivity.
4. Old step 4 is the partition assertion of the labelled-clopen task, applied in assembly step 2. Lift every point to a covering member to check exactly one label; allow rank zero and empty X.
5. Old step 5 is the test-morphism comparison of the labelled-clopen task and its application to additional trivializations in assembly step 2. In a proof of the new task, base-change the cover to the test V and test each point there. Equivalently, for the original constant labels, adjoin V to the original family and use descent uniqueness, exactly as in the retained old text.
6. Old step 6 stays explicitly in assembly step 3: base-change the cover, weakly-etale stability, coefficient pullback, constant-rank restriction, and the scheme coproduct isomorphism checked on its disjoint opens.
7. Old step 7 stays explicitly in assembly step 4: finite subcover of disjoint open rank pieces.

For the more general locally constant functions in the second task, apply the old fibre-and-complement descent to W_{i,a}=rho_i^{-1}(a). Each complement is the union of the other open fibres. Equalities on overlaps are given. Descended complements and point lifts prove a partition and uniqueness. For its test clause, base-change the covering to V; compatibility says the inverse images of h^{-1}(Z_a) and sigma^{-1}(a) coincide on that cover. Its joint surjectivity makes them equal on V. Thus the universal comparison is a stated task with its own hypotheses; no part of the old rank-independence argument disappears.

## Original argument retained verbatim

The following is the seven-step returned proof, retained so the extracted tasks preserve every argument and are reviewable against the original text. It is not a proof field of either new node.

### Original step 1

Choose a pro-etale trivializing covering $\{f_i:U_i\to X\}_{i\in I}$ and isomorphisms $L|_{U_i}\simeq E_{U_i}^{\oplus n_i}$ with $n_i\in\mathbf N$. The index set may be infinite. This is precisely the locally free hypothesis, refining to individual finite-rank trivializations if necessary. By [sk-def-pe-site] this is an fpqc covering, in particular jointly surjective. No quasi-compactness of $X$ or of the $U_i$ is assumed here.

Uses: sk-def-pe-site.

### Original step 2

On $W=U_i\times_XU_j$, the two trivializations induce an isomorphism $E_W^{\oplus n_i}\simeq E_W^{\oplus n_j}$: [sk-prop-sfb-cartesian-coefficients](1) identifies each pulled-back coefficient ring with $E_W$. By [lem-weil-pbc-condensed-field-continuous-realization] and [def-weil-pbc-lisse-lattice-coefficients], $\Gamma(W,E_W)=C(|W|,E)$. The isomorphism and its inverse are rectangular matrices $A,B$ over this ring: their columns are the coordinates of the images of the global standard basis sections, and their inverse identities give $AB=1$ and $BA=1$. If $w\in|W|$, evaluating entries at $w$ preserves sums and products and gives inverse $E$-linear maps $E^{n_i}\rightleftarrows E^{n_j}$. The image of the standard basis of $E^{n_i}$ is consequently a basis of $E^{n_j}$ with $n_i$ elements; comparison with its standard $n_j$-element basis using [def-weil-vector-space-dimension] gives $n_i=n_j$. Thus whenever $n_i\ne n_j$ the overlap $W$ is empty. This also treats rank zero, and uses no assertion that an ordinary stalk of the pro-etale coefficient sheaf is a field.

Uses: sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-condensed-field-continuous-realization, def-weil-pbc-lisse-lattice-coefficients, def-weil-vector-space-dimension.

### Original step 3

For each $r\in\mathbf N$ put $W_{i,r}=U_i$ if $n_i=r$, and $W_{i,r}=\varnothing$ otherwise. These subsets and their complements are open. Their pullbacks to every $U_i\times_XU_j$ agree: if the two local ranks differ the overlap is empty by step 2, and otherwise the two pullbacks are both the whole overlap or both empty. Apply [lem-weil-pbc-etale-open-fpqc-descent] with base $S=X$, etale map $V\to S$ the identity of $X$, and covering $\{U_i\to X\}$. It gives a unique open $O_r\subseteq|X|$ with $f_i^{-1}(O_r)=W_{i,r}$. Apply the same statement to the compatible complements $U_i\setminus W_{i,r}$ to obtain an open $P_r$. Joint surjectivity shows $P_r=|X|\setminus O_r$, so $O_r$ is also closed.

Uses: lem-weil-pbc-etale-open-fpqc-descent.

### Original step 4

The $O_r$ are pairwise disjoint and cover $|X|$. Indeed, for $x\in|X|$, choose $u\in U_i$ above $x$ using joint surjectivity of the covering. The equality $f_i^{-1}(O_r)=W_{i,r}$ says exactly that $x\in O_r$ if and only if $n_i=r$. Thus each point belongs to exactly one $O_r$, including points where $L$ is zero (the piece $O_0$). If $X$ is empty all pieces are empty.

Uses: sk-def-pe-site.

### Original step 5

The construction is independent of all choices. Given an additional trivializing object $V\to X$ with $L|_V\simeq E_V^{\oplus s}$, adjoin it to the chosen covering; this is still a pro-etale covering, since it retains the finite affine covering refinements of the original one. Repeat steps 2 and 3 for the enlarged family. The descended open of rank $r$ must be $O_r$, by uniqueness in [lem-weil-pbc-etale-open-fpqc-descent] for the original covering. Hence its preimage in $V$ is all of $V$ when $s=r$, and empty otherwise. Apply this to every constant-rank neighborhood in any trivializing covering. At every preimage of $x$ the local rank is therefore the unique $r$ with $x\in O_r$. This proves the asserted equivalence of some and every and identifies the subsets in the statement as $X_r=O_r$.

Uses: sk-def-pe-site, lem-weil-pbc-etale-open-fpqc-descent.

### Original step 6

Give each $X_r$ its open subscheme structure. By [lem-galois-fpqc-covering-base-change], the maps $U_i\times_XX_r\to X_r$ form an fpqc covering; they are weakly etale by [sk-lem-pe-weakly-etale-stability], hence form a covering of its small pro-etale site by [sk-def-pe-site]. Its nonempty members have $n_i=r$, and pulling back their trivializations using [sk-prop-sfb-cartesian-coefficients](1) gives $L|_{U_i\times_XX_r}\simeq E_{U_i\times_XX_r}^{\oplus r}$. Thus $L|_{X_r}$ is lisse of constant rank $r$. The disjoint clopen partition of step 4 gives $X=\coprod_rX_r$: the coproduct exists by [lem-weil-pbc-scheme-coproduct-family], and its canonical map to $X$ is an isomorphism, since on each open $X_r$ it is the identity and these opens cover both schemes.

Uses: lem-galois-fpqc-covering-base-change, sk-lem-pe-weakly-etale-stability, sk-def-pe-site, sk-prop-sfb-cartesian-coefficients, lem-weil-pbc-scheme-coproduct-family.

### Original step 7

If $X$ is quasi-compact, the open covering $\{X_r\}_{r\geq0}$ has a finite subcover by [def-weil-pbc-quasi-compact-scheme]. Since these opens are disjoint, any $X_s$ not in that finite subcover must be empty: a point of it would also lie in a member of the subcover. Therefore only finitely many ranks occur. This argument needs no globally finite original trivializing covering.

Uses: def-weil-pbc-quasi-compact-scheme.

## Not duplicates

lem-sfb-fpqc-labelled-clopen-descent vs lem-galois-fpqc-covering-base-change: the existing statement concerns An fpqc covering remains an fpqc covering after base change, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-pc-descent-finite-flat-closed-subschemes: the existing statement concerns Effective descent of finite flat closed subschemes, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-pc-fpqc-descent: the existing statement concerns FPQC descent for quasi-coherent modules, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-pd-descended-overlap-glue-data: the existing statement concerns Descended overlap transitions and cartesian intersection lifts, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-fpqc-covering-axioms: the existing statement concerns Fpqc coverings satisfy the site covering axioms, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-etale-open-fpqc-descent: the existing node descends a single compatible open; this task assembles all label fibres and complements into a partition and proves comparison with every compatible test morphism. It reuses the existing node rather than restating its one-open assertion.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-etale-sections-fpqc-descent: the existing statement concerns Fpqc descent of sections of a small etale sheaf, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-finite-affine-coproduct-spectrum: the existing statement concerns Finite coproducts of affine schemes are spectra of product rings, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-flat-qc-surjective-quotient-map: the existing statement concerns Flat quasi-compact surjective morphisms are quotient maps, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-fpqc-affine-standard-refinement: the existing statement concerns Affine fpqc coverings admit finite standard refinements, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-fpqc-detects-openness: the existing statement concerns Fpqc coverings detect openness of subsets, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-open-subscheme-fpqc-descent: the existing node descends a single compatible open; this task assembles all label fibres and complements into a partition and proves comparison with every compatible test morphism. It reuses the existing node rather than restating its one-open assertion.

lem-sfb-fpqc-labelled-clopen-descent vs lem-weil-pbc-standard-fpqc-quotient-topology: the existing statement concerns Standard affine fpqc covers are quotient maps, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-a1-ind-quasi-affine-fpqc-effective-descent: the existing statement concerns Effective fpqc descent for morphisms with quasi-affine quasi-compact opens, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs det-lem-stratified-lattice-rank: the existing item is about lisse E-module rank loci, whereas this task has arbitrary set-valued labels and a test-morphism comparison, with no sheaves, scheme coproduct or quasi-compact finiteness.

lem-sfb-fpqc-labelled-clopen-descent vs lem-sf-proetale-locally-constant-origin: the existing statement concerns Locally constant pro-etale sheaves with finite values are of etale origin, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-trf-etale-relation-finding-opens: the existing statement concerns Restriction of a quotient by an fppf relation is an open subspace, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-fpqc-labelled-clopen-descent vs lem-trf-space-open-immersion-etale-local: the existing statement concerns Open immersions of spaces descend along etale target covers, not the unique partition from arbitrary compatible set-valued labels with its test-morphism clause. Shared descent tools/tags do not give equal statements.

lem-sfb-continuous-coefficient-free-rank vs lem-weil-pbc-condensed-field-continuous-realization: the existing node identifies the coefficient ring sheaf with continuous functions; it does not compare finite free sheaves of different ranks.

lem-sfb-continuous-coefficient-free-rank vs lem-weil-pbc-continuous-field-matrix-sheaf-normal-form: the existing node splits a map from a supplied block factorization; it does not prove invariant rank from an arbitrary free-sheaf isomorphism.

lem-sfb-continuous-coefficient-free-rank vs lem-weil-pbc-continuous-field-presentation-normal-form: the existing node is a presentation normal-form result, not the any-scheme nonempty free-sheaf rank comparison.

lem-sfb-continuous-coefficient-free-rank vs det-lem-stratified-lattice-rank: the item proves the full global rank-locus decomposition for a lisse module, while this task concerns only one isomorphism of finite free coefficient sheaves over a nonempty scheme.

lem-sfb-fpqc-labelled-clopen-descent vs lem-galois-coproduct-copies-morphisms-clopen: that node identifies morphisms into an existing scheme coproduct with an existing clopen partition; it neither descends an fpqc-compatible family of labels nor constructs its partition.

lem-sfb-fpqc-labelled-clopen-descent vs lem-pur-etale-local-shift-partition: that node detects finitely many shifts of a bounded finite-coefficient complex on an etale cover; this task has arbitrary labels and fpqc covers and no derived, boundedness or finiteness hypothesis.
