# Worker report: Q53

## Files written

- `dag/nodes/sec-six-functors/lem-sf-complete-residue-cohomology-bounds.json`: the assigned stage-1 re-split, statement unchanged; four assembly steps, 1886 characters in total.
- `dag/nodes/sec-six-functors/lem-sf-strict-dvr-reduction-triangles.json`: new statement, status unsplit, no Mathlib match. Isolates the simultaneous strict quotient construction, coefficient exactness with completed-coefficient linearity, and residue triangles (old steps 2-4).
- `dag/nodes/sec-six-functors/lem-sf-bounded-epimorphic-top-derived-limit.json`: new statement, status unsplit, no Mathlib match. Isolates the general strict-tower Milnor comparison and the endpoint obstruction calculation (old steps 6-7).
- `citations.json`: verbatim statements for every node cited in the item's four steps.
- `searches.jsonl`: actual msearch.py log, retained without editing; each new node records its own queries and actual result records.

Only the three node files and this report are delivery files. Both new nodes have empty proof and proof_deps, null proof_origin and mathlib_match. They are independently claimable tasks, not already split nodes. The discussion below is the handoff of their arguments, as required by the brief, not proof text hidden inside their statements.

## Attachments

None. Searching WeilConjectures for the blueprint id and by residue/amplitude/cohomology notions finds no project declaration proving the item. The landed `WeilConjectures.complete_residue_cohomology_bounds` in `lean/Sheaf/Paper/CompleteResidueCohomologyBounds.lean:93` has `sorry` (line 120), and is not an attachment. I read its statement and full proof docstring; it agrees with the unchanged natural-language target. No Lean was written and no compiler, Lake or build command was run.

## WANTED

None: the needed Stacks .tex sources are present.

## What was wrong and what changed

This is the human's deliberate 2026-10-21 re-split, not a finding that the reviewed result was mathematically false or that its existing status was stale. The previous seven-step proof allocated the simultaneous quotient construction and the arbitrary-derived-limit Milnor comparison to one worker. I divided those two independent arguments into separate statement-only nodes. The item still carries the tensor-unit test and the full base/step induction and top-surjectivity calculation. Its statement, coefficient category, hypotheses and conclusion are byte-for-byte unchanged. No constructibility, local constancy, characteristic, invertibility, Noetherian or finite-dimensionality condition on X was introduced. The two new nodes also do not require quasi-compactness, which the item already has.

The key distinction is that the quotient node has no completeness hypothesis and no vanishing conclusion, and the limit node has no DVR, adic reduction or residue hypothesis. Neither is a clause of the item or a restatement of the whole argument. Their proofs require separate construction/comparison arguments of comparable size; neither is the elementary induction that remains in assembly step 3.

## Source and argument allocation

I read proetale.tex Tag 09C2 (`lemma-describe-constructible-complexes`), in particular the proof of (1),(2), and sites-cohomology.tex Tag 0942 (`lemma-bounded`), including its ideal-quotient triangle and finite-filtration proof. These locate exactly where residue bounds propagate and where derived completeness is used. The present proof stays over B_X throughout, so it does not need an implicit equivalence with a different coefficient category.

For `lem-sf-strict-dvr-reduction-triangles`, the main source is the displayed triangle of 0942(1), specialized to a DVR; I also read sites-cohomology.tex Tag 06YS (`lemma-K-flat-resolution`) and Tag 06YY (`lemma-derived-base-change`), and the statements of the existing resolution/change-of-rings/short-exact-triangle nodes. A future worker can start as follows, with no use of the item or its conclusion:

1. Choose an arbitrary representative G of K and use `lem-pc-kflat-resolution` to obtain one K-flat resolution P -> G with flat B-terms. `lem-pur-derived-change-of-rings` computes all reductions by P tensor C_n. The strict maps are literally 1_P tensor q_n, so they represent the quotient maps for the same resolution; no unrelated isomorphisms of individual reductions are used.
2. On coefficient modules, define u_n(r mod varpi) = varpi^n r mod varpi^(n+1). If the lift changes by varpi s, its image changes by varpi^(n+1)s. Cancellation of varpi^n in the DVR proves injectivity. Its image is the kernel of R/varpi^(n+1) -> R/varpi^n, which is surjective. Pass to constant sheaves by taking local representatives and local lifts. These are local kernel/image calculations, not an assumption that constant-sheaf sections on every object are constant.
3. Check B-linearity, the part not supplied by an ordinary module exact sequence: for a section z of B, its compatible components satisfy z_(n+1) mod varpi = z_1; hence z_(n+1) varpi^n r = varpi^n z_1 r mod varpi^(n+1), locally on representatives. Thus the kernel map and quotient maps form a short exact sequence of B-module sheaves.
4. Every P^j is flat, exactly as defined by `def-pc-flat-sheaf-modules`, so tensoring this sequence is exact in each degree. `lem-weil-pbc-complex-ses-triangle` gives the required triangle with its middle-to-last map the localized strict transition. The statement of that existing lemma specifies this arrow, not merely an abstract triangle on three isomorphic objects.

For `lem-sf-bounded-epimorphic-top-derived-limit`, I read sites-cohomology.tex Tag 0947 (`proposition-enough-weakly-contractibles`), (5)-(7) and their proof, and derived.tex Tag 08TC (`definition-derived-limit`) and the uniqueness discussion immediately following it. I read the complete statements of `det-pe-products-derived`, `det-pe-milnor-sequence`, `det-pe-milnor-epimorphic`, `lem-weil-derived-limit-existence`, and the derived/triangulated category definitions. They give the following independent task:

1. For the strict tower P_n, form its termwise product V, its chain map T with pr_n T = t_n pr_(n+1), and C = Cone(1-T)[-1]. `det-pe-products-derived` says that Q(V), with the images of the termwise projections, is the product of Q(P_n) in D(Mod(R)). Localization preserves differences and composites, so pr_n Q(1-T) = pr_n - Q(t_n) pr_(n+1). This identifies the exact transition endomorphism in the derived-limit definition.
2. Use the cone triangle and inverse rotation: if delta is its third map, then C -> V -> V -> C[1], with first map -delta[-1], is distinguished. Its rotation is the original cone triangle. This is precisely the Roos triangle, using TR2 of `def-weil-triangulated-category`, not a silent identification of a termwise product with a derived product. Therefore Q(C) and the supplied L are derived limits of the same fixed localized tower. Clause 1 of `lem-weil-derived-limit-existence` makes them isomorphic. No canonical or functorial choice of this isomorphism is asserted or needed.
3. `det-pe-milnor-sequence` applies to C and gives 0 -> R^1 lim H^(j-1)(P_n) -> H^j(C) -> lim H^j(P_n) -> 0. At j<a and j>b+1 both outer towers are zero, so their product kernels and cokernels are zero. At j=b+1 the right tower is zero, and the left term is R^1 lim H^b(P_n); it vanishes by `det-pe-milnor-epimorphic` for the sheaf of rings R and the assumed epimorphic H^b transitions. Exactness gives the bound for C, and the above isomorphism gives it for L. This is where the possible extra degree is removed.

The original proof paragraphs are reproduced verbatim below, so no old argument has been dropped or blurred. Old steps 2-4 belong to the first new task, old steps 6-7 to the second; old step 1 is assembly step 1, and old step 5 is assembly step 3 with its long-exact-sequence input explicit. The item no longer carries either construction argument inline.

## Mathlib and duplicate searches

I used only the prescribed msearch.py command for Mathlib searches, with two semantic phrasings per new node, Loogle patterns and source grep. Both LeanSearch calls returned a rate-limit error; their verdicts are unavailable. LeanFinder and Loogle ran successfully, as did grep. The node records include the exact query strings and actual log records, not searches inferred from names.

For the quotient node, LeanFinder returned ordinary AdicCompletion flatness/exactness, formal smoothness and ordinary flat-module criteria, not a simultaneous strict sheaf quotient model with its residue exact sequences. Loogle returned truncation short exactness and a small-localized-Hom instance. I read Mathlib/Algebra/Homology/DerivedCategory/ShortExact.lean: the triangleOfSES construction and triangleOfSES_distinguished (line 92) handle a given short exact sequence and do not construct the coefficient sequence or the single K-flat tower. That generic theorem already has `lem-weil-pbc-complex-ses-triangle` in the DAG; it is not grounds for declaring the new construction a Mathlib leaf.

For the limit node, LeanFinder returned ordinary coherent-topology/condensed sequential epimorphism lemmas, K-projective/factorization facts, and generic IsLE/IsGE bounds. I read the coherent-topology SequentialLimit source around its actual local-surjectivity statement: it concerns an ordinary limit projection and does not provide the arbitrary-derived-limit cohomology interval. Loogle gave no DerivedCategory/limit match, and the IsLE/limit query gave IsLeftAdjoint substring matches about colimits. The global Milnor/Roos/homotopyLimit/derivedLimit grep found only the unrelated Milnor exotic-sphere docstring. Neither full new statement is a one-line specialization of those hits.

Before creating nodes I searched the full DAG by tags 0942, 0947, 08TC, 09C2 and relevant terms; inspected statement-level candidates (not just proof-text matches); and used blueprint_refs.py search with quotient tower, Milnor, residue cohomology, quotient cohomology, uniformly bounded, top cohomology, Milnor cone, DVR, reduction triangle, epimorphic top, and flat resolution. The nearest blueprint ancestor is lem-fix-weil-operations; the new via lists prepend this item to its existing ancestry. The blueprint provides no same-statement match. I also searched the live WeilConjectures source for residue, K-flat quotient transitions and Milnor bound notions; its generic TowerLimitMilnor and DerivedLimitEpimorphicTower statements do not contain either new full construction/bound. In particular, degreewise epimorphic transitions in the latter file are stronger than epimorphic top cohomology and are not silently substituted.

## Not duplicates

lem-sf-strict-dvr-reduction-triangles vs lem-sf-complete-residue-cohomology-bounds: the new node constructs strict quotient residue triangles for arbitrary K; it has neither completeness nor any cohomological vanishing conclusion.
lem-sf-strict-dvr-reduction-triangles vs lem-pe-kflat-scalar-tower-realization: the existing node identifies strict transitions with normalized tensor-restriction-adjunction transitions for general scalar towers; it does not supply the DVR residue kernel short exact sequence or its distinguished triangles.
lem-sf-strict-dvr-reduction-triangles vs lem-coef-normalized-dvr-kflat-reduction-model: the existing node provides simultaneous reduction isomorphisms and adjoint-transition normalization, but no residue short exact sequences or triangles. Its normalized/global coefficient datum is also unnecessary here.
lem-sf-strict-dvr-reduction-triangles vs lem-coef-normalized-dvr-kflat-transition: the existing node identifies an adjoint transition with a chain quotient map; the new task also constructs and proves the short exact sequences with residue kernel.
lem-sf-strict-dvr-reduction-triangles vs def-weil-integral-reduction-tower: the existing definition specifies the strict quotient tower but does not prove the residue kernel sequence or triangles. It also packages the global ell != p coefficient conventions that this item does not assume.
lem-sf-strict-dvr-reduction-triangles vs lem-weil-pbc-complex-ses-triangle: the existing generic result assumes a degreewise short exact sequence; the new node constructs that sequence for the simultaneous DVR reductions.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-sf-complete-residue-cohomology-bounds: the new node is a statement about arbitrary strict towers over arbitrary ring sheaves, with uniform levelwise bounds and epimorphic top cohomology as inputs; it does not assume or deduce anything about a residue reduction.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-sf-proetale-vanishing-detection: the latter detects acyclicity by weakly contractible evaluation for finite coefficients; it gives no derived-limit interval or endpoint calculation for arbitrary ring sheaves.
lem-sf-bounded-epimorphic-top-derived-limit vs det-pe-milnor-sequence: the latter computes cohomology of the particular termwise-product cone, with a possible R^1 lim term, and does not identify an arbitrary supplied derived limit with that cone or remove the endpoint term under the new hypotheses.
lem-sf-bounded-epimorphic-top-derived-limit vs det-pe-milnor-epimorphic: the latter concerns a tower of module sheaves, or degreewise epimorphic complexes; here only H^b(t_n) is epimorphic, and the conclusion is a cohomological interval for any derived limit.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-pe-roos-cone-calculus: the latter supplies a model, functorial cone/shift comparisons and the Roos property, but does not state this cohomological interval or top-degree obstruction removal. It can serve as a tool when the new node is later split.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-sf-strict-roos-derived-limit-comparison: the latter supplies an evaluation-compatible zigzag to a K-injective tower limit, but not the interval statement for an arbitrary supplied derived limit.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-pc-derived-limit-milnor-sequence: that result concerns D(Ab), not general module sheaves on X_proet, and leaves the R^1 lim obstruction present.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-weil-derived-limit-existence: existence, uniqueness and termwise products do not themselves supply the Milnor calculation and endpoint vanishing.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-sfb-left-complete-heart-upper-bound: that node bounds an exact product-preserving functor from its values on a class of heart objects, assuming left completeness. It is not a bound on the derived limit of an arbitrary strict tower with epimorphic top cohomology.
lem-sf-strict-dvr-reduction-triangles vs lem-coef-integral-residue-tor: the latter concludes finite-level Tor amplitude for a bounded constructible integral complex and has no strict residue triangles; the new construction requires no constructibility or boundedness.
lem-sf-bounded-epimorphic-top-derived-limit vs lem-sfb-integral-cohomological-adic-criterion: the latter is a constructible-completeness criterion, not a general strict-tower limit bound, and requires different geometric/coefficient data.

## Review by Q53

I checked the item and both new statements against the source passages named above and read every cited statement. In assembly step 1, def-weil-proetale-tor-amplitude tests every k_X-module, hence permits k_X itself; def-weil-derived-tensor gives its K-flat model, on which P tensor k_X = P is the tensor-unit identity. There is no need for constructibility or residue cohomology to be locally constant. The V=X test is allowed by the item's local hypothesis.

In step 2, the new strict-triangle statement explicitly gives the one model, the termwise short exact sequences, and the equality of the displayed arrow with the canonical quotient transition. It introduces its own l,E,X,B,K and needs only the coefficient and site hypotheses already in force. I checked that flatness is over the completed sheaf B, while each quotient is a constant sheaf read as a B-module by the relevant projection. I did not identify B with the constant sheaf R_X or assume multiplication on B has already been proved to be injective. The explicit cancellation is in the DVR coefficient rings, and its sheaf B-linearity is included in the new argument.

In step 3, lem-sf-derived-homology-long-exact states precisely the exact segment used for each distinguished triangle. The induction states both the base and its step; the bound in degree j uses the two outer zero groups H^j(K_1), H^j(K_n). For the separate top-degree surjectivity assertion, the zero next group is H^(b+1)(K_1), not H^b(K_1). The step keeps this elementary work in the item rather than introducing an induction-only node. This existing generic lemma is the sole new split_report tool-use request outside the unit; it was already approved on the original item and no unit route changes.

In step 4, the second new statement requires a *strict* tower, an interval on all its levels, and epimorphic top transitions. Steps 2-3 supply exactly these. Its L is any Roos-derived-limit object, so the item's completeness hypothesis applies with L=K. The simultaneous-transition clause prevents a mismatch between a tower with conveniently chosen maps and the actual canonical quotient tower. I checked the original step 6 comparison in detail: termwise products becoming derived products is a theorem (det-pe-products-derived), inverse rotation has the -delta[-1] sign, and uniqueness of the derived-limit object uses clause 1 of lem-weil-derived-limit-existence. These non-elementary facts have moved to the general limit task, with every old formula retained below. In the new limit task, the top-transition hypothesis is a sheaf epimorphism, exactly what det-pe-milnor-epimorphic states for any ring sheaf, not merely a surjectivity assertion on arbitrary-object sections.

I tested small cases: X empty and K=0 give zero sequences and limits. For K=B in degree zero and a=b=0, the strict coefficient sequence is the ordinary u_n quotient sequence, H^0 transitions are epimorphic, and the limit is concentrated in degree zero. Shifting this test checks arbitrary integral endpoints and a=b. For a general tower, a constant complex and identity transitions satisfy the limit node with the original interval, while the hypothetical extra b+1 term is precisely R^1 lim H^b, showing why the epimorphism hypothesis is retained. No assertion about degreewise surjectivity of the tower was inserted. Omitting completeness in the original item would permit a nonzero varpi-inverted module with zero residue, so completeness remains essential in assembly step 4.

I reviewed delivery-errors B-E point by point: complete independent statements and definition references; actual tagged .tex sources; all required real Mathlib searches with the rate-limited service marked unavailable; no Mathlib leaf claimed without a match; full blueprint ancestry; no item-clause relabelling; no one-node relocation; no new elementary induction lemma; no dependency on this item's conclusion inside either new statement; no hidden constructibility or coefficient-category switch. The longest new assembly step is 494 characters, so there is no non-elementary step over 2000 characters. All original proof details are allocated below; the delivered unsplit nodes contain no proof sketch. Nothing needed statement repair.

## Unfinished work

None in the assigned stage-1 scope. The two new tasks are intentionally unsplit, so future workers can prove/split them independently. No stage-2 or stage-3 work was attempted.

## Original proof retained verbatim, with allocation

### Original step 1 -> assembly step 1

Write $C_n=(R/\varpi^n)_X$ with its $B_X$-module structure given by the $n$-th projection, and $K_n=K\otimes^L_{B_X}C_n$, viewed over $B_X$ by restriction of scalars. In the Tor-amplitude hypothesis take $V=X$ and $N=k_X$. The unit identity $K_1\otimes^L_{k_X}k_X\cong K_1$ follows on a K-flat representative from $P\otimes_{k_X}k_X=P$. Hence $H^j(K_1)=0$ outside $[a,b]$. This is just the defining test of [def-weil-proetale-tor-amplitude], with derived tensor as in [def-weil-derived-tensor].

Cited nodes: def-weil-proetale-tor-amplitude, def-weil-derived-tensor.

### Original step 2 -> lem-sf-strict-dvr-reduction-triangles

Choose a representative of $K$ and a single K-flat resolution $P^\bullet$ with flat $B_X$-module terms by [lem-pc-kflat-resolution]. For every $n\geq1$, [lem-pur-derived-change-of-rings] identifies $P_n^\bullet=P^\bullet\otimes_{B_X}C_n$ with $K_n$. Use the actual chain maps $1_P\otimes(C_{n+1}\to C_n)$ as its strict transition maps. These are the canonical quotient transitions in the completeness hypothesis, because the same resolution computes every reduction and every quotient map.

Cited nodes: lem-pc-kflat-resolution, lem-pur-derived-change-of-rings.

### Original step 3 -> lem-sf-strict-dvr-reduction-triangles

For every $n\geq1$ the coefficient sequence $0\to k_X\xrightarrow{u_n}C_{n+1}\to C_n\to0$, where $u_n(\bar r)=\varpi^n r\bmod\varpi^{n+1}$, is short exact as a sequence of $B_X$-modules. Indeed, $R$ is a DVR with nonzero uniformizer by [def-weil-l-adic-coefficient-extension]: cancellation of $\varpi^n$ shows that $u_n$ is well defined and injective, and its image is exactly the kernel of the quotient map, which is surjective. By the constant-sheaf construction [def-weil-pbc-constant-sheaf], sections locally come from elements of the coefficient modules and equality can be checked after a covering refinement; therefore the same kernel calculation and local lifts prove exactness of the sheaf sequence. The maps are $B_X$-linear: for a local section $z$ of $B_X$, its components satisfy $z_{n+1}\bmod\varpi=z_1$, so $z_{n+1}\varpi^n r=\varpi^n z_1r$ modulo $\varpi^{n+1}$, checked locally where the finite coefficient sections are constant.

Cited nodes: def-weil-l-adic-coefficient-extension, def-weil-pbc-constant-sheaf.

### Original step 4 -> lem-sf-strict-dvr-reduction-triangles

Each $P^j$ is flat, so tensoring the short exact coefficient sequence of Step 3 with $P^j$ preserves exactness, precisely the definition in [def-pc-flat-sheaf-modules]. Thus $0\to P_1^\bullet\to P_{n+1}^\bullet\to P_n^\bullet\to0$ is a degreewise short exact sequence of complexes. Apply [lem-weil-pbc-complex-ses-triangle] in the abelian category of $B_X$-module sheaves to get the distinguished triangle $K_1\to K_{n+1}\to K_n\to K_1[1]$. Its second arrow is the canonical transition from Step 2, not an independently chosen isomorphism between reductions. By [lem-sf-derived-homology-long-exact], for every $j$ its cohomology sequence contains $H^j(K_1)\to H^j(K_{n+1})\to H^j(K_n)\to H^{j+1}(K_1)$.

Cited nodes: def-pc-flat-sheaf-modules, lem-weil-pbc-complex-ses-triangle, lem-sf-derived-homology-long-exact.

### Original step 5 -> assembly step 3

Induct on $n\geq1$ to prove $H^j(K_n)=0$ for all $j\notin[a,b]$. The base $n=1$ is Step 1. For the induction step, the exact segment in Step 4 has $H^j(K_1)=H^j(K_n)=0$ for such $j$, forcing $H^j(K_{n+1})=0$. At $j=b$, its next term is $H^{b+1}(K_1)=0$, so the same segment proves that every canonical transition $H^b(K_{n+1})\to H^b(K_n)$ is an epimorphism. This proves both assertions for the entire fixed tower.

Cited nodes: .

### Original step 6 -> lem-sf-bounded-epimorphic-top-derived-limit

Apply [det-pe-milnor-sequence] to the strict tower $P_n^\bullet$ of $B_X$-module complexes on the small pro-etale site, with $T$ built from the termwise product complex $\prod_nP_n^\bullet$. It gives $0\to R^1\varprojlim_n H^{j-1}(K_n)\to H^j(R\varprojlim_n P_n^\bullet)\to\varprojlim_n H^j(K_n)\to0$ for every $j$, where $R\varprojlim_nP_n^\bullet=\operatorname{Cone}(1-T)[-1]$; shifting the initial index from $0$ to $1$ only renames the tower. This cone is a derived limit of the tower $(K_n)$ in $D(\operatorname{Mod}(B_X))$ in the sense of [def-weil-derived-limit]. Indeed, by [det-pe-products-derived] the termwise product $\prod_nP_n^\bullet$, with the images of its termwise projections, is a product of the $K_n$ in $D(\operatorname{Mod}(B_X))$; since the localization functor preserves composites and differences, $\mathrm{pr}_n\circ Q(1-T)=\mathrm{pr}_n-Q(t_n)\circ\mathrm{pr}_{n+1}$, so $Q(1-T)$ is the transition endomorphism $1-s$ of the tower with its canonical transitions from Step 2. The cone triangle $\prod_nP_n^\bullet\xrightarrow{1-T}\prod_nP_n^\bullet\to\operatorname{Cone}(1-T)\to(\prod_nP_n^\bullet)[1]$ is distinguished by [def-weil-abstract-derived-category], and since (TR2) of [def-weil-triangulated-category] is an equivalence, the triangle $\operatorname{Cone}(1-T)[-1]\xrightarrow{-\delta[-1]}\prod_nP_n^\bullet\xrightarrow{1-T}\prod_nP_n^\bullet\to\operatorname{Cone}(1-T)$, whose rotation is the cone triangle (with $\delta$ its third arrow), is distinguished; it is a Roos triangle. Completeness supplies $K$ as a derived limit of this same canonical tower. By clause 1 of [lem-weil-derived-limit-existence], any two derived limits of a fixed tower are isomorphic; hence $H^j(K)\cong H^j(\operatorname{Cone}(1-T)[-1])$, the Milnor middle term. No canonical choice of that isomorphism is needed for vanishing.

Cited nodes: det-pe-milnor-sequence, det-pe-products-derived, def-weil-abstract-derived-category, def-weil-triangulated-category, def-weil-derived-limit, lem-weil-derived-limit-existence.

### Original step 7 -> lem-sf-bounded-epimorphic-top-derived-limit

For $j<a$ both towers in the outer terms of the Milnor sequence are zero by Step 5, as are both towers for $j>b+1$. Their limits and first derived limits are zero (equivalently their defining product kernels and cokernels are zero). At the remaining degree $j=b+1$, the right-hand tower is zero, and the left-hand term is $R^1\varprojlim_n H^b(K_n)$. The transitions of this latter tower are epimorphisms by Step 5, so [det-pe-milnor-epimorphic], applied with ring sheaf $\mathcal R=B_X$, makes that term zero as well. Exactness therefore gives $H^j(K)=0$ in every degree outside $[a,b]$.

Cited nodes: det-pe-milnor-epimorphic.
