# Worker report — Q49

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-parameter-cochain-completion-boundary-descent.json`: unchanged statement, six-step assembly (2323 proof-text characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-cochain-closed-rectangle-certificates.json`: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-cover-retractions-stabilizing-selectors.json`: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-accelerated-finite-field-cochain-differences.json`: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.
- `dag/nodes/sec-six-functors-basics/lem-sfb-retracted-cochain-primitive-summation.json`: statement, unsplit, no Mathlib match; no proof steps or proof dependencies.

`citations.json` supplies verbatim statement quotes for every parent citation. `searches.jsonl` is the actual msearch log. Supporting scripts, the search plan and inherited-proof.json stay in the sandbox. No repository, launcher, Lean, unit or chapter file was written.

## Attachments

None. The upstream keyword/tag search found no declaration stating this boundary-descent assertion. The existing Sheaf module `Sheaf.RepresentationTheory.ParameterCochainCompletionBoundaryDescent`, theorem at line 189, ends in `sorry` at line 211 and cannot be attached. Its docstring preserves the inherited thirteen-step argument.

## Wanted sources

WANTED: an exact continuous-cochain / nonarchimedean analytic reference for lem-sfb-parameter-cochain-completion-boundary-descent; main-20261015 direct-images paragraph (3) supplies the application, not this auxiliary theorem.
WANTED: an exact continuous-cochain / nonarchimedean analytic reference for lem-sfb-cochain-closed-rectangle-certificates; main-20261015 direct-images paragraph (3) supplies the application, not this auxiliary theorem.
WANTED: an exact continuous-cochain / nonarchimedean analytic reference for lem-sfb-closed-cover-retractions-stabilizing-selectors; main-20261015 direct-images paragraph (3) supplies the application, not this auxiliary theorem.
WANTED: an exact continuous-cochain / nonarchimedean analytic reference for lem-sfb-accelerated-finite-field-cochain-differences; main-20261015 direct-images paragraph (3) supplies the application, not this auxiliary theorem.
WANTED: an exact continuous-cochain / nonarchimedean analytic reference for lem-sfb-retracted-cochain-primitive-summation; main-20261015 direct-images paragraph (3) supplies the application, not this auxiliary theorem.

## What changed and why

The returned task explicitly requires redistributing the 9572-character proof into at least three comparable statement-only tasks. Four tasks now carry the mathematical work: certificates (old steps 3–4), topology and selection (5–6), accelerated coefficients (7–10), and correction plus summation (11–13). Boundary cases and the simultaneous metrizable quotient reduction (1–2) stay in the parent. The parent uses each independent interface and checks their shared hypotheses. No task is the whole boundary-descent assertion, and none merely repeats the finite-cover conclusion.

The sandbox initially contained only dispatcher marker files, no delivered nodes, report or searches. I copied the complete current repository node, including all prior citations, Mathlib searches, Lean and review metadata. The server review_split check on that unmodified copy correctly reported no change against origin. There was no older sandbox result or logged search to overwrite. The current repository proof and the Lean docstring supplied the returned argument; it is retained verbatim below. The original statement is byte-identical. The historical source is agent-formulated, so no claim that the blueprint proves it has been added.

## Not duplicates

lem-sfb-cochain-closed-rectangle-certificates vs lem-sfb-profinite-metric-function-quotients: the quotient lemma makes a single map metrizable; the new lemma starts with metrizable spaces and constructs countably many closed finite-field rectangle certificates.
lem-sfb-cochain-closed-rectangle-certificates vs lem-sfb-algcl-countable-closed-finite-cover: the existing lemma covers the coefficient field; the new lemma is about parameter sets and group rectangles for a continuous map.
lem-sfb-closed-cover-retractions-stabilizing-selectors vs lem-sfb-countable-discrete-product-closed-retraction: the existing exact Mathlib leaf is a retraction from an already specified countable discrete product. The new task constructs the compact-space embedding and common shrinking clopen partitions and proves eventual least-cover-index selection; it is more than a specialization of that product theorem.
lem-sfb-accelerated-finite-field-cochain-differences vs lem-sfb-norm-one-finite-subfield-projection: the existing lemma supplies a single contraction on Omega. The new task extends a family to the completion, simultaneously accelerates approximations to z and b against arbitrary norm losses and proves the finite-field cochain identities and pointwise vanishing.
lem-sfb-accelerated-finite-field-cochain-differences vs lem-sfb-finite-subfield-continuous-linear-retraction: that retraction has no norm-one bound, extension to the completion, simultaneous approximation or pointwise cochain decomposition.
lem-sfb-retracted-cochain-primitive-summation vs lem-sfb-finite-index-rectangle-primitive-operator: the existing lemma constructs one finite evaluation operator from a rectangle; the new lemma assumes an entire family of such operators and small exact differences and proves the closed-parameter correction and convergent pointwise finite assembly.
lem-sfb-retracted-cochain-primitive-summation vs lem-sfb-bounded-finite-evaluation-rectangle-replacement: the existing lemma is a prime-to-ell norm-one rectangle operator. The new lemma allows arbitrary norm losses and combines given operators with retractions and stabilizing selectors.
lem-sfb-retracted-cochain-primitive-summation vs lem-sfb-parameter-cochain-completion-boundary-descent: the new lemma has arbitrary incomplete vector coefficients and assumes explicit small exact differences, finite evaluation operators, retractions and stabilizing selectors. It constructs their corrected series; it neither produces these inputs nor compares coefficients with an algebraic closure completion.

Whole-DAG searches used rectangle/certificate, closed retraction, pointwise finite, cochain projection, selector and the four exact proposed ids. The relevant existing results are distinguished above. Whole-blueprint searches `rectangle certificate`, `closed retraction`, `cochain projection`, `pointwise finite`, `finite field rectangle`, `stabilizing selector`, `accelerated projection`, and `primitive summation` found no imported statement for these tasks. The ancestor command returns null, inherited from this agent-created analytic chain; every new node preserves that anchor and prepends the item to the via list. No missing blueprint ancestor was invented.

## Search results

Each task has two distinct LeanFinder phrasings, a Loogle query, a Mathlib grep and LeanSearch, recorded literally from msearch.py. All services answered successfully in this run. Searches returned clopen finite approximation, PiNat closed-product retractions, completion extension maps, generic continuous-map summation, Mahler series, ordinary inhomogeneous differentials, orthogonal projections, and unrelated homological mapping-cone projections. These do not state any of the four interfaces in a one-line specialization. In particular PiNat.exists_retraction_subtype_of_isClosed is reused as the existing leaf, not copied as a new leaf. Additional logged grep verified its source lines 680–687 (and the variant at 675) and LinearMap.extendOfNorm at 190, extendOfNorm_eq at 194–195 and norm_extendOfNorm_apply_le at 201–203. No new Mathlib leaves.

## Review by Q49

I read the main-20261015 six-functors-basics chapter and direct-images paragraph (3), the recorded unit, the item’s thirteen steps and its Lean statement/docstring, all twelve inherited proof-dependency statements, and Stacks topology.tex at lemma-baire-category-locally-compact (Tag 0CQN). That tag gives Baire for locally quasi-compact Hausdorff spaces; applying it to nonempty compact G^(n+1) is legitimate. The blueprint only motivates the open-direct-image application. Each new node therefore explicitly identifies the precise inherited analytic argument it isolates and requests an exact reference, rather than pretending that paragraph (3) asserts it.

For the certificate task, I checked the closed finite-field exhaustion comes as an explicit hypothesis; Baire is applied separately at each parameter, so it does not falsely make a certificate valid on a neighbourhood of that parameter. Normal open subgroups refine all finitely many translated coordinate neighbourhoods. Metrizability supplies a countable clopen basis; compactness makes every clopen set a finite union of basis members, so all subgroups/cosets/rectangles can be enumerated. Evaluation inverse images make A_j closed. Repeating a nonempty certificate handles a finite enumeration.

For the retraction/selector task I checked that finite clopen partitions can be commonly refined while their diameters tend to zero, and that the atom map is an embedding into a countable discrete product. Each A_j is compact, hence its image is closed in that Hausdorff product and nonempty, exactly the hypotheses of the existing product-retraction statement. There is no assertion that an arbitrary nonmetrizable profinite closed subset retracts. A point outside a closed A_j has positive distance from it; this is the precise reason the shrinking neighbourhoods exclude each smaller j eventually. A finite number of smaller indices is then excluded at a fixed s.

For the coefficient task I checked each finite target F_N is complete, allowing extension of a norm-one projection by the exact dense-subspace extension statement. This only extends maps into finite fields; it never constructs a retraction into incomplete Omega. Compact images of both z and b admit finite nets with centres in Omega. An increasing finite-field exhaustion eventually contains their finitely many centres. Taking L_i large enough for those nets, all first i+1 certificates and previous L_i gives simultaneous estimates and strict increase. Linearity commutes with the finite differential; c_i need not vanish pointwise. Algebraicity of an individual z(s,y) makes both adjacent projections eventually fix it. In the rectangle clause j<=i gives L_(i-1)>=N_j, including the first nontrivial pair i=j=1.

For the summation task I checked its hypotheses are data that the other tasks actually deliver, rather than another version of the item. It assumes the exactness of T_j e_i only on A_j, not globally. On A_j the cochain v_(i,j)=c_i-T_j e_i is a cocycle. Pulling that cocycle back by rho_j keeps its differential zero at every parameter, so subtracting it gives dB_(i,j)=e_i globally, including off A_j. The strong triangle inequality gives the stated maximum norm bound without a factor two. Clopen selector fibres make b_i continuous. At each fixed (s,x), the selector eventually stays at one j with rho_j(s)=s, and T_j is then one fixed finite list of evaluations of eventually zero e_i. Thus b_i is eventually zero at that input. Uniform convergence uses completeness only in V-hat; pointwise finite sums restore values in V and its isometric subspace topology restores continuity. The finite differential commutes with this limit.

Parent step 1 cites the completion statement for injectivity/isometry and the finite-extension absolute-value statement for ultrametricity. It handles empty S and degree one directly. Parent step 2 cites the actual clopen-basis and open-normal-basis statements before applying the metric-function quotient theorem; the target metric need not be complete. Its homomorphic q ensures the differential descends, and surjectivity justifies removing the dummy last group coordinate. Parent step 3 cites the actual coefficient exhaustion and new rectangle certificate statements. Parent step 4 uses exactly the new retraction and selector outputs. Parent step 5 cites the actual rectangle operator statement, whose bound allows ell-divisible subgroup index, and the accelerated-coefficient statement; its final clause supplies the needed zero rectangle and hence the operator exactness hypothesis of the summation task. Parent step 6 uses exactly the corrected-series conclusion and pulls back the primitive along the earlier quotient maps. Every cited node’s verbatim statement is in citations.json, and every non-elementary assertion in the parent is supplied by these interfaces.

Small cases checked: empty original S and n=1 stay outside the four tasks; S a singleton gives a repeating certificate and identity retraction; finite G (including trivial G and H=G) has a countable rectangle set and finite index; constant z has eventually zero differences after its values enter one finite field; b=0 and z=0 permit zero projected differences and primitives; A_1=S gives k_i=1; repeated or intersecting A_j do not break the least-index rule. Indices divisible by ell produce C_j>1, which D_i and the accelerated delta_i explicitly absorb. Nothing assumes a uniform bound on C_j or a uniform stabilization index in the parameter.

This repair corrects the single numbered return requirement in all its parts: four genuinely separate new unsplit statements, all actual searched, no proof steps in them, unchanged parent statement, parent proof below 3000 characters, and the complete old arguments assigned below. I kept no parent proof step longer than 2000 characters. No statement dispute or route change was found.

## Allocation and full inherited argument

The following is the exact text and dependency list of every inherited step, retained so the redistribution does not shorten or blur any argument. These paragraphs are work briefs for later workers, not proof steps in the new unsplit JSON nodes. Their sources are the original node’s paragraph-(3) agent expansion and the cited inputs named in each paragraph.

### Inherited step 1 — lem-sfb-parameter-cochain-completion-boundary-descent

If $S=\varnothing$, use the empty family. If $n=1$, then $db=d^0b=0$; the embedding $\iota$ is injective, so $z=0$, and the zero degree-zero cochain is already a primitive. Henceforth $S\ne\varnothing$ and $n\geq2$. We construct a primitive on $S$ itself; the required cover will be the single identity map. Identify $\Omega$ with its isometric image in $B=\widehat\Omega$ using [lem-sfb-normed-field-completion]. The strong triangle inequality holds in $\Omega$: any two algebraic elements lie in one finite extension, where [lem-weil-l-adic-extension-absolute-value] applies. It holds in $B$ by passage to limits, as does scalar norm homogeneity over $\mathbf Q_\ell$.

Inputs: lem-sfb-normed-field-completion, lem-weil-l-adic-extension-absolute-value

### Inherited step 2 — lem-sfb-parameter-cochain-completion-boundary-descent

Read the profinite set $S$ as a compact Hausdorff totally disconnected space; it has a basis of clopen sets by [lem-weil-pbc-profinite-clopen-basis]. By [lem-sfb-profinite-group-open-normal-subgroup-basis], the original compact Hausdorff totally disconnected group $G$ has a neighbourhood basis of open normal subgroups. Thus $S$ and $G$ satisfy the hypotheses of the next input. Apply [lem-sfb-profinite-metric-function-quotients], with $r=n$ and the product metric target $\Omega\times B$, to
$$F(s;g_1,\ldots,g_n)=(z(s;g_1,\ldots,g_n),b(s;g_1,\ldots,g_{n-1})).$$
It gives continuous surjections $p:S\to S_0$, $q:G\to G_0$, the latter a homomorphism, with $S_0,G_0$ metrizable profinite. The first component descends $z$; evaluating the last group argument at $1$ in the second component descends $b$. Its independence of that argument follows by surjectivity of $p,q$. Surjectivity on all powers shows $dz_0=0$ and $db_0=\iota z_0$. A primitive on these quotients pulls back to the original spaces. Rename them $S,G,z,b$ in the rest of the proof.

Inputs: lem-weil-pbc-profinite-clopen-basis, lem-sfb-profinite-group-open-normal-subgroup-basis, lem-sfb-profinite-metric-function-quotients

### Inherited step 3 — lem-sfb-cochain-closed-rectangle-certificates

Apply [lem-sfb-algcl-countable-closed-finite-cover] with $E=\mathbf Q_\ell$ and choose increasing closed finite fields $F_N$ covering $\Omega$. Set
$$f(s;g_0,\ldots,g_n)=z(s;g_0^{-1}g_1,\ldots,g_{n-1}^{-1}g_n).$$
For each $s$, the closed sets $f(s,-)^{-1}(F_N)$ cover the nonempty compact Hausdorff $G^{n+1}$. By [lem-sfb-baire-closed-cover-interior] one has nonempty interior. A product neighbourhood in that interior contains $Ha_0\times\cdots\times Ha_n$ for some open normal subgroup $H$: intersect finitely many translated neighbourhoods of $1$ and apply [lem-sfb-profinite-group-open-normal-subgroup-basis]. Thus every $s$ has a certificate consisting of such a rectangle and a field $F_N$. No neighbourhood of $s$ is asserted to have that certificate.

Inputs: lem-sfb-algcl-countable-closed-finite-cover, lem-sfb-baire-closed-cover-interior, lem-sfb-profinite-group-open-normal-subgroup-basis

### Inherited step 4 — lem-sfb-cochain-closed-rectangle-certificates

A compact metric profinite space has a countable clopen basis: for each positive integer $t$, choose clopen neighbourhoods of diameter $<2^{-t}$ and take a finite subcover. The union of these finite covers is a basis. Every clopen subset is a finite union of basis members, by compactness. Apply this to $G$: there are countably many open subgroups and their cosets, hence countably many coset rectangles. Enumerate all rectangle/field pairs with nonempty certificate sets as $(B_j,N_j)$, $j\geq1$, repeating entries if the list is finite, and put
$$A_j=\{s:f(s,B_j)\subseteq F_{N_j}\}.$$
Each $A_j$ is closed, as an intersection of inverse images of the closed field $F_{N_j}$ under continuous evaluation maps. The preceding step gives $S=\bigcup_{j\geq1}A_j$, with every $A_j$ nonempty. Write $B_j=H_ja_{j,0}\times\cdots\times H_ja_{j,n}$. Each $H_j$ has finite index: its disjoint open cosets cover compact $G$, hence admit a finite subcover.

Inputs: elementary in the inherited split.

### Inherited step 5 — lem-sfb-closed-cover-retractions-stabilizing-selectors

Choose finite clopen partitions $\mathcal P_t$ of $S$ refining each other, with all atom diameters $<2^{-t}$. Obtain them from finite clopen covers at each scale by taking their finite Boolean refinements and then common refinements. Map $S$ to $D=\prod_t\mathcal P_t$ by its atom at each level. This map $e$ is continuous. It is injective because the mesh tends to zero; its inverse on its image is continuous because fixing the $t$th coordinate confines the inverse to one atom of diameter $<2^{-t}$. For each $j$, $e(A_j)$ is compact and closed in the Hausdorff space $D$: a point outside this compact set has neighbourhoods separating it from each of its points, and finitely many of the latter neighbourhoods cover the set. Apply [lem-sfb-countable-discrete-product-closed-retraction] to the nonempty closed subset $e(A_j)\subseteq D$. Restrict the resulting map to $e(S)$ and compose with $e^{-1}$. This gives a continuous $\rho_j:S\to A_j$ fixing $A_j$ pointwise.

Inputs: lem-sfb-countable-discrete-product-closed-retraction

### Inherited step 6 — lem-sfb-closed-cover-retractions-stabilizing-selectors

For $i\geq1$ let $U_{j,i}$ be the union of the atoms of $\mathcal P_i$ meeting $A_j$. These are clopen, decrease with $i$, and have intersection $A_j$: a point outside the closed $A_j$ has positive distance from it and is eventually in an atom disjoint from it. Let $k_i(s)$ be the least $j\leq i$ with $s\in U_{j,i}$, or $1$ when none exists. This is locally constant with finite range. For each $s$, let $j(s)$ be the least $j$ with $s\in A_j$. Eventually all $j<j(s)$ are excluded from $U_{j,i}$, while $s\in U_{j(s),i}$ always. Thus $k_i(s)=j(s)$ for all sufficiently large $i$.

Inputs: elementary in the inherited split.

### Inherited step 7 — lem-sfb-accelerated-finite-field-cochain-differences

For each rectangle $B_j$ choose the operator $T_j$ of [lem-sfb-finite-index-rectangle-primitive-operator], with $C_j=|[G:H_j]|_\ell^{-1}$. It works for every coefficient field used below and for profinite parameter families. In particular, for every cocycle $c$ with homogeneous function zero on $B_j$, one has $dT_jc=c$. All $C_j$ are finite, even when the subgroup index is divisible by $\ell$. Put $D_t=\max(1,C_1,\ldots,C_t)$ for $t\geq1$ and $\delta_i=2^{-i}/D_{i+1}$ for $i\geq0$.

Inputs: lem-sfb-finite-index-rectangle-primitive-operator

### Inherited step 8 — lem-sfb-accelerated-finite-field-cochain-differences

For every $N$, [lem-sfb-norm-one-finite-subfield-projection] gives a $\mathbf Q_\ell$-linear contraction $p_N:\Omega\to F_N$ fixing $F_N$. The finite field $F_N$ is complete by [lem-weil-l-adic-extension-complete]. Apply [lem-sfb-dense-subspace-contractive-extension] to the dense normed $\mathbf Q_\ell$-subspace $\Omega\subseteq B$, with target $F_N$. It extends $p_N$ to a linear contraction $P_N:B\to F_N$, still fixing $F_N$. Density here is the defining density of the canonical inclusion in the metric completion; no continuous retraction $B\to\Omega$ is used.

Inputs: lem-sfb-norm-one-finite-subfield-projection, lem-weil-l-adic-extension-complete, lem-sfb-dense-subspace-contractive-extension

### Inherited step 9 — lem-sfb-accelerated-finite-field-cochain-differences

For each $i\geq0$, compactness of the images of $z$ and $b$ gives finite $\delta_i$-nets with centres in $\Omega$ (use its density in $B$ for the image of $b$). Choose strictly increasing $L_i\geq i$ so that $F_{L_i}$ contains all these centres and $L_i\geq N_j$ for $j\leq i+1$. This is possible since the increasing $F_N$ cover $\Omega$. Put $P_i=P_{L_i}$. If $a\in F_{L_i}$ is a chosen centre within $\delta_i$ of $x$, contractivity and $P_ia=a$ give
$$|P_ix-x|\leq\max(|P_i(x-a)|,|a-x|)\leq\delta_i.$$
Consequently $\|P_iz-z\|_\infty\leq\delta_i$ and $\|P_ib-b\|_\infty\leq\delta_i$. The same choice controls both maps and all the first $i+1$ rectangle constants.

Inputs: elementary in the inherited split.

### Inherited step 10 — lem-sfb-accelerated-finite-field-cochain-differences

Set $P_{-1}=0$, $e_i=(P_i-P_{i-1})z$ and $c_i=(P_i-P_{i-1})b$ for $i\geq0$. All are continuous $F_{L_i}$-valued cochains; the linear coefficient maps commute with every finite sum in $d$, so $dc_i=e_i$ and $de_i=0$. Their telescoping sums are $\sum_{h=0}^ie_h=P_iz\to z$. For $i\geq1$, both supremum norms are at most $\max(\delta_i,\delta_{i-1})$. At any fixed input $(s,y)$ of $z$, $e_i(s,y)$ is eventually zero: the algebraic value $z(s,y)$ lies in one $F_N$ and both projections eventually fix it. This last assertion is made only for $z$, not for the completed primitive $b$.

Inputs: elementary in the inherited split.

### Inherited step 11 — lem-sfb-retracted-cochain-primitive-summation

For $i\geq1$ and $j\leq i$ put $v_{i,j}=c_i-T_je_i$ and define
$$B_{i,j}(s,x)=(T_je_i)(s,x)+v_{i,j}(s,x)-v_{i,j}(\rho_j(s),x).$$
These are continuous $F_{L_i}$-valued cochains. At $a\in A_j$, the homogeneous values of $z(a,-)$ on $B_j$ lie in $F_{N_j}$, which both $P_i$ and $P_{i-1}$ fix since $L_{i-1}\geq N_j$. Thus the homogeneous function of $e_i(a,-)$ vanishes there. The rectangle operator gives $dT_je_i(a,-)=e_i(a,-)$, so $dv_{i,j}(a,-)=0$. Therefore
$$dB_{i,j}=dT_je_i+(e_i-dT_je_i)-0=e_i.$$
Also $B_{i,j}(s,-)=T_je_i(s,-)$ for $s\in A_j$, because $\rho_j(s)=s$. Its supremum norm is at most $\max(\|c_i\|_\infty,C_j\|e_i\|_\infty)$, by the ultrametric inequality and the operator bound.

Inputs: lem-sfb-finite-index-rectangle-primitive-operator

### Inherited step 12 — lem-sfb-retracted-cochain-primitive-summation

Let $b_0=c_0$. For $i\geq1$ define $b_i(s,x)=B_{i,k_i(s)}(s,x)$. The finitely many clopen pieces of $k_i$ make this a continuous $F_{L_i}$-valued cochain with $db_i=e_i$. Since $k_i(s)\leq i$, the preceding bound and $D_i\max(\delta_i,\delta_{i-1})\leq2^{-(i-1)}$ give $\|b_i\|_\infty\leq2^{-(i-1)}$. Here $D_i\delta_{i-1}=2^{-(i-1)}$ and $D_i\delta_i\leq2^{-i}$. Fix $(s,x)$. Eventually $k_i(s)=j(s)$ and $s\in A_{j(s)}$, so
$$b_i(s,x)=T_{j(s)}e_i(s,x)=\sum_{a=1}^{u_{j(s)}}\alpha_{j(s),a}e_i(s,\psi_{j(s),a}(x)).$$
This is one fixed finite list of evaluations. Each term is eventually zero by step 10. Hence $b_i(s,x)=0$ for all sufficiently large $i$.

Inputs: lem-sfb-finite-index-rectangle-primitive-operator

### Inherited step 13 — lem-sfb-retracted-cochain-primitive-summation

The partial sums $\sum_{i=0}^Nb_i$ are uniformly Cauchy into the complete field $B$: by the ultrametric inequality every tail has norm at most the largest norm of its terms, and those norms tend to zero. Their pointwise limits therefore give a uniform limit $b_*:S\times G^{n-1}\to B$. For continuity, approximate $b_*$ uniformly within any prescribed positive error by one continuous partial sum and use the strong triangle inequality near the point in question. Step 12 makes every value a finite sum in $\Omega$; the isometric subspace topology then makes $b_*$ continuous into $\Omega$ itself. At a fixed input $d$ is a finite sum of evaluations, so
$$db_*=\lim_Nd\Big(\sum_{i=0}^Nb_i\Big)=\lim_NP_Nz=z.$$
Pull back this cochain by $p\times q^{n-1}$ from step 2. It is a genuine $\Omega$-valued continuous primitive on the original $S$. Choose $S_1=S$, $u_1=\mathrm{id}_S$. This proves the requested assertion with actual equality of cochains.

Inputs: lem-sfb-normed-field-completion

## Unfinished work

Only the required statement-only tasks remain open for other workers. The exact external analytic references remain WANTED. Required server dry run and direct push are the delivery validation; no Lean was compiled.
