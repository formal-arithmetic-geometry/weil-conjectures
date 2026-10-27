# Worker report: lem-trf-derived-evaluation-pseudocoherent

## Files written

- dag/nodes/sec-trace-formula/lem-trf-derived-evaluation-pseudocoherent.json: retained statement, short assembly split.
- dag/nodes/sec-trace-formula/lem-trf-double-evaluation-finite-components.json: statement, unsplit; no full Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-double-evaluation-signed-derived-model.json: statement, unsplit; no full Mathlib match.
- citations.json: exact statement quotations for every parent step citation.

## Attachments

None. Read the project module Sheaf.Algebra.Homology.DerivedEvaluationPseudoCoherent: isIso_evaluation_of_isPseudoCoherent ends in sorry at line 106. The searches in lean/WeilConjectures found no finished theorem with every clause. This stage changes no Lean.

## WANTED

None. Stacks more-algebra.tex contains all source arguments.

## Returned issue and repair

The retained sandbox had no node, report, citations or search log, only dispatcher markers. I copied the current shared node, whose proof has the returned eight steps, and preserved all its other fields. No git operation was run in the shared repository. There was no earlier sandbox split/report on which to run an initial dry run. The current shared node is the returned mathematical version, with stage-2 and review metadata retained.

The sole return requires at least two substantial new unsplit nodes and a parent proof at most 3000 characters. The two children separate graded invertibility from differential compatibility and canonical normalization; neither restates the derived isomorphism. The first needs no injectivity and the second needs no boundedness or finite-freeness and asserts no invertibility. They can be worked on independently. Original steps 4 and 7 belong to finite-components; steps 3, 5 and 6 belong to signed-derived-model. Steps 1, 2 and 8 remain the assembly. All eight old arguments appear verbatim below; no argument was shortened away. Neither child has proof steps, proof dependencies or a proof sketch in its statement.

## Searches and duplicate investigation

Read actual msearch results and retained their command-generated queries/digests in searches.jsonl. Both nodes have LeanFinder, Loogle, grep and LeanSearch attempts, with second semantic phrasings. LeanSearch was rate limited and is recorded unavailable. HasGoodTensor and tensorObj concern tensor totalization, not double Hom; Double.lean defines a two-term complex, unrelated to double Hom. Read Monoidal.lean lines 45--76 and Double.lean lines 30--85. Read Contraction.lean lines 150--185: dualTensorHomEquivOfBasis is an ordinary finite module duality, not the finite-diagonal double-Hom comparison, so does not make the whole child a one-line specialization.

Whole-DAG searches by Tags 0A60/0A61/0A67/0A68 and by signed evaluation, finite support and double Hom, and blueprint_refs searches for evaluation, double Hom, evaluation pseudocoherent, signed evaluation, finite support, evaluate-and-more and internal-hom-evaluate found no existing statement giving either child. The canonical-map node's proof contains a related representative formula, but its statement only gives the derived map and triangle naturality; citing that proof for a chain model would be C4. The project ModuleHomComplex infrastructure defines total Hom, not either comparison.

## Not duplicates

lem-trf-double-evaluation-finite-components vs lem-trf-derived-evaluation-pseudocoherent: new statement is finite-support graded decomposition and the specified component inverse for actual complexes without injectivity; existing statement is a derived evaluation theorem or construction and supplies neither these bounds nor these module inverses.
lem-trf-double-evaluation-finite-components vs lem-trf-derived-evaluation-canonical-map: new statement is finite-support graded decomposition and the specified component inverse for actual complexes without injectivity; existing statement is a derived evaluation theorem or construction and supplies neither these bounds nor these module inverses.
lem-trf-double-evaluation-finite-components vs lem-trf-derived-evaluation-finite-injective: new statement is finite-support graded decomposition and the specified component inverse for actual complexes without injectivity; existing statement is a derived evaluation theorem or construction and supplies neither these bounds nor these module inverses.
lem-trf-double-evaluation-signed-derived-model vs lem-trf-derived-evaluation-pseudocoherent: new statement gives the chain formula, differential identities and its comparison with the canonical derived map for arbitrary K-flat/K-injective representatives; existing statement neither states that chain-level comparison nor its sign identities.
lem-trf-double-evaluation-signed-derived-model vs lem-trf-derived-evaluation-canonical-map: new statement gives the chain formula, differential identities and its comparison with the canonical derived map for arbitrary K-flat/K-injective representatives; existing statement neither states that chain-level comparison nor its sign identities.
lem-trf-double-evaluation-signed-derived-model vs lem-trf-derived-evaluation-finite-injective: new statement gives the chain formula, differential identities and its comparison with the canonical derived map for arbitrary K-flat/K-injective representatives; existing statement neither states that chain-level comparison nor its sign identities.

## Review by O4

I read Stacks more-algebra.tex lemma-internal-hom-evaluate-isomorphism (0A68), including its finite support proof for case (2), lemma-evaluate-and-more (0A60), its three sign recurrences, remark-sign-explanation (0A61), and lemma-internal-hom-evaluate (0A67). These are the sources of the parent and of both new nodes. The source's last sign display has inconsistent dummy subscripts; I use the three preceding recurrences and the remark's sign, which agree with the retained proof. The parent statement is unchanged and requires no dispute.

For parent Step 1 I opened the actual statements of def-pc-ring-pseudo-coherent-complex (bounded-above finite free model), lem-weil-pbc-ring-modules-enough-injectives (ordinary module category has enough injectives), and lem-weil-pbc-dplus-injective-representative (bounded-below injective model AND bounded-below injectives are K-injective). Their hypotheses apply over the given commutative ring; M's bounded injective model is expressly a hypothesis, so is not an existence assertion borrowed from a definition.

For Step 2 I read lem-pc-module-bounded-flat-kflat (bounded-above flat implies acyclic-tensor K-flatness), def-pc-module-kflat-complex (its quasi-isomorphism-preserving equivalent convention), and lem-pc-source-kflat-module-tensor-model (one K-flat factor suffices with an arbitrary other factor). Finite freeness gives flatness by the displayed finite-direct-sum argument, which stays in the parent. The tensor symmetry puts P on the correct side and imposes no flatness on H. These off-unit lemmas remain declared generic tools.

Step 3 cites the new signed-derived-model statement: it expressly supplies the chain map, both derived object comparisons and equality with the specified canonical morphism. K-flat P and K-injective I,J were established in Steps 1--2. The formula has no boundedness requirement, so none is silently added. Step 4 cites finite-components: its statement expressly supplies finite ranges, decomposition and inverse for every degree; its bounds and finite-freeness are exactly those chosen in Step 1. I checked the parity ks=s(r+1) modulo 2 independently. Step 5 uses only functoriality of localization from def-weil-abstract-derived-category and the written multiplication of the chain identity by component inverses. All citations.json quotations are copied from the cited statements, not their proofs.

For finite-components I checked p in [a,b], r<=-ell, s<=u imply n-b+ell<=s and n-b-u<=r, and A^k only uses ell-k<=s<=u. Thus every remaining product is finite before it is replaced by a sum, including Hom from A^k. I checked both finite-basis inverse composites as in original step 7. For signed-derived-model I checked the d_I, d_J and d_P recurrences and the transposition exponent kh+kn=ks, where n=h+s. K-flat replacement of A gives the canonical derived transpose; the original replacement argument is retained below for the next worker. This child gives derived-category object comparisons, not a replacement by per-cohomology statements.

Small cases: zero ring, any zero input and empty index ranges give zero modules and the unique inverse; rank-zero P^s uses an empty basis sum. For complexes concentrated in single degrees the sign is (-1)^(ks), with k=-r-s; negative odd degrees obey the same parity calculation. Rank two verifies that all basis components, rather than a single evaluation coordinate, are required. For P unbounded below the fixed-degree bounds still cut out a finite set; I need not claim a uniform finite set over all n. No finiteness of J's modules is used. Removing I's lower or upper bound is not done in the finite-components statement, while the signed model deliberately allows unbounded injective representatives because it asserts no invertibility.

Checked B--E: new statements introduce every object and cite their notions, source labels/tags are explicit, new nodes are statement-only, neither relocates the whole conclusion, no dependency on the parent creates a cycle, no SGA route is used, and every non-elementary parent input is stated in a cited node. No remaining parent step exceeds 2000 characters. The full original argument distribution below is the proof handoff for parallel work, not proof text inside the new nodes.

## Preserved original arguments and assignment

### Original step 1 -> parent assembly

Choose a bounded-above complex $P$ of finite free $R$-modules representing $K$, by [def-pc-ring-pseudo-coherent-complex], and an integer $u$ with $P^s=0$ for $s>u$. The finite-injective-dimension hypothesis, in the explicit meaning given in the statement, supplies a bounded complex of injective modules $I$ representing $M$; fix $a\le b$ with $I^p=0$ outside $[a,b]$. By [lem-weil-pbc-ring-modules-enough-injectives] the abelian category of $R$-modules has enough injectives. Apply [lem-weil-pbc-dplus-injective-representative] to $L\in D^+(R)$ to obtain a bounded-below complex of injectives $J$ representing $L$, with $J^j=0$ for $j<\ell$. Both $I$ and $J$ are K-injective by the bounded-below-injective assertion of that same node. All bounds are bounds on terms of these chosen complexes, not just on their cohomology.

Cited statements: def-pc-ring-pseudo-coherent-complex, lem-weil-pbc-ring-modules-enough-injectives, lem-weil-pbc-dplus-injective-representative.

### Original step 2 -> parent assembly

Each $P^s$ is flat: after choosing a finite basis, tensoring with $P^s$ is a finite direct sum of the identity functor on modules, and hence preserves exact sequences componentwise. Consequently [lem-pc-module-bounded-flat-kflat] makes $P$ K-flat. Use the equivalent quasi-isomorphism criterion of [def-pc-module-kflat-complex] to express this in the categorical K-flat convention. Then [lem-pc-source-kflat-module-tensor-model], together with the symmetry $x\otimes y\mapsto(-1)^{|x||y|}y\otimes x$, computes $R\operatorname{Hom}(L,M)\otimes_R^{\mathbf L}K$ by $T=\operatorname{Tot}(H\otimes_R P)$, where $H=\operatorname{Hom}_R^\bullet(J,I)$. No K-flatness of $H$ is required.

Cited statements: lem-pc-module-bounded-flat-kflat, def-pc-module-kflat-complex, lem-pc-source-kflat-module-tensor-model.

### Original step 3 -> lem-trf-double-evaluation-signed-derived-model

Specialize [def-pur-derived-internal-hom] to the one-object ringed site with ring $R$. Because $I,J$ are K-injective, it identifies $H=\operatorname{Hom}_R^\bullet(J,I)$ with a representative of $R\operatorname{Hom}_R(L,M)$, $A=\operatorname{Hom}_R^\bullet(P,J)$ with a representative of $R\operatorname{Hom}_R(K,L)$, and $B=\operatorname{Hom}_R^\bullet(A,I)$ with a representative of the target. These are the product total Hom complexes of [def-sc-module-total-hom-complex], with differential $d(f)=d_{\rm target}f-(-1)^{|f|}fd_{\rm source}$.

Cited statements: def-pur-derived-internal-hom, def-sc-module-total-hom-complex.

### Original step 4 -> lem-trf-double-evaluation-finite-components

Fix a degree $n$. A potentially nonzero triple component is indexed by $p+r+s=n$ and has source $\operatorname{Hom}_R(J^{-r},I^p)\otimes_R P^s$. Necessarily $a\le p\le b$, $r\le-\ell$, and $s\le u$, whence $n-b+\ell\le s\le u$ and $n-b-u\le r\le-\ell$. Thus there are finitely many such triples. Moreover $A^k=\prod_s\operatorname{Hom}_R(P^s,J^{s+k})$ has only $\ell-k\le s\le u$ potentially nonzero factors. Hence every product that occurs here is a finite product after zero factors are removed, and so equals the finite direct sum. Using the component projections and inclusions gives the identifications
$$T^n\cong\bigoplus_{p+r+s=n}\operatorname{Hom}_R(J^{-r},I^p)\otimes_R P^s,$$
$$B^n\cong\bigoplus_{p+r+s=n}\operatorname{Hom}_R(\operatorname{Hom}_R(P^s,J^{-r}),I^p),$$
with the finite ranges just proved. The identifications use only finite distributivity of tensor over sums and the fact that a linear map from a finite direct sum is the tuple of its restrictions.

Cited statements: def-sc-module-total-hom-complex, def-pc-tensor-complex-sheaves.

### Original step 5 -> lem-trf-double-evaluation-signed-derived-model

Define $E:T\to B$ on the triple summand $(p,r,s)$ to be
$$g\otimes x\longmapsto\bigl(f\longmapsto\epsilon_{p,r,s}\,g(f(x))\bigr),\qquad\epsilon_{p,r,s}=(-1)^{s(r+1)},$$
where $g:J^{-r}\to I^p$, $x\in P^s$, and $f:P^s\to J^{-r}$. Extend by the finite sum in Step 4 and by precomposing with the corresponding projection of $A^{p-n}$. This is a chain map. Indeed, substituting the Hom differential and total tensor differential of [def-sc-module-total-hom-complex, def-pc-tensor-complex-sheaves], equality for the terms involving $d_I,d_J,d_P$, respectively, reduces to
$$\epsilon_{p,r,s}=\epsilon_{p+1,r,s},\qquad\epsilon_{p,r,s}=(-1)^s\epsilon_{p,r-1,s},\qquad\epsilon_{p,r,s+1}=(-1)^{r+1}\epsilon_{p,r,s}.$$
All three follow immediately from the displayed exponent. Thus there is no unverified assertion about compatibility with differentials.

Cited statements: def-sc-module-total-hom-complex, def-pc-tensor-complex-sheaves.

### Original step 6 -> lem-trf-double-evaluation-signed-derived-model

The localized $E$ is the specified canonical evaluation, rather than an arbitrary map between the two objects. To check this, transpose as in [lem-trf-derived-evaluation-canonical-map]. Write $h=p+r$, $k=-r-s$, so $g$ has Hom degree $h$ and $f$ has Hom degree $k$. In the composite $A\otimes H\otimes P\to I$, moving $f$ past $g$ contributes $(-1)^{kh}$; the two evaluations then give $g(f(x))$. The ordinary Hom transposition from $A\otimes T$ to $\operatorname{Hom}(A,I)$ contributes $(-1)^{kn}$, where $n=h+s$. Thus the adjoint sends $g\otimes x$ to $f\mapsto(-1)^{k(h+n)}g(f(x))=(-1)^{ks}g(f(x))$. Since $ks=(-r-s)s\equiv s(r+1)\pmod2$, this is exactly Step 5. Here evaluation with the Hom factor first is $f\otimes x\mapsto f(x)$, as follows directly from the Hom differential. Choose a K-flat resolution of $A$ using [lem-pc-kflat-resolution] on the one-object site. These computations also hold after precomposing $A$ with that resolution: both sides simply replace $f$ by its image in $A$. Since $P$ is K-flat and $I,J$ are K-injective, the tensor and Hom models in Steps 2 and 3 compute precisely these derived composites and their transpose. This verifies the canonical normalization, including its sign, on the chosen models.

Cited statements: lem-trf-derived-evaluation-canonical-map, def-pur-derived-internal-hom, lem-pc-source-kflat-module-tensor-model, lem-pc-kflat-resolution.

### Original step 7 -> lem-trf-double-evaluation-finite-components

For each triple, put $V=J^{-r}$ and $W=I^p$. The unsigned map $c:\operatorname{Hom}_R(V,W)\otimes_R P^s\to\operatorname{Hom}_R(\operatorname{Hom}_R(P^s,V),W)$, $c(g\otimes x)(f)=g(f(x))$, is an isomorphism by the following explicit finite-basis argument. Choose a finite basis $(e_i)$ of $P^s$ and let $\iota_i:V\to\operatorname{Hom}_R(P^s,V)$ send $v$ to the map taking $e_j$ to $\delta_{ij}v$. The inverse sends $\beta$ to $\sum_i(\beta\circ\iota_i)\otimes e_i$. Composing with $c$ gives $f\mapsto\sum_i\beta(\iota_i(f(e_i)))=\beta(f)$. Conversely, on $g\otimes x$, writing $x=\sum_i x_i e_i$ gives $\sum_i x_i g\otimes e_i=g\otimes x$. Thus both composites are identities. Multiplying $c$ by the unit $\epsilon_{p,r,s}\in\{1,-1\}$ preserves invertibility. Step 4 identifies $E^n$ with a finite direct sum of these invertible maps, so $E^n$ is invertible for every integer $n$.

Cited statements: def-pc-ring-pseudo-coherent-complex.

### Original step 8 -> parent assembly

The componentwise inverses of $E$ form a chain map: from $d_BE=Ed_T$, multiply in consecutive degrees by the two component inverses to obtain $E^{-1}d_B=d_TE^{-1}$. Hence $E$ is an isomorphism of complexes. Localization into $D(R)$ preserves its inverse by functoriality [def-weil-abstract-derived-category]. With the identifications of Steps 2 and 3 and the normalization of Step 6, its localization is exactly the canonical morphism in the statement. It is therefore an isomorphism.

Cited statements: def-weil-abstract-derived-category.

## Unfinished work

The two new nodes are intentionally statement-only for other workers to split. Stage 1 delivery only; no Lean was written or compiled.
