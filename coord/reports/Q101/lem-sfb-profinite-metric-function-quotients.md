# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-metric-function-quotients.json`: repaired split, statement unchanged; six assembly steps, 2185 characters of proof text.
- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-product-finite-oscillation.json`: new statement, unsplit; no Mathlib match after two semantic phrasings, Loogle and source grep; the first LeanSearch query was rate-limited and is recorded unavailable.
- `dag/nodes/sec-six-functors-basics/lem-sfb-countable-finite-coordinate-images.json`: new statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep.
- `citations.json`: verbatim statement quotations for every node used by every parent step.

## Attachments

None. The search in `lean/WeilConjectures/` by the blueprint tag and by profinite/metric quotient concepts found no declaration stating this item. `lean/Sheaf/Topology/ProfiniteMetricFunctionQuotients.lean:67` states the item but its body is `sorry` at line 75, so it is not an attachment. Its theorem has precisely the original hypotheses and all the conclusion clauses. No Lean file was edited or compiled.

## WANTED

WANTED: an external textbook or paper reference for simultaneous metrizable profinite space/group quotient factorization of a metric-valued function, for `lem-sfb-profinite-metric-function-quotients`.

WANTED: an external reference for finite rectangular quotient oscillation with the same open normal subgroup in all group coordinates, for `lem-sfb-profinite-product-finite-oscillation`.

WANTED: an external reference for the compact countable finite-coordinate image construction including the open-normal kernel basis, for `lem-sfb-countable-finite-coordinate-images`.

## Fault and repair

The return asks that a 6016-character proof be spread across at least two comparable independently claimable statements, with parent assembly at most 3000 characters. This repair adds two such nodes, both `unsplit`, with no proof or proof dependencies. The first owns the local-to-uniform finite rectangle argument, Boolean refinement, normal intersection, finite-index argument and continuity of the finite quotient maps (old steps 2-4). The second owns the compact diagonal-image construction, clopen cylinder basis, subgroup operations and open-normal kernel basis, plus metrizability by countable separation (old steps 5-7). These carry approximately 2170 and 1925 characters of the old proof respectively. They share only input notions, and neither depends on the other or on the item. Neither asserts a factorization of a continuous metric-valued function through metrizable quotients.

The parent retains the empty case (old step 1), countable choices at epsilon 2^(-n) (the application in old step 4), fibre constancy (old step 8), the compact-to-Hausdorff quotient criterion (old step 9), and descent with actual Y-values and the universe check (old step 10). The full old proof is archived verbatim below; no former argument is discarded or replaced by a vague summary. Its future proof obligations are now assigned explicitly to the two new statements. No item statement correction, source dispute, new coefficient category or route change is involved.

The sandbox initially contained only dispatcher brief markers: no item, report, citations or searches. The first required dry run exited with `FAILED: no node files`. I therefore copied the current read-only repository node, which is the returned ten-step version, and retained all its existing searches and metadata. There was no earlier sandbox report or search log to recover. The delivery tool creates and rebases its own worktree; no git command was run in the read-only repository.

## Not duplicates

lem-sfb-profinite-product-finite-oscillation vs lem-sfb-profinite-finite-map-approximation: the existing leaf approximates by an arbitrary finite map out of the entire domain; it does not give separate parameter and group quotients, or one common normal subgroup in every group coordinate.

lem-sfb-profinite-product-finite-oscillation vs lem-sfb-profinite-action-finite-quotients: the existing theorem refines partitions for a continuous group action and identifies a limit; it says nothing about epsilon bounds for an arbitrary metric-valued function on S times G^r.

lem-sfb-profinite-product-finite-oscillation vs lem-exc-etale-open-subgroup-quotient-finite-discrete: the existing leaf only establishes finiteness/discreteness for a specified open subgroup of a Galois group, not the oscillation subgroup and clopen partition for general profinite groups.

lem-sfb-countable-finite-coordinate-images vs lem-sfb-compact-countable-separating-metrizable: the existing leaf gives metrizability once compactness and separating metric-valued maps are supplied; it does not construct compact profinite images, group operations or a normal-subgroup basis.

lem-sfb-countable-finite-coordinate-images vs lem-sfb-finite-quotient-fiber-product: the existing statement represents a profinite fibre product by a compatible-partition limit; it neither concerns a prescribed sequence of coordinates nor asserts metrizability or a group-image normal basis.

lem-sfb-countable-finite-coordinate-images vs new-lem-zl-relative-finite-profinite-presentation: relative finite-clopen presentations over a base have no countability, metrizable diagonal image, or group structure clause.

The whole DAG and imported blueprint were searched for profinite quotients, oscillation, metrizability, countable products and coordinate images. `blueprint_refs.py search` found no metrizable, oscillation, finite oscillation or coordinate images node; the finite-quotient/countable-product hits concerned coefficient reductions or homological products. The nearest blueprint ancestor command returns null. Both new nodes retain that value and prepend the parent to its inherited via chain; this existing scalar tame-kernel expansion is agent-authored, not an invented blueprint theorem.

## Review by Q101

I read `GOAL.md`, the fixed six-functors-basics chapter, the inherited `sk-thm-sf-ctf-stability` unit record, the current main-20261015 direct-images proof, and every old item step. Paragraph (3) only motivates direct-image reductions; it contains no topological lemma. Accordingly I retain the agent proof origin and WANTED reference, and the two new source records say explicitly which part of the agent expansion they extract. I do not attribute these arguments to SGA or to an unrelated Stacks tag. I read the full statement of each citation in the assembled parent. `citations.json` contains exactly those statements, copied verbatim, rather than paraphrases of what their proofs might supply.

Step 1 retains the original empty-space construction. The empty map onto empty S_0 is surjective, G maps onto the one-element group, and S_0 times G_0^r is empty even when Y is empty.

Step 2 uses the full new finite-oscillation statement: it explicitly supplies finite A and finite group B with continuous surjections, the group map a homomorphism, and the epsilon bound on their common product fibres. Its hypotheses are exactly the parent's clopen and open-normal bases, compactness, continuity and finite r. I checked the triangle inequality bound 2 epsilon/3, finite rectangle subcover, Boolean atoms and common subgroup intersection in the preserved argument. Normality is required for the quotient group; commutativity is never used. Finiteness follows because distinct open cosets must each occur in any subcover. This is a real multi-step uniformity argument, not an elementary standalone new node or a clause of the parent.

Step 3 uses the full new coordinate-image statement, applied to the compact Hausdorff S and topological group G and the finite maps of step 2. It gives precisely the images, topology, continuous surjections, homomorphism, profinite and metrizable properties and the coordinate-equality equivalences being used. I checked all hypotheses without assuming the coordinates jointly injective or the original spaces metrizable. For its future worker I retained the old proofs of continuity on cylinders, compactness of images, Hausdorff separation by coordinates, clopen cylinders and group continuity. The K_F basis consists of open normal subgroups in the image group even when the coordinates have nontrivial kernels. I read `lem-sfb-compact-countable-separating-metrizable` and its Mathlib source `Topology/MetricSpace/PiNat.lean:1063-1097`: finite discrete targets carry 0/1 metrics and coordinate maps separate image tuples, so its compactness and separation assumptions hold. I also read the original compact-image and subspace-topology statements; they support exactly this future proof, not a stronger unproved quotient claim.

Step 4 is the explicit elementary assembly of the epsilon bounds: a nonnegative distance smaller than 2^(-n) for every n is zero. It uses equality in the metric space Y itself; no limit of Y-valued approximations and no completeness are used.

Step 5 cites `lem-weil-pbc-tychonoff-product-quasi-compact`, whose actual statement allows any family of compact spaces with the product topology. S and all r copies of G satisfy this, so it applies to D. Continuity of R follows from its coordinates, surjectivity by independent finite choices, and Hausdorffness by separation in a differing coordinate. I read `lem-sfb-compact-hausdorff-surjection-quotient`: it allows U=X and V=Y explicitly and assumes only compactness of the domain, Hausdorffness of the target and continuous surjectivity. All are established before invoking it. No small-index or coefficient hypothesis is hidden here.

Step 6 chooses the value on a nonempty fibre and uses step 4 to make it independent of the representative. The open-preimage equality plus step 5 proves continuity. The cited `def-weil-size-convention` is the actual Grothendieck-universe convention; closure under subsets, finite/countable products and quotient sets is the elementary universe calculation being used, not an asserted extra theorem in the definition.

I checked B1-B9: new statements introduce all objects; topological terms are inline or refer to the actual subspace/size definition; no proof sketches or proof dependencies occur in them; their sources honestly identify agent expansion; TeX uses a single backslash after JSON parsing; searches and actual response records are copied from `searches.jsonl`. `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal` in `Topology/Separation/DisjointCover.lean:140` only gives an arbitrary finite factor, so it is not a one-line specialization to rectangular homomorphic quotients. The related open-subgroup facts at `Topology/Algebra/OpenSubgroup.lean:287` and `ClopenNhdofOne.lean:48` do not supply the uniform rectangle refinement. The coordinate-image search found product/limit constructors in `Profinite/Product.lean` and `ProfiniteGrp/Basic.lean`; I read their types, which do not assert the whole new statement. Two differently phrased semantic searches were run per new node. The first node's LeanSearch was unavailable due to a real rate limit; this is not logged as evidence of absence. C1-C5 are addressed by reading every cited statement, retaining all former arguments below the extracted statements, and whole-DAG/blueprint/source searches before creating them. The new nodes have only definition statement dependencies, so they cannot cycle back to the parent; the parent's dependency list is the union of its uses. Both new statements inherit the parent's chapter and unit, with no off-route theorem substitution (C7-C8).

For E1-E7 I tested both new statements on empty S, singleton/finite spaces, trivial G, noncommutative finite G, r=1, constant f, and a noncomplete metric Y. Empty A_n in the second statement forces S empty if a coordinate map exists, and the image construction is still valid; B_n cannot be empty because it is a group. Coordinate maps need not be onto or separate points of S or G: only image tuples need separating coordinates. For example with all coordinates constant the two images are a point (or empty S-image), not the original nonmetrizable domains. An empty Y forces empty domain when f exists; the parent handles that. No new hypothesis was introduced into the item, no identification with the full products was made, and no limit in Y was substituted for an actual fibre value.

The single return point is repaired by two new independent unsplit nodes, and the parent proof is 2185 characters, below 3000; no parent step exceeds 2000. The detailed old proof is retained below as the work assignment for future workers, not placed in the new statement-only node files. There is no unfinished mathematical repair. The required dry run passed; its result is recorded below.

## Preserved proof and allocation to future workers

The following are the exact ten original proof steps, read from the current returned repository node before editing. Steps 2-4 belong to the finite-oscillation worker, except choosing the sequence which the parent now does; steps 5-7 belong to the coordinate-image worker. Steps 1 and 8-10 remain in the parent assembly. Existing citations inside the extracted arguments are guidance for those workers' later splits, not proof dependencies incorrectly added to an unsplit node.

### Original step 1

If $S=\varnothing$, take $S_0=\varnothing$ with its unique topology and empty metric, $G_0=\{1\}$ with its discrete group topology, and the unique maps $p,q,f_0$. These are continuous and $p,q$ are surjective, $q$ is a homomorphism, and the required identity has empty domain. Thus assume $S\ne\varnothing$ for the remaining steps.

Original uses: none.

### Original step 2

Write $D=S\times G^r$. It is compact by [lem-weil-pbc-tychonoff-product-quasi-compact], applied to its finitely many compact factors. Fix $\epsilon>0$. For each $x=(s,g_1,\ldots,g_r)\in D$, continuity gives a product neighbourhood mapping into $B_Y(f(x),\epsilon/3)$. Using the clopen basis of $S$ and the open-normal-subgroup basis of $G$, shrink it to a rectangle $U_x\times g_1H_x\times\cdots\times g_rH_x$, where $U_x$ is clopen and $H_x$ is open normal (intersect the finitely many subgroups chosen for the coordinates). Cosets are open; they are closed because their complements are unions of other open cosets. Any two values on this rectangle have distance less than $2\epsilon/3$, by the triangle inequality.

Original uses: lem-weil-pbc-tychonoff-product-quasi-compact.

### Original step 3

Choose finitely many such rectangles $R_j=U_j\times a_{j,1}H_j\times\cdots\times a_{j,r}H_j$ covering $D$, by compactness. Let $\mathcal P$ consist of the nonempty Boolean atoms of the finitely many clopens $U_j$: intersections choosing $U_j$ or its complement for every $j$. It is a finite clopen partition. Put $N=\bigcap_jH_j$, an open normal subgroup. If $s,s^\prime$ belong to the same atom and $g_iN=g_i^\prime N$ for every $i$, choose $R_j$ containing $(s,g_1,\ldots,g_r)$. The same atom lies in $U_j$, and $g_i^\prime=g_in_i$ for some $n_i\in N\subseteq H_j$. Thus $(s^\prime,g_1^\prime,\ldots,g_r^\prime)$ also lies in $R_j$, and the two $f$-values have distance less than $\epsilon$. This is the required uniform oscillation bound, directly from the finite cover.

Original uses: none.

### Original step 4

For every integer $n\geq0$, perform the preceding construction with $\epsilon_n=2^{-n}$, obtaining $\mathcal P_n,N_n$. Let $A_n$ be the finite discrete set of atoms of $\mathcal P_n$, and let $B_n=G/N_n$ with its discrete topology and quotient group law. The set $B_n$ is finite: its open cosets cover compact $G$, so a finite subcover includes every coset. The maps $p_n:S\to A_n$ and $q_n:G\to B_n$ are continuous surjections, since each point fibre is a clopen atom or open coset; $q_n$ is a homomorphism by normality. Their common product fibres satisfy the distance bound $d_Y(f(s,g),f(s^\prime,g^\prime))<2^{-n}$. Neither nesting the partitions nor completing $Y$ is needed.

Original uses: none.

### Original step 5

Define $P:S\to\prod_{n\geq0}A_n$ by $P(s)=(p_n(s))_n$, and $Q:G\to\prod_{n\geq0}B_n$ by $Q(g)=(q_n(g))_n$. Set $S_0=P(S)$ and $G_0=Q(G)$ with their subspace topologies [def-kun-subspace-topology], and corestrict $P,Q$ to surjections $p,q$. Preimages of basic cylinders are finite intersections of coordinate preimages, so $P,Q,p,q$ are continuous. By [lem-weil-pbc-continuous-image-quasi-compact], both images are compact. Each product, and each image, is Hausdorff: unequal tuples differ in a coordinate, whose disjoint singleton cylinders separate them. Basic cylinders specify finitely many coordinates and are clopen; their intersections with $S_0$ form a clopen basis. Consequently $S_0$ is profinite in exactly the sense of the statement.

Original uses: def-kun-subspace-topology, lem-weil-pbc-continuous-image-quasi-compact.

### Original step 6

The image $G_0$ is a subgroup of $\prod_nB_n$: $Q(gh)=Q(g)Q(h)$, $Q(g^{-1})=Q(g)^{-1}$, and $Q(1)=1$. Thus $q$ is a homomorphism. Componentwise multiplication and inversion on the product are continuous, since preimages of finite-coordinate cylinders are open, and their restrictions give continuous operations on $G_0$. For a finite set $F\subseteq\mathbf N$, put $K_F=\{b\in G_0:b_n=1\text{ for all }n\in F\}$. These are open normal subgroups, being finite intersections of coordinate kernels, and they form a neighbourhood basis of $1$: every basic cylinder neighbourhood of $1$ contains one of them. With compactness and Hausdorffness from the preceding step, this proves that $G_0$ is a profinite group under the definition in the item.

Original uses: none.

### Original step 7

Give each finite set $A_n,B_n$ its discrete metric, with distance $0$ on equal points and $1$ otherwise. The coordinate maps on $S_0$ and on $G_0$ are continuous and separate distinct tuples, and these two image spaces are compact. Apply [lem-sfb-compact-countable-separating-metrizable] to each of these two sequences of coordinate maps. It follows that both $S_0$ and $G_0$ are metrizable. No metric on the original $S$ or $G$ is assumed.

Original uses: lem-sfb-compact-countable-separating-metrizable.

### Original step 8

Let $R=p\times q^r:D\to S_0\times G_0^r$. If $R(s,g_1,\ldots,g_r)=R(s^\prime,g_1^\prime,\ldots,g_r^\prime)$, equality of every $n$th coordinate implies $p_n(s)=p_n(s^\prime)$ and $q_n(g_i)=q_n(g_i^\prime)$ for all $i$. Step 4 gives $d_Y(f(s,g),f(s^\prime,g^\prime))<2^{-n}$ for every $n$. Since $2^{-n}\to0$ and distances are nonnegative, this distance is zero, and the metric separation axiom gives equality of the two values. Hence $f$ is constant on each fibre of $R$.

Original uses: none.

### Original step 9

The map $R$ is continuous by its coordinate formula. It is surjective: for a point $(s_0,b_1,\ldots,b_r)$ choose a preimage of $s_0$ under $p$ and, independently, a preimage of each $b_i$ under $q$. Its domain $D$ is compact by step 2, and its codomain is Hausdorff by coordinate separation. Apply [lem-sfb-compact-hausdorff-surjection-quotient] (with the whole spaces as the two subsets): $R$ is a quotient map, so a subset $W$ of its codomain is open precisely when $R^{-1}(W)$ is open.

Original uses: lem-sfb-compact-hausdorff-surjection-quotient.

### Original step 10

Define $f_0(t)$ to be the common value of $f$ on the nonempty fibre $R^{-1}(t)$. Steps 8 and 9 make this well-defined and give $f=f_0\circ R$. For any open $V\subseteq Y$, one has $R^{-1}(f_0^{-1}(V))=f^{-1}(V)$, which is open. The quotient criterion in step 9 therefore makes $f_0^{-1}(V)$ open, proving continuity. The values are actual values of $f$ in $Y$, so this argument does not require completeness. Under [def-weil-size-convention], finite partitions, finite quotients, countable products and their image subsets remain in the chosen universe, as do the constructed maps. This supplies every required object and identity.

Original uses: def-weil-size-convention.

## Server validation

The repaired delivery passed the required `deliver.py Q101 lem-sfb-profinite-metric-function-quotients --no-push` on 2026-10-22: `OK (not pushed)` at edb8ecb6fbf, with server preflight passed. This includes the server DAG and split review checks. The final invocation builds and validates the delivery again before pushing.


## Landing-return repair by Q101 (2026-10-22)

The latest return is administrative: the reader approved the split, but landing found completion recorded only in the side project's DAG, not promoted to the live DAG. I compared the retained delivery with the current shared item and repair order. The released stage-1 order still requires two new nodes and a parent proof of at most 3000 characters. The current shared item still has the original ten-step proof. The retained delivery differs from that item only in proof, proof_deps and split_report; every other field, including the statement, statement dependencies, Lean record and independent review metadata, already agrees. Both extracted node ids remain absent from the shared DAG. The delivery tool rebases these sandbox files in its own worktree on the current server base.

I re-read the current statements of def-weil-size-convention, def-kun-subspace-topology, lem-weil-pbc-tychonoff-product-quasi-compact and lem-sfb-compact-hausdorff-surjection-quotient, together with both extracted statements. All five step/node quotation pairs in citations.json remain verbatim substrings of those current statements. Thus no dependency needs replacement or changed mathematical use: step 2 receives the common normal subgroup and finite continuous quotient maps; step 3 receives compact metrizable profinite images and coordinate equality; step 5 receives finite-product compactness and the quotient criterion with whole spaces as subsets; step 6 uses the existing universe convention. I also re-read the two historical citations for compact images and countable separating maps, since the archived original arguments assign them to the future coordinate-image worker. Their statements still give exactly these properties without surjectivity or completeness assumptions.

I checked the Stacks source at topology.tex labels theorem-tychonov, lemma-closed-map and lemma-closed-morphism-quotient-topology, and the current main-20261015 direct-image proof paragraph (3). The former justify the cited compactness and quotient-map statements; the latter remains only motivation for this agent-authored topological expansion. The project theorem in Sheaf/Topology/ProfiniteMetricFunctionQuotients.lean still ends in sorry, and the search of WeilConjectures finds no exact project attachment. No Lean file or compiler was used. I read and reused all retained search results rather than rerunning unchanged questions.

For the renewed B-E review, both new nodes remain self-contained statement-only obligations, with all old arguments preserved in this report. Neither repeats the parent factorization claim. The finite-oscillation lemma supplies genuinely rectangular quotients with a common normal subgroup; the coordinate-image lemma needs no jointly injective or surjective coordinates. Empty S, empty metric Y when a map exists, singleton coordinates, noncommutative G and incomplete Y still satisfy the arguments. No parent step exceeds 2000 characters and the assembly remains 2185 characters. The correction for this return is the freshly based delivery and explicit current-DAG review; the approved mathematical split is retained, with this repair recorded in split_report and report instead of an unchanged re-push.

The resumed initial dry run completed and wrote a fresh stage1-ready receipt for head 27e14dcbfcd. A new dry run is required after this report and split_report update; the final push will occur only after it exits successfully.


## Resumed landing-return audit by Q101 (2026-10-22)

The mandatory initial dry run of the retained split exited successfully with `OK (not pushed)` at `2a4508bc328`. I compared all retained parent fields with the current shared node: only `proof`, `proof_deps` and `split_report` differ. I reconstructed the parent from that current node and overlaid those three reviewed fields, retaining every current statement, definition dependency, blueprint field, Lean record and independent review record. Both new node ids remain absent from the current shared DAG. The delivery tool supplies the current server base; no repository git command is used.

I re-read the two new statements and all current parent citations. Step 2 has exactly the clopen-space, open-normal-group, continuity and finite-power hypotheses of the oscillation lemma. Step 3 applies the coordinate-image lemma to the resulting finite continuous coordinates and homomorphisms, without requiring joint injectivity. Step 5 uses product quasi-compactness and the compact-to-Hausdorff surjection criterion with whole spaces as subsets. Step 6 uses the actual universe convention. Every one of the five `(step, node)` pairs has a verbatim current-statement quotation in `citations.json`; there is no missing pair. The historical compact-image and countable-separating-metrizability citations were also re-read for the preserved future-worker arguments. None requires a change of hypotheses or use.

I checked the current main-20261015 paragraph (3), the chapter and unit records, Stacks `topology.tex` labels `theorem-tychonov`, `lemma-closed-map` and `lemma-closed-morphism-quotient-topology`, and the recorded Mathlib candidate types. The blueprint still only motivates this agent-authored auxiliary argument. The generic finite-approximation theorem does not give rectangular quotients or group homomorphisms, and the profinite product constructors do not assert the entire coordinate-image lemma. I read all retained search responses and reused them without repeating unchanged questions. Whole-blueprint metrizability and oscillation searches still find no matching blueprint node. The project Lean declaration still ends in `sorry`; no exact attachment appeared in the searched upstream project source.

For the renewed B-E review, neither new statement contains proof steps or proof dependencies, each introduces its objects, and neither states the parent's factorization. The full original ten-step argument remains preserved above and allocated between two independent future workers and the short assembly. The empty-space and empty-target cases, constant/nonseparating coordinates, noncommutative groups and incomplete metric targets still work. No statement correction, new route, source attribution or extra hypothesis is needed. This resumed repair records the fresh base and audit rather than sending an unchanged retained delivery. The final dry run must exit successfully before the push starts.
