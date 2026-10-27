# Repair report: Q124 / lem-sfb-finite-valued-cech-cocycle-descent

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-valued-cech-cocycle-descent.json`: statement unchanged; five-step assembly using two new independent lemmas.
- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-rectangular-extension.json`: statement, unsplit; no exact or one-line Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-profinite-defect-base-partition.json`: statement, unsplit; no exact or one-line Mathlib match.

## Attachments

None. I searched the project source for the blueprint tag, the declaration name, finite quotients, rectangular extensions and clopen partitions. The current `lean/Sheaf/Topology/FiniteValuedCechCocycleDescent.lean:80` states the item with `sorry`; there is no exact finished project declaration to attach. No Lean file was written and no compiler or Lake tool was run.

## WANTED

None. The auxiliaries are explicitly agent-formulated applications of the available Stacks topology material, not assertions attributed verbatim to a missing reference.

## What was wrong and what changed

The returned eight-step proof was mathematically correct, but at 4777 characters contained two independent compactness arguments for one worker. This is a substantive re-split in response to the 2026-10-21 human decision, not a shortened re-push. It adds two statement-only nodes with no proof steps, no proof dependencies and null proof origins, so other workers can split their proofs independently. Neither node states a clause of cocycle descent: the first is an extension theorem on an arbitrary closed subset of a finite product, with no base space, surjection or cocycle; the second controls an arbitrary discrete defect by a partition of the base, with no cochain, quotient arrow or cocycle hypothesis. The common quotient arrow, factorization and equation remain assembled in the parent.

The supplied sandbox initially contained only dispatcher markers, not the previous node files, report, citations or search log. I recovered the returned argument from the current read-only repository, retained its statement, source, inherited searches and metadata, and copied the full old proof below. `returned-node.json` in the sandbox is the unedited baseline. There were no earlier local search results to reuse. The delivery tool performs the required overlay onto current main and preserves maintainer-owned fields.

## Unfinished work

The two new nodes are intentionally unsplit for parallel future work. No requested repair point is left open. Verification and delivery results are recorded below after the required tools exit.

## Review by Q124

I read the current chapter record, the inherited unit record, and the current main-20261015 direct-images proof paragraph (3). Its open-coefficient branch delegates the theorem; this finite topological input is an agent auxiliary below that branch, not a theorem stated in the blueprint. The inherited ancestry command returns `blueprint.from.node = None`; I retained it and prefixed the item's id to the new nodes' `via` chains. Whole-blueprint searches for clopen, rectangular, finite quotient, extension and vanishes gave no statement of either proposed auxiliary. All files written are in this item's sandbox.

For the item and both new nodes I read `literature/stacks-project/topology.tex`, Tag 08ZY (`lemma-profinite`), including the inverse system of finite disjoint clopen partitions, and Tag 08ZZ (`lemma-profinite-refine-open-covering`), including its proof. These support the finite clopen arguments; the stronger auxiliary conclusions are agent-formulated and labelled as such. I also read Bhatt–Scholze Lemma 4.3.9(2) and its proof on printed page 33 in the available PDF: it says discrete modules have the required higher-direct-image vanishing, but does not spell out this finite Cech descent. I do not claim it directly states the auxiliaries. The parent's old source and agent proof origin are retained.

Step 1 cites the actual assertion “The space $P$ is compact Hausdorff and totally disconnected” in `lem-sfb-finite-quotient-fiber-product`, not its inverse-limit proof. Products use the point as base and fibre powers use the continuous coordinate map to S. The closedness assertion follows from finitely many preimages of the closed diagonal in Hausdorff S. All factor spaces meet that lemma's compact/Hausdorff/totally disconnected hypotheses. The existing off-unit tool declaration is retained.

Step 2 cites the full statement of `lem-sfb-profinite-rectangular-extension`: K is the closed fibre power P_k, the topology is its product subspace topology, M is finite discrete abelian and k=n+1 is positive. Its statement supplies both the continuous extension and a single partition of T controlling every coordinate, not merely an arbitrary partition of T^k. The old neighbourhood-rectangle selection and atom refinement are allocated to this node, with every line preserved in the archive below.

Step 3 defines the defect by the displayed alternating sum. Continuity of deletion maps and of a finite sum in a discrete group is immediate; each face of a fibre tuple is a fibre tuple, so its value is c and the given equation forces zero. The full statement of `lem-sfb-profinite-defect-base-partition` applies to r=k+1 and gives the required partition for all approximate equal-image tuples. Its hypotheses deliberately require no surjectivity, and the old compact defect locus and separating clopens are its independent argument. This citation is to the conclusion about arbitrary same-block tuples, not to an unrecorded construction in a proof.

Step 4 is finite-partition algebra from the previously supplied alpha and gamma. The nonempty intersections are disjoint clopens and cover T. Point-to-block maps are continuous because singleton preimages are open blocks; all block sets are finite and discrete. Surjectivity of q is used exactly to prove q_0 surjective, by choosing s in a gamma-block and a lift t. No assumption about lifting tuples is used.

Step 5 descends h along the refinement beta and restricts to equal-q_0-image tuples. The displayed factorization follows from h|P_k=c. For the quotient cocycle equation each block has a representative, and their base images are in the same gamma-block. That is exactly what step 3 guarantees, even when those base images differ. Every face value is identified by the definition of h_0, so the alternating sum is literally the zero value e(t). This retains the most important clause of the item on nonliftable quotient tuples. These final two steps are elementary assembly and cite no additional theorem. `citations.json` contains a verbatim statement quote for every cited node in steps 1–3.

I checked B1–B9: both new files introduce every object and hypothesis, spell out clopen partitions and empty partitions, contain no proof sketches in their statements, have empty proof/proof_deps, and have source tags/labels and precise blueprint provenance. The Mathlib search records are copied from actual msearch log entries, with unchanged tool/query text. I read the returned hits, including `Profinite.exists_locallyConstant_finite_aux`, `Profinite.NobelingProof.fin_comap_jointlySurjective`, `ContinuousMap.exists_disjoint_nonempty_clopen_cover_of_mem_nhds_diagonal` and `DiscreteQuotient.exists_of_compat`; I inspected the local CofilteredLimit, Extend, ClopenBox and DisjointCover source statements. Supplied-limit factorization does not produce the new common-coordinate partition and extension, and finite covers on T^r do not provide a partition of S that kills the defect. These are not one-line specializations. Rephrasings in LeanSearch and second Loogle/grep queries were actually executed and read. No new Mathlib leaf is claimed.

For E1–E7 I checked the small cases. In the extension lemma T empty with k>0 forces K empty and the empty partition suffices; K empty in nonempty T permits alpha={T} and h=0. At k=1 the same rectangular argument is valid. The zero group has h=0 on every cell. In the defect lemma r=1 makes P_1=T and hence e=0 everywhere, so {S} works for nonempty S; S empty forces T empty whenever q exists. A non-surjective q causes no problem because only a partition of S is needed, not surjectivity of any block map. For M=0 the bad locus is empty and the one-block partition works. If e is already zero, the construction uses the empty separating family. For a finite surjection with two different fibres, a coarse gamma may produce quotient tuples with no equal-base-image representatives: e=0 on the whole product (e.g. h a global coboundary) still makes the quotient equation valid. Conversely a nonzero defect at a mixed-fibre tuple forces a separation of its distinct base points; this is why merely factoring c without checking its equation would be insufficient. The parent separately handles S empty and assumes no false surjectivity of fibre-power maps. All parent steps are below 2000 characters, and the whole assembly is below 3000 characters.

No statement dispute or source error was found. The requested correction is exactly the distribution of the two compactness arguments to separate future workers. Every old argument is retained in its allocation below and verbatim in the archive. I made no change to target statements, definitions, chapter/unit records or Lean metadata.

## Current return repaired (2026-10-22)

The latest return is L's 06:42 UTC landing refusal at returned branch head `57314b8c49d`: the side completion had not been promoted to the live DAG. I retained the previously reviewed five-step proof, both auxiliary statements, citations, logged searches, and archived eight-step argument. I compared `returned-node.json` field by field with the current repository item: they are identical, so no current main statement or metadata change needs to be overridden. The sandbox split changes only the split-owned proof, proof dependencies and split report against that baseline. The delivery command rebuilds the delivery on current main; I made no git invocation in the read-only repository.

I re-read all three proof dependencies in their current versions: the fibre-product lemma still explicitly supplies compact Hausdorff totally disconnected fibre products; the rectangular-extension statement supplies a single common coordinate partition and an extension; the defect-partition statement forces vanishing for all tuples in one base block. The quotes in `citations.json` remain verbatim. I also re-read both statement dependencies, the size convention and set Cech nerve, and checked the current Lean declaration, which still has `sorry`. Thus no new attachment or change of proof route is warranted.

The first required dry run exited 1 on a new same-tag collision, with `lem-sfb-profinite-clopen-pullback-bijective-open`. I opened its full statement and source: its bijective-clopen-pullback hypothesis and bijective/open-map conclusions cannot supply either auxiliary. The two explicit pairwise comparisons under `## Not duplicates` repair this diagnostic. This is a changed delivery report, not an unchanged re-push. I re-read Stacks topology.tex Tags 08ZY and 08ZZ, the retained search log, and the released stage-1 repair order: the two independent statement-only auxiliaries and the short parent assembly still satisfy that order. Empty spaces, k=1, r=1, zero coefficients, and nonliftable quotient tuples pass the same checks recorded above. No statement correction is needed.

## Allocation of every old argument

- Old step 1: empty-space case, product/fibre-power compactness, tuple identifications and continuous coordinate deletions remain in parent steps 1 and 3.
- Old step 2: continuous discrete-valued local constancy, ambient open neighbourhoods, coordinate rectangles, clopen refinement and finite compact subcover belong to `lem-sfb-profinite-rectangular-extension`.
- Old step 3: nonempty atoms of coordinate clopens, containment of a whole atom product in a selected rectangle, constancy on its intersection with K, extension by zero on disjoint cells and continuity of h belong to that same extension node. Its statement explicitly requires a common coordinate partition and zero on disjoint cells.
- Old step 4: definition and continuity of e and its vanishing on the fibre power remain in parent step 3. The nonzero locus being clopen/compact and disjoint from the equal-image locus belongs to `lem-sfb-profinite-defect-base-partition`.
- Old step 5: distinguish two unequal q-images, separate by a base clopen, form W_t, take a finite subcover of the defect locus, take atoms gamma, and prove vanishing on every same-gamma-block tuple belong to that defect-partition node.
- Old step 6: refine alpha by inverse images of gamma, discard empty intersections, define continuous block surjections a,b and q_0, verify commutation and use q surjective to prove q_0 surjective remain in parent step 4.
- Old step 7: constancy after refinement, definition of h_0 and restriction c_0, membership of the image tuple and its factorization equation remain in parent step 5.
- Old step 8: independent representatives, common gamma-block, term-by-term identification of the alternating sum, absence of any equal-base-image lifting assertion, and the zero-group case remain in parent step 5. The empty-defect case is also part of the second node's edge-case check.

## Not duplicates

- lem-sfb-profinite-rectangular-extension vs lem-sfb-profinite-clopen-pullback-bijective-open: the existing lemma assumes a continuous map induces a bijection on clopens and proves that map is bijective and open; it gives no extension of a finite-valued map from a closed product subspace or common coordinate partition.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-profinite-clopen-pullback-bijective-open: the existing lemma assumes bijective clopen pullback and concludes bijectivity and openness; the new lemma assumes an arbitrary continuous map and a function vanishing on its fibre power, and produces a base partition forcing vanishing on approximate fibre tuples. Neither the hypotheses nor the conclusions specialize to the other.

- lem-sfb-profinite-rectangular-extension vs def-sfb-invariant-discrete-quotients: defines group-invariant discrete quotients and their canonical diagram, with no theorem about extending functions or killing defects.
- lem-sfb-profinite-rectangular-extension vs def-sfb-profinite-cech-tuples: only defines equal-image tuple spaces and faces, with no extension or finite vanishing assertion.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-compact-discrete-quotient-realization: realizes compatible choices of points in all discrete quotients; it constructs neither a rectangular extension nor a defect-killing base partition.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-finite-quotient-fiber-product: states topology and a compatible-partition inverse-limit description of binary fibre products, with no extension of functions or vanishing of a defect on approximate tuples.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-finite-valued-cech-cocycle-descent: asserts finite Cech cocycle descent along a surjection; the extension lemma has no base map or cocycle and the defect lemma has an arbitrary defect but no descended cochain or quotient surjection.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-integers-profinite-tower: concerns the specific adic quotient tower of the integers of a finite local field, not arbitrary profinite spaces and closed product subspaces or defects.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-profinite-action-finite-quotients: produces invariant refinements for a group action and their inverse limit; it imposes neither product-cell extension nor same-base-block vanishing.
- lem-sfb-profinite-rectangular-extension vs lem-sfb-spectral-clopen-component-homeomorphism: identifies connected-component spaces of a spectral map with bijective clopen pullback, not either new auxiliary.
- lem-sfb-profinite-rectangular-extension vs lem-weil-pbc-profinite-clopen-basis: provides one clopen neighbourhood inside an open neighbourhood, not the finite rectangular extension or compact defect separation theorem.
- lem-sfb-profinite-rectangular-extension vs lem-weil-pbc-profinite-limit-function-factorization: factors a locally constant function on an already supplied cofiltered limit; it does not construct an extension on a product or ensure that a finite base quotient kills all defects.
- lem-sfb-profinite-defect-base-partition vs def-sfb-invariant-discrete-quotients: defines group-invariant discrete quotients and their canonical diagram, with no theorem about extending functions or killing defects.
- lem-sfb-profinite-defect-base-partition vs def-sfb-profinite-cech-tuples: only defines equal-image tuple spaces and faces, with no extension or finite vanishing assertion.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-compact-discrete-quotient-realization: realizes compatible choices of points in all discrete quotients; it constructs neither a rectangular extension nor a defect-killing base partition.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-finite-quotient-fiber-product: states topology and a compatible-partition inverse-limit description of binary fibre products, with no extension of functions or vanishing of a defect on approximate tuples.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-finite-valued-cech-cocycle-descent: asserts finite Cech cocycle descent along a surjection; the extension lemma has no base map or cocycle and the defect lemma has an arbitrary defect but no descended cochain or quotient surjection.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-integers-profinite-tower: concerns the specific adic quotient tower of the integers of a finite local field, not arbitrary profinite spaces and closed product subspaces or defects.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-profinite-action-finite-quotients: produces invariant refinements for a group action and their inverse limit; it imposes neither product-cell extension nor same-base-block vanishing.
- lem-sfb-profinite-defect-base-partition vs lem-sfb-spectral-clopen-component-homeomorphism: identifies connected-component spaces of a spectral map with bijective clopen pullback, not either new auxiliary.
- lem-sfb-profinite-defect-base-partition vs lem-weil-pbc-profinite-clopen-basis: provides one clopen neighbourhood inside an open neighbourhood, not the finite rectangular extension or compact defect separation theorem.
- lem-sfb-profinite-defect-base-partition vs lem-weil-pbc-profinite-limit-function-factorization: factors a locally constant function on an already supplied cofiltered limit; it does not construct an extension on a product or ensure that a finite base quotient kills all defects.

Whole-DAG concept searches additionally found `lem-sfb-profinite-metric-function-quotients` (metrizable reductions of maps S times group powers), `lem-sfb-homogeneous-cocycle-rectangle-detection` (equivariant group cocycles), and `lem-sfb-prime-to-ell-cochain-finite-quotient-descent` (quasi-isomorphism of group-cochain sheaf complexes). Their full statements were read; none asserts either new finite topological lemma. The two new nodes are also distinct from each other: extension from a closed product subspace versus forcing vanishing after partitioning a base. Neither depends on the parent or on the other.

## Returned proof preserved verbatim

The following is an archival allocation record for future workers, not proof steps in either new unsplit node.

### Old step 1

If $S=\varnothing$, the map $q$ forces $T=\varnothing$. Take $T_0=S_0=\varnothing$ and the unique maps and function. All assertions are vacuous since every tuple length is positive. Henceforth $S$ and $T$ are nonempty. Put $k=n+1$. Repeated application of [lem-sfb-finite-quotient-fiber-product] gives compact Hausdorff totally disconnected spaces $T^r$ and $P_r=T_S^r$ for every $r\geq1$: use the base point to form ordinary products, and use $P_{r+1}=P_r\times_S T$ for the fibre powers, starting with $P_1=T$. The identifications with tuple subspaces and the maps to $S$ are given by the coordinates. In particular $P_k$ is compact and coordinate-deletion maps are continuous.

### Old step 2

For each $z\in P_k$, continuity of $c$ into discrete $M$ gives an open neighbourhood $O_z$ of $z$ in $T^k$ such that $c=c(z)$ on $O_z\cap P_k$. By the finite-product topology choose a rectangle around $z$ inside $O_z$. Apply [lem-weil-pbc-profinite-clopen-basis] in $T$ to each coordinate neighbourhood to obtain a clopen rectangle $R_z=\prod_{i=0}^{k-1}U_{z,i}$ around $z$ with $R_z\subseteq O_z$. Compactness of $P_k$ selects finitely many $R_1,\ldots,R_N$ covering it; $c$ is constant on each $R_l\cap P_k$.

### Old step 3

Let $\alpha$ consist of the nonempty atoms of the finite family of clopens $U_{l,i}$ in $T$: an atom is an intersection choosing each $U_{l,i}$ or its complement. Thus $\alpha$ is a finite partition into nonempty clopens. For any $k$-tuple of its blocks $A_0,\ldots,A_{k-1}$ whose product meets $P_k$, choose a point $z$ of that intersection and an $R_l$ containing $z$. Membership in every $U_{l,i}$ is constant on $A_i$, so $\prod_iA_i\subseteq R_l$. Consequently $c$ is constant on $(\prod_iA_i)\cap P_k$. Define $h:T^k\to M$ to have this constant value on $\prod_iA_i$ if the intersection is nonempty, and value $0$ otherwise. This is well-defined, agrees with $c$ on $P_k$, and is continuous: each fibre is a union of the finitely many clopen product cells.

### Old step 4

Define the continuous function $e:T^{k+1}\to M$ by
$$e(t_0,\ldots,t_k)=\sum_{j=0}^k(-1)^j h(t_0,\ldots,\widehat{t_j},\ldots,t_k).$$
Continuity follows because coordinate deletions are continuous and finite sums in discrete $M$ are continuous. Its nonzero locus $D=e^{-1}(M\setminus\{0\})$ is clopen, hence compact as a closed subset of compact $T^{k+1}$. Every face of a tuple in $P_{k+1}$ belongs to $P_k$, where $h=c$; the assumed equation therefore gives $e|_{P_{k+1}}=0$. Thus for each $t\in D$ there are indices $i,j$ with $q(t_i)\ne q(t_j)$.

### Old step 5

For each $t\in D$ choose such $i,j$. Hausdorffness makes $S\setminus\{q(t_j)\}$ an open neighbourhood of $q(t_i)$. Apply [lem-weil-pbc-profinite-clopen-basis] in $S$ to choose a clopen $V_t$ containing $q(t_i)$ and excluding $q(t_j)$. The open set
$$W_t=\{u\in T^{k+1}:q(u_i)\in V_t,\ q(u_j)\notin V_t\}$$
contains $t$. Compactness of $D$ selects finitely many $W_t$ covering $D$. Let $\gamma$ be the partition of $S$ into the nonempty atoms of their finitely many clopens $V_t$ (the partition $\{S\}$ when the family is empty). A tuple $u$ whose $q(u_i)$ all lie in the same $\gamma$-block belongs to none of these $W_t$: membership in each selected $V_t$ is constant on a block. Hence such a tuple lies outside $D$, and $e(u)=0$.

### Old step 6

Refine $\alpha$ to the finite clopen partition
$$\beta=\{A\cap q^{-1}(B): A\in\alpha,\ B\in\gamma,\ A\cap q^{-1}(B)\ne\varnothing\}.$$
Let $T_0=\beta$, $S_0=\gamma$, and let $a,b$ send a point to its block. The maps are continuous surjections because the blocks are open and nonempty. Define $q_0(C)=B$ for the unique $B\in\gamma$ with $C\subseteq q^{-1}(B)$. This is well-defined and $q_0a=bq$. Given $B\in\gamma$, choose $s\in B$ and then $t$ with $q(t)=s$; its $\beta$-block maps to $B$. Thus $q_0$ is surjective.

### Old step 7

Because $\beta$ refines $\alpha$, the function $h$ is constant on each product of $k$ blocks of $\beta$. Write $h_0:T_0^k\to M$ for the corresponding function and restrict it to $c_0:(T_0)_{S_0}^k\to M$. For $(t_0,\ldots,t_{k-1})\in P_k$, compatibility $q_0a=bq$ places its block tuple in this domain, and
$$c_0(a(t_0),\ldots,a(t_{k-1}))=h(t_0,\ldots,t_{k-1})=c(t_0,\ldots,t_{k-1}).$$

### Old step 8

For any $(x_0,\ldots,x_k)\in(T_0)_{S_0}^{k+1}$, independently choose representatives $t_i\in x_i$. Their $q$-images lie in the single $\gamma$-block $q_0(x_i)$, so step 5 gives $e(t_0,\ldots,t_k)=0$. Each face of the block tuple belongs to $(T_0)_{S_0}^k$ and the definition of $h_0$ gives
$$\sum_{j=0}^k(-1)^j c_0(x_0,\ldots,\widehat{x_j},\ldots,x_k)=\sum_{j=0}^k(-1)^j h(t_0,\ldots,\widehat{t_j},\ldots,t_k)=e(t_0,\ldots,t_k)=0.$$
The representatives need not have equal $q$-images. This verifies the equation even on block tuples with no lift to $P_{k+1}$. When $M$ is the zero group, $h=e=0$, $D=\varnothing$, and the same construction applies.

