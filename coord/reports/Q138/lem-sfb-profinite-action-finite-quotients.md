# Q138 stage-1 repair: lem-sfb-profinite-action-finite-quotients

## Files written

- Item: unchanged statement; four-step assembly (1789 characters).
- dag/nodes/sec-six-functors-basics/lem-sfb-action-clopen-orbit-refinement.json: statement; unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-invariant-partition-quotient-system.json: statement; unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-cofinal-clopen-partition-reconstruction.json: statement; unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-action-compatible-limit.json: statement; unsplit; no exact or one-line Mathlib match.

## Attachments

None. The project WeilConjectures source has no declaration of the whole item. `profiniteAction_finite_quotients` in lean/Sheaf/Topology/ProfiniteActionFiniteQuotients.lean is still `sorry`, so it is not an attachment. The invariant Galois scheme partition theorem has different objects and hypotheses.

## WANTED

None for the repair. Bhatt–Scholze Example 4.1.10, p. 28, and Stacks topology.tex are available and read. The equivariant details are explicitly agent expansions of that example, as in the returned version.

## Return repaired

The only numbered/content point is mandatory re-splitting of the 7840-character parent proof. The sandbox contained no node or report on arrival, only dispatcher marker files. I recovered the returned ten steps from the live read-only node; its lengths agree exactly with the return entry. I preserved every field outside proof, proof_deps and split_report. In particular the statement, Lean record, previous searches, provenance and audit fields remain unchanged. Four new nodes distribute the old argument in blocks of 1854, 1621, 2106 and 2259 characters. Each is statement-only, status unsplit, with empty proof/proof_deps and null proof_origin. The full argument for each future worker is preserved below, verbatim from the returned parent; it is not hidden in the new statement or discarded.

The first lemma needs no Hausdorffness or total disconnectedness of P, only compactness; it retains the stronger finite-orbit and blockwise-open-normal-subgroup assertions the proof established. The second works for any topological G and compact P, independently of the first. The third works for any cofinal directed family of partitions without a group. The fourth works for any topological G and even a non-directed nonempty poset. These are separate reusable arguments, not one renamed copy of the parent or a collection of its whole-statement restatements.

## Unfinished work

The four new lemmas intentionally await independent stage-1 workers. No source error or parent statement dispute found. Required server checks and delivery results are recorded at the end.

## Review by Q138

I read Bhatt–Scholze Example 4.1.10 on printed p. 28 (the identification of finite-G-set pro-objects with profinite continuous actions), and the adjacent Example 4.1.12, which illustrates the danger of dropping compactness of the acting group. I read Stacks topology.tex labels lemma-profinite (08ZY), theorem-tychonov (08ZU), lemma-inverse-limit-quasi-compact (08ZV), and lemma-describe-limits (0A2P). The former steps and the Lean docstring agree clause by clause with the unchanged item. The current blueprint's chapter record and sk-thm-sf-ctf-stability unit record were read; this is a generic topological input below the field-site argument, not a replacement of a unit-level route. No SGA source is used.

Step 1 cites the orbit-refinement node's actual conclusion that its translated common refinement is finite, clopen, invariant and finer; the statement explicitly quantifies over exactly the profinite group and compact action hypotheses available. Its additional open-normal-subgroup and finite-translate clauses retain old arguments 1–2. Step 2 cites the quotient-system node for smallness, directedness, surjectivity, continuity and equivariance; all of these are explicit clauses of its statement. The definition node is cited only to identify the invariant-quotient diagram, not to prove continuity. I read that definition: it is an equivalence relation with open classes stable under G and the containing-class functor. The finer-is-smaller convention there is opposite to the coarse-is-smaller order J used in prose, exactly as the new statement specifies.

Step 3 cites the reconstruction node only after checking the two nontrivial hypotheses: step 1 gives cofinality among every finite clopen partition, and step 2 gives nonempty directed J. Compactness, Hausdorffness and total disconnectedness come from the original P. The cited statement specifies the same compatible blocks, transitions and topology, and even identifies the inverse as the unique intersection point. It carries the old separation, finite-intersection and compact-to-Hausdorff homeomorphism arguments, rather than assuming them in the parent. Step 4 cites the compatible-limit node with the finite jointly continuous actions and equivariant inverse-system maps supplied in step 2, and then with the system given in the converse. Its conclusion explicitly includes joint continuity, not merely continuity for each fixed group element. The only remaining computation is coordinate equality q_i(gx)=gq_i(x), provided by step 2. All citation quotes in citations.json are exact statement substrings.

For the new statements I checked B1–B10 and C1–C8 against the files: objects and partition/limit topologies are defined inline; all four cite the size convention, and the quotient-system node also cites the existing invariant-quotient definition. They have no proof sketch in the statement. I searched every DAG chapter by tags 08ZY/08ZV/08ZU/0A2P and invariant/clopen/partition/compatible-family vocabulary, searched the entire imported blueprint via blueprint_refs.py (clopen, profinite, invariant, inverse limit, clopen partition, finite discrete, coordinatewise), and read the closest actual statements listed below. The new ids did not exist. The ancestor command returns None; each new node retains null from.node and prepends this item to its inherited via chain, with a precise old-step/source location. No other Lean declaration supplies these complete statements. I did not run a compiler or edit Lean.

For Mathlib I used only msearch.py; each new node has LeanFinder with two distinct phrasings, Loogle, grep and an attempted LeanSearch. LeanSearch returned rate-limit errors and is recorded unavailable. I read the returned candidate declarations Profinite.asLimit, isoAsLimitConeLift, DiscreteQuotient.exists_of_compat and ofLE, and PreGaloisCategory.has_decomp_quotients. The first three reconstruct from all discrete quotients, not an arbitrary cofinal family; the invariant action descent is not ofLE alone. Group-valued limit results do not cover arbitrary G-sets, especially empty ones. Thus no new node is marked Mathlib. The exact results/digests in searches.jsonl are retained and copied into each corresponding node's records.

The edge checks are mathematical: for empty P, alpha and beta are empty and N=G works; J has exactly the empty partition, all quotients and its limit are empty and all surjectivity statements are vacuous. For a singleton or trivial action the trivial partition and ordinary partitions behave as claimed. The reconstruction node assumes J nonempty, crucial when P is empty; directedness makes every finite set of chosen blocks have a common subordinate block. For nonempty P, nonempty blocks are essential for that compactness argument. In the inverse-limit lemma finite discrete factors may be empty; then T and Q are empty, closed and compact. Non-surjective transitions can give empty limits, which are allowed; no point or surjectivity was used. With incomparable indices the equations still define a closed subspace and coordinate cylinders still prove joint continuity, so the stronger non-directed-poset version is valid. Each parent step is below 2000 characters (indeed below 800); no long inline argument remains. The old arguments are preserved, with allocation and source cautions below.

## Not duplicates

lem-sfb-invariant-partition-quotient-system vs lem-sfb-profinite-action-finite-quotients: the new node works for any topological group and any compact action space, without total disconnectedness, Hausdorffness of P or a profinite G; it proves the quotient-system argument only and assumes no cofinality. Extracting old steps 3–4 as a statement-only independent work item is explicitly required by the human work-spreading return. It neither asserts nor depends on the parent's refinement or reconstruction theorem.

lem-sfb-finite-action-compatible-limit vs lem-sfb-profinite-action-finite-quotients: the new node permits every topological group and every small nonempty poset, including non-directed ones; it additionally states closedness of the compatibility locus. It extracts old steps 8–10 as the separate limit-construction argument required by the human work-spreading return, independent of invariant partitions and the forward reconstruction. The four new nodes have comparable underlying arguments; none replaces the whole parent.

lem-sfb-invariant-partition-quotient-system vs lem-sfb-compact-discrete-quotient-realization: the existing node realizes compatible classes over ALL discrete quotients; the new lemma concerns the indicated invariant system or arbitrary cofinal directed partition family, including topology or actions.

lem-sfb-invariant-partition-quotient-system vs lem-sfb-finite-quotient-fiber-product: the existing node reconstructs a particular fibre product using partition triples for two maps; the new lemma states the different generic partition/action assertion above.

lem-sfb-invariant-partition-quotient-system vs lem-sfb-integers-profinite-tower: the existing statement is Let $\ell$ be a prime and $E/\mathbf Q_\ell$ a finite extension, with its extending absolute value $|\cdot|_E$, ring of integers $\cO_E=\{x\in E:|x|_E\le1\}$, uniformizer $\pi_E$, ; it does not assert the new generic continuous finite quotient system of invariant partitions.

lem-sfb-invariant-partition-quotient-system vs lem-weil-pbc-profinite-limit-function-factorization: the existing statement is Use the universes of [def-weil-size-convention]. Let $J$ be a small cofiltered category, let $F:J\to\mathbf{Prof}$ be a diagram of compact Hausdorff totally disconnected spaces and; it does not assert the new generic continuous finite quotient system of invariant partitions.

lem-sfb-invariant-partition-quotient-system vs def-sfb-invariant-discrete-quotients: the existing node defines invariant relations and a diagram; the new lemma proves the explicitly stated topological or reconstruction properties.

lem-sfb-invariant-partition-quotient-system vs def-sfb-profinite-cech-tuples: the existing statement is Let $T,V$ be profinite sets, meaning compact Hausdorff totally disconnected topological spaces, and let $q:T\to V$ be any continuous map. For each integer $r\geq0$, define the equa; it does not assert the new generic continuous finite quotient system of invariant partitions.

lem-sfb-invariant-partition-quotient-system vs lem-sfb-finite-valued-cech-cocycle-descent: the existing statement is Use the universes of [def-weil-size-convention]. Let $q:T\to S$ be a continuous surjection of compact Hausdorff totally disconnected spaces, and let $M$ be a finite abelian group w; it does not assert the new generic continuous finite quotient system of invariant partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-compact-discrete-quotient-realization: the existing node realizes compatible classes over ALL discrete quotients; the new lemma concerns the indicated invariant system or arbitrary cofinal directed partition family, including topology or actions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-finite-quotient-fiber-product: the existing node reconstructs a particular fibre product using partition triples for two maps; the new lemma states the different generic partition/action assertion above.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-integers-profinite-tower: the existing statement is Let $\ell$ be a prime and $E/\mathbf Q_\ell$ a finite extension, with its extending absolute value $|\cdot|_E$, ring of integers $\cO_E=\{x\in E:|x|_E\le1\}$, uniformizer $\pi_E$, ; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-weil-pbc-compact-hausdorff-bijection: the existing statement is Let $X,Y$ be topological spaces and $U\subseteq X$, $V\subseteq Y$ subsets, endowed with their subspace topologies [def-kun-subspace-topology]. If $U$ is quasi-compact and $V$ is H; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-weil-pbc-profinite-limit-function-factorization: the existing statement is Use the universes of [def-weil-size-convention]. Let $J$ be a small cofiltered category, let $F:J\to\mathbf{Prof}$ be a diagram of compact Hausdorff totally disconnected spaces and; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs def-sfb-invariant-discrete-quotients: the existing node defines invariant relations and a diagram; the new lemma proves the explicitly stated topological or reconstruction properties.

lem-sfb-cofinal-clopen-partition-reconstruction vs def-sfb-profinite-cech-tuples: the existing statement is Let $T,V$ be profinite sets, meaning compact Hausdorff totally disconnected topological spaces, and let $q:T\to V$ be any continuous map. For each integer $r\geq0$, define the equa; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-compact-closed-finite-intersection: the existing statement is Place sets and index families in compatible universes as in [def-weil-size-convention]. Let $X$ be a topological space such that every open covering of $X$ admits a finite subcover; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-finite-valued-cech-cocycle-descent: the existing statement is Use the universes of [def-weil-size-convention]. Let $q:T\to S$ be a continuous surjection of compact Hausdorff totally disconnected spaces, and let $M$ be a finite abelian group w; it does not assert the new generic reconstruction from a cofinal family of finite clopen partitions.

lem-sfb-finite-action-compatible-limit vs lem-sfb-compact-discrete-quotient-realization: the existing node realizes compatible classes over ALL discrete quotients; the new lemma concerns the indicated invariant system or arbitrary cofinal directed partition family, including topology or actions.

lem-sfb-finite-action-compatible-limit vs lem-sfb-finite-quotient-fiber-product: the existing node reconstructs a particular fibre product using partition triples for two maps; the new lemma states the different generic partition/action assertion above.

lem-sfb-finite-action-compatible-limit vs lem-sfb-integers-profinite-tower: the existing statement is Let $\ell$ be a prime and $E/\mathbf Q_\ell$ a finite extension, with its extending absolute value $|\cdot|_E$, ring of integers $\cO_E=\{x\in E:|x|_E\le1\}$, uniformizer $\pi_E$, ; it does not assert the new generic compact compatible-family limits of finite continuous actions.

lem-sfb-finite-action-compatible-limit vs lem-weil-pbc-profinite-limit-function-factorization: the existing statement is Use the universes of [def-weil-size-convention]. Let $J$ be a small cofiltered category, let $F:J\to\mathbf{Prof}$ be a diagram of compact Hausdorff totally disconnected spaces and; it does not assert the new generic compact compatible-family limits of finite continuous actions.

lem-sfb-finite-action-compatible-limit vs lem-weil-pbc-spectral-limit-constructible-closed-quasi-compact: the existing statement is Let $(I,\le)$ be a preordered set (a set with a reflexive and transitive relation $\le$; no directedness is assumed), let $(X_i)_{i\in I}$ be spectral spaces [def-weil-spectral-spa; it does not assert the new generic compact compatible-family limits of finite continuous actions.

lem-sfb-finite-action-compatible-limit vs lem-weil-pbc-tychonoff-product-quasi-compact: the existing node proves compactness of products only; the new lemma additionally proves closedness of compatibility, separation and continuous induced actions.

lem-sfb-finite-action-compatible-limit vs def-sfb-invariant-discrete-quotients: the existing node defines invariant relations and a diagram; the new lemma proves the explicitly stated topological or reconstruction properties.

lem-sfb-finite-action-compatible-limit vs def-sfb-profinite-cech-tuples: the existing statement is Let $T,V$ be profinite sets, meaning compact Hausdorff totally disconnected topological spaces, and let $q:T\to V$ be any continuous map. For each integer $r\geq0$, define the equa; it does not assert the new generic compact compatible-family limits of finite continuous actions.

lem-sfb-finite-action-compatible-limit vs lem-sfb-finite-valued-cech-cocycle-descent: the existing statement is Use the universes of [def-weil-size-convention]. Let $q:T\to S$ be a continuous surjection of compact Hausdorff totally disconnected spaces, and let $M$ be a finite abelian group w; it does not assert the new generic compact compatible-family limits of finite continuous actions.

lem-sfb-action-clopen-orbit-refinement vs lem-weil-pbc-galois-finite-invariant-clopen-partition: the existing lemma concerns Galois base changes of schemes and a finite intermediate field stabilizing a nontrivial clopen; the new lemma concerns every partition of any compact continuous profinite-group space and its entire finite translate orbit.

lem-sfb-finite-action-compatible-limit vs lem-dl-a1-finite-group-limit-profinite: the existing node concerns diagrams of finite groups with homomorphisms and topological group structure; the new node concerns arbitrary finite continuous G-sets, which can be empty and need no group operations.

lem-sfb-cofinal-clopen-partition-reconstruction vs lem-sfb-profinite-action-finite-quotients: this auxiliary assertion has no group and assumes a supplied cofinal directed family; it carries only the underlying reconstruction argument. The parent must still produce that family, continuous quotient actions and the converse.

## Full retained arguments and allocation to future workers

These are the old parent proof steps, copied verbatim. They are handoff material, not proof steps of the new unsplit nodes. References to old step numbers mean the ten original steps. For reconstruction generalize the supplied invariant family to a given cofinal directed family: use its cofinality instead of old steps 1–2; use the existing clopen-basis and compact-Hausdorff-bijection leaves cited here. For compatible limits, the proof uses no directedness, so applies to the newly stated non-directed poset. For the quotient-system node the whole argument uses only compactness of P and continuity of the group action.

### lem-sfb-action-clopen-orbit-refinement

Old step 1 (977 characters). Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Agent expansion of the compact-action refinement implicit in Bhatt–Scholze Example 4.1.10, p. 28.

First suppose $P$ is empty. Its sole finite clopen partition is empty, its quotient set is empty, and its inverse system has one object and empty limit; all forward assertions hold. For the forward argument below assume $P\ne\varnothing$. Fix a finite clopen partition $\alpha$. For each $x\in P$ let $A_x\in\alpha$ contain $x$. Continuity of the action at $(1,x)$ gives open neighbourhoods $V_x$ of $1$ and $W_x$ of $x$, shrinking $W_x$ inside $A_x$, such that $V_xW_x\subseteq A_x$. Choose finitely many $W_{x_1},\ldots,W_{x_r}$ covering $P$ by compactness. Set $V=\bigcap_tV_{x_t}$. If $v\in V$ and $y\in A\in\alpha$, choose $t$ with $y\in W_{x_t}$. Then $A=A_{x_t}$ and $vy\in A$, so $vA\subseteq A$ for every block. By the assumed neighbourhood basis choose an open normal subgroup $N\subseteq V$. For $n\in N$, both $nA\subseteq A$ and $n^{-1}A\subseteq A$ hold, hence $nA=A$. This proves uniform block preservation directly from the open-cover definition of compactness.

Old step 2 (877 characters). Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Agent expansion of the compact-action refinement implicit in Example 4.1.10, p. 28.

The open left cosets $gN$ cover compact $G$, so finitely many $g_1N,\ldots,g_sN$ cover it. If $g=g_tn$ with $n\in N$, then $gA=g_tA$ for each $A\in\alpha$. Consequently the family $\mathcal T=\{g\alpha:g\in G\}$ of translated partitions is finite and contains $\alpha$. Take their common refinement $\beta$: its blocks are the nonempty intersections obtained by choosing one block of each partition in $\mathcal T$. These intersections are clopen, disjoint, cover $P$, and form a finite collection. Every $h\in G$ sends the family $\mathcal T$ bijectively to itself, so it permutes the intersection blocks. Thus $\beta$ is $G$-invariant and refines $\alpha$. Translations preserve clopens because $x\mapsto gx$ and $x\mapsto g^{-1}x$ are continuous inverse maps. No finiteness-of-index theorem is being invoked: the needed finite coset cover was just obtained from compactness.

### lem-sfb-invariant-partition-quotient-system

Old step 3 (916 characters). Source: literature/stacks-project/topology.tex, Tag 08ZY, lemma-profinite, directed set of finite clopen decompositions, restricted to invariant decompositions.

Let $J$ be the set of $G$-invariant finite clopen partitions of $P$, and write $i\leq j$ when $j$ refines $i$. It is small under [def-weil-size-convention]: partitions form a subset of the power set of the power set of the underlying small set $P$. It is nonempty, using $\{P\}$ (or the empty partition when $P$ is empty). Intersecting the blocks of two invariant partitions and discarding empty intersections gives an invariant common refinement. Thus $J$ is directed and $J^{\mathrm{op}}$ is cofiltered. Let $P_i$ be the finite discrete set of blocks of $i$, and $r_{ji}:P_j\to P_i$ send a block to its unique containing block. These maps satisfy $r_{ii}=1$ and $r_{ki}=r_{ji}\circ r_{kj}$ for $i\leq j\leq k$. Each is surjective: choose a point in a coarse block and its block in the finer partition. The quotient $q_i:P\to P_i$ is likewise surjective, and $r_{ji}q_j=q_i$. Empty quotient sets cause no exception.

Old step 4 (705 characters). Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10, p. 28; explicit check of finite discrete continuous actions.

For $i\in J$, define $g\cdot B=gB$ on its blocks. The action identities follow from those on $P$, and $q_i(gx)=gq_i(x)$. The containing-block construction gives $r_{ji}(gB)=g r_{ji}(B)$, so all maps are equivariant. To check continuity of the finite action, for each block $B$ choose $x_B\in B$. For blocks $B,C$, invariance and disjointness give $gB=C$ if and only if $gx_B\in C$. Therefore $\{g:gB=C\}$ is open, being the inverse image of clopen $C$ under the continuous orbit map $g\mapsto gx_B$. The inverse image of $\{C\}$ under $G\times P_i\to P_i$ is the finite union of these open sets times $\{B\}$. The action is continuous. Also $q_i$ is continuous because the inverse image of $\{B\}$ is $B$.

### lem-sfb-cofinal-clopen-partition-reconstruction

Old step 5 (542 characters). Source: literature/stacks-project/topology.tex, Tag 08ZY, lemma-profinite, injectivity; clopen separation of points.

Finite invariant partitions separate points. If $x\ne y$ in $P$, choose an open neighbourhood $U$ of $x$ excluding $y$ by Hausdorffness. Apply [lem-weil-pbc-profinite-clopen-basis], with the given compactness, Hausdorffness and total disconnectedness of $P$, to find clopen $A$ with $x\in A\subseteq U$. The partition $\{A,P\setminus A\}$ separates $x,y$. Steps 1–2 supply an invariant finite refinement, which still separates them. Hence the canonical map $\phi:P\to L:=\{(B_i)\in\prod_{i\in J}P_i:r_{ji}(B_j)=B_i\ (i\leq j)\}$ is injective.

Old step 6 (733 characters). Source: literature/stacks-project/topology.tex, Tags 08ZY (lemma-profinite, surjectivity) and 005D (lemma-intersection-closed-in-quasi-compact, open-cover proof).

Let $(B_i)\in L$. The $B_i\subseteq P$ are nonempty closed blocks. Any finite collection of indices has a common refinement $j$, and compatibility says $B_j\subseteq B_i$ for every index in that collection. Thus every finite intersection of the $B_i$ is nonempty. If their total intersection were empty, the open complements $P\setminus B_i$ would cover compact $P$; a finite subcover would contradict the preceding nonempty finite intersections. Choose $x$ in their total intersection. Then $q_i(x)=B_i$ for all $i$, so $\phi$ is surjective. If $P$ is empty, the empty partition contributes an empty coordinate, so $L$ is empty as already checked. This writes out the finite-intersection argument, rather than using a further lemma.

Old step 7 (831 characters). Source: literature/stacks-project/topology.tex, Tags 08YE (lemma-bijective-map) and 0A2P (lemma-describe-limits, compatibility subspace topology).

The map $\phi$ is continuous for the specified topology: the inverse image of a basic cylinder in the product is a finite intersection of inverse images under the continuous $q_i$, and passing to the subspace $L$ preserves this assertion. Distinct compatible families differ at a coordinate, whose distinct singleton cylinders are disjoint open neighbourhoods; hence $L$ is Hausdorff. Apply [lem-weil-pbc-compact-hausdorff-bijection] to $\phi$ with whole source and target as the two subspaces: $P$ is compact by hypothesis, $L$ is Hausdorff as just verified, and steps 5–6 prove bijectivity. It follows that $\phi$ is a homeomorphism. Equivariance holds coordinatewise by step 4. The coordinate action preserves compatibility because every $r_{ji}$ is equivariant; its continuity is checked for arbitrary systems in step 10 below.

### lem-sfb-finite-action-compatible-limit

Old step 8 (857 characters). Source: literature/stacks-project/topology.tex, Tag 08ZU (theorem-tychonov) and Tag 08ZV (lemma-inverse-limit-quasi-compact, closed-subspace construction).

Now let $(Q_i,r_{ji})$ be any inverse system in the converse, with its given small nonempty directed index set $I$. Every finite discrete $Q_i$ is compact: an open cover has a finite subcover by choosing one member for each of its finitely many points. By [lem-weil-pbc-tychonoff-product-quasi-compact], the product $T=\prod_iQ_i$ with its product topology is compact. For each $i\leq j$, the equation $r_{ji}(z_j)=z_i$ cuts out a closed subset of $T$: at any failure the cylinder specifying $z_i$ and $z_j$ is an open neighbourhood consisting entirely of failures. Their intersection $Q$ is closed. It is compact directly from the open-cover definition: extend any cover of $Q$ by relative opens to opens of $T$, add $T\setminus Q$, and take a finite subcover of $T$. If any $Q_i$ is empty, $T$ and $Q$ are empty, and the same compactness conclusion holds.

Old step 9 (633 characters). Source: literature/stacks-project/topology.tex, Tag 08ZY, lemma-profinite, proof of (1) implies (2): separation by finite discrete coordinates.

The product $T$, and thus its subspace $Q$, is Hausdorff: any two distinct families differ at some coordinate, and the two distinct singleton cylinders at that coordinate separate them. It is also totally disconnected without any assumption on the transition maps. Indeed if a subset $C\subseteq Q$ contained distinct points, a singleton cylinder distinguishing their differing coordinate would give a nonempty proper clopen subset of $C$. This separates $C$ into two nonempty disjoint relatively open subsets, so $C$ is not connected. Therefore every connected subset has at most one point. These assertions include $Q=\varnothing$.

Old step 10 (769 characters). Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Example 4.1.10, p. 28, profinite continuous G-sets; explicit product-topology check.

Finally define $(gz)_i=gz_i$ for $g\in G$ and $z\in Q$. Equivariance of each transition map gives $r_{ji}(gz_j)=g r_{ji}(z_j)=gz_i$, so this family lies in $Q$. The unit and multiplication identities hold in each coordinate. For a finite cylinder $\bigcap_{i\in F}\{z:z_i\in U_i\}$, its inverse image under $G\times Q\to Q$ is the finite intersection of the inverse images of $U_i$ under $(g,z)\mapsto gz_i$. Each latter map is continuous: it is the composite of $(g,z)\mapsto(g,z_i)$ and the given continuous action on $Q_i$. These finite cylinders form a basis of the subspace topology of $Q$, so their open inverse images prove joint continuity of the coordinatewise action. This applies both to the arbitrary inverse system and to the partition system of steps 3–7.

## Validation

The first required dry run stopped before pushing at the duplicate-source check: two new nodes needed explicit comparisons with their own parent. Added those two comparisons above, explaining the stronger hypotheses-free generality and the explicit human requirement to extract the returned arguments. The repaired dry run exited successfully: OK (not pushed), branch deliver/Q138/lem-sfb-profinite-action-finite-quotients, commit 7c1173ac07d; the server preflight (including check_dag and review_split) passed. This report now records that result; the final dry run refreshes the receipt for this report, then direct delivery follows.


## Landing-return repair and current-DAG comparison

The latest return is L's landing refusal: the side completion had not been promoted to the live DAG. This is a rebase repair of the approved four-node split, preserving its mathematics, searches, citation quotes and complete handoff arguments. The delivery tool prepares the fresh commit against current server state; no git command was run in the shared read clone. The interrupted no-push invocation left a completed receipt at head 82cc3ed6f4c and no active delivery process, so it was not duplicated while running.

I compared every field of the retained parent with the current read-only DAG. The only differences are proof, proof_deps and split_report: the live parent still carries the original ten steps, whereas the retained delivery has the four-step assembly and four statement-only children. The statement, statement dependencies, provenance, blueprint information, searches and Lean/audit metadata agree and are retained. None of the four new node ids exists in the current DAG. The released stage-1 repair note still requests at least two independent nodes and an assembly of at most 3000 characters; the four-node split meets that order.

For the existing citations I reread def-sfb-invariant-discrete-quotients and def-weil-size-convention. The former still states invariant equivalence relations with discrete quotient topology and the containing-class transition diagram, ordered finer-is-smaller; parent step 2 explicitly reverses that order to its directed J. It is used only to identify the diagram. The latter still supplies the universe convention; no new size assumption is introduced. I rechecked all five parent citation entries against the actual current or retained node statements: every quote remains verbatim. Steps 1, 2, 3 and 4 respectively take invariant refinement, continuous quotient-system data, cofinal reconstruction and continuous compatible-family limits from the explicitly stated conclusions of their children.

I reread Bhatt–Scholze Example 4.1.10 and the retained arguments, checked the arbitrary-topological-group hypotheses of the quotient and limit children, and checked cofinality and directedness before reconstruction. Empty P gives the singleton indexing family consisting of the empty partition and an empty compatible-family space; empty stages remain allowed in the converse. The project source still has no finished declaration of the item under WeilConjectures, and the Sheaf declaration remains sorry. No mathematical amendment is needed after the rebase. The final no-push and push invocations are captured in this sandbox so their completion survives a provider interruption.
