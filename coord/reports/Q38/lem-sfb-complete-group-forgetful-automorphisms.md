# Q38 repair: lem-sfb-complete-group-forgetful-automorphisms

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-complete-group-forgetful-automorphisms.json: original statement unchanged; four assembly steps, 1668 characters.
- lem-sfb-orbit-translation-topological-embedding: statement, unsplit; no Mathlib match after LeanFinder, Loogle, grep and LeanSearch.
- lem-sfb-orbit-automorphism-cauchy-realizers: statement, unsplit; no Mathlib match after the same four search kinds.
- lem-sfb-orbit-reconstruction-extension: statement, unsplit; no Mathlib match after the same four search kinds.
- citations.json: one verbatim statement quotation per cited node per assembly step.

## Attachments

None. Read lean/Sheaf/GroupTheory/CompleteGroupForgetfulAutomorphisms.lean: the exact theorem ends in sorry. Search of lean/WeilConjectures for the blueprint tag, forgetful_automorphisms, openOrbitForget, Noohi and orbit/automorphism terminology found no finished declaration. No new-node argument has a finished project declaration in the searched source.

## WANTED

None; the sources used are available locally.

## Return repaired

The dispatcher retained no DAG files, report or prior search log in this sandbox: only .brief files. Copied the current shared item as returned-item.json and the editable item. This is the supplied eleven-step 5904-character proof, with the NP searches and stage-2 metadata; retained those fields and the exact statement. No git command was run in the shared repository. The delivery tool handles rebasing against server main and building the reviewable commit.

The human requested at least two comparable, independently provable statement-only nodes, a parent proof of at most 3000 characters, and preservation of every argument. We create three nodes: embedding (old steps 1–3, 1881 characters of argument), Cauchy realizers (old steps 4–6, 1546), and extension (old steps 10–11, 1329). Their proof/proof_deps are empty, status unsplit. Original convergence, compactness, and assembly steps 7–9 remain in the parent. No whole-theorem surrogate node was made. The complete old arguments below are worker handoff material in this report, not hidden proof sketches inside the new statements.

## Not duplicates

Searches before creating nodes: whole DAG for 7.1.5, Noohi, orbit category, two-sided Cauchy, natural automorphisms of discrete actions; blueprint_refs.py search forgetful, Cauchy and orbit, plus ancestor for the item. The ancestor is None, as inherited; preserve from.node null and extend via. No equivalent blueprint statement was found. New IDs were absent in the DAG. Read the statements of the possible definition/monodromy collisions.

- lem-sfb-orbit-translation-topological-embedding vs lem-sfb-complete-group-forgetful-automorphisms: the parent also proves surjectivity using completeness or compactness and the other extracted arguments; this lemma alone does not reconstruct the group.
- lem-sfb-orbit-translation-topological-embedding vs def-sfb-open-orbit-functor: the existing node defines the categories/functors and asserts none of this lemma's structural conclusions.
- lem-sfb-orbit-translation-topological-embedding vs def-sfb-set-functor-aut-pointwise-topology: the existing node defines the topology; it does not prove this embedding, Cauchy-net or restriction result.
- lem-sfb-orbit-translation-topological-embedding vs lem-sfb-complete-group-torsor-monodromy: the existing node classifies torsors on normal schemes; the new node concerns only topological groups and orbit functors.
- lem-sfb-orbit-translation-topological-embedding vs lem-sfb-compact-closed-finite-intersection: the existing node is an abstract compact-space intersection theorem; none of the new nodes assumes compactness or asserts its intersection conclusion.
- lem-sfb-orbit-automorphism-cauchy-realizers vs lem-sfb-complete-group-forgetful-automorphisms: the parent also proves surjectivity using completeness or compactness and the other extracted arguments; this lemma alone does not reconstruct the group.
- lem-sfb-orbit-automorphism-cauchy-realizers vs def-sfb-open-orbit-functor: the existing node defines the categories/functors and asserts none of this lemma's structural conclusions.
- lem-sfb-orbit-automorphism-cauchy-realizers vs def-sfb-set-functor-aut-pointwise-topology: the existing node defines the topology; it does not prove this embedding, Cauchy-net or restriction result.
- lem-sfb-orbit-automorphism-cauchy-realizers vs lem-sfb-complete-group-torsor-monodromy: the existing node classifies torsors on normal schemes; the new node concerns only topological groups and orbit functors.
- lem-sfb-orbit-automorphism-cauchy-realizers vs lem-sfb-compact-closed-finite-intersection: the existing node is an abstract compact-space intersection theorem; none of the new nodes assumes compactness or asserts its intersection conclusion.
- lem-sfb-orbit-reconstruction-extension vs lem-sfb-complete-group-forgetful-automorphisms: the parent also proves surjectivity using completeness or compactness and the other extracted arguments; this lemma alone does not reconstruct the group.
- lem-sfb-orbit-reconstruction-extension vs def-sfb-open-orbit-functor: the existing node defines the categories/functors and asserts none of this lemma's structural conclusions.
- lem-sfb-orbit-reconstruction-extension vs def-sfb-set-functor-aut-pointwise-topology: the existing node defines the topology; it does not prove this embedding, Cauchy-net or restriction result.
- lem-sfb-orbit-reconstruction-extension vs lem-sfb-complete-group-torsor-monodromy: the existing node classifies torsors on normal schemes; the new node concerns only topological groups and orbit functors.
- lem-sfb-orbit-reconstruction-extension vs lem-sfb-compact-closed-finite-intersection: the existing node is an abstract compact-space intersection theorem; none of the new nodes assumes compactness or asserts its intersection conclusion.

## Review by Q38

I read Bhatt–Scholze, printed pp. 63–65, especially Definition 7.1.1, Proposition 7.1.5 and Example 7.1.6, for the item and each new node. The source uses inverse cosets to force the second Cauchy condition; our Cauchy-realizer statement explicitly preserves it. It does not require normal open subgroups. The extension node takes bijective orbit translation as a hypothesis, so it neither assumes nor proves completeness and is strictly smaller than the original reconstruction theorem. It preserves the pointwise q_s formula of the old proof. The embedding node carries both the category/naturality checks and the inverse-topology calculation, not an unproved claim that a continuous bijection is automatically a homeomorphism. The Mathlib finite Galois reconstruction candidates were read in CategoryTheory/Galois/IsFundamentalgroup.lean and Topology.lean; FintypeCat-valued hypotheses prevent applying them to arbitrary orbits. The Tannaka grep hits concern finite-dimensional linear representations of finite groups, as checked in RepresentationTheory/Tannaka.lean, not discrete coset actions. Logged LeanFinder and LeanSearch questions give two distinct phrasings for each new statement, alongside Loogle and grep. No search record was invented.

Assembly step 1 takes exactly the embedding/homomorphism/topological-group conclusions from the embedding node, and the net, closed coordinate sets, finite-intersection property and both Cauchy differences from the realizer node. I opened those new statements after writing them and included their literal full statements in citations.json. Hausdorffness and the open-subgroup identity basis are exactly the item's hypotheses, with compactness/completeness unused here. Step 2 uses the item’s expressly stated net completeness and the data already obtained in step 1; the open-complement argument verifies that a limit remains in every closed coordinate fibre, and hides no completeness theorem. Step 3 uses precisely the full finite-intersection assertion of the existing compact leaf, whose statement I read, including its empty-family condition. I also read Stacks topology.tex, Tag 005D, lemma-intersection-closed-in-quasi-compact. The coordinate index D is a set because the orbit category is small; G is nonempty since it is a group. Step 4 uses surjectivity proved by either preceding branch and the embedding from step 1 to obtain the topological isomorphism; then it applies the extension node with exactly the bijectivity it assumes, obtaining actual restriction and the translation formula on every S. No use is taken from a cited proof rather than its statement.

Against delivery-errors B–E: each new statement introduces its group, categories, topology and universes (B2/B3), has empty proof/proof_deps and no proof sketch (B1), cites its exact source rather than an unspecific tag (B5/B7), and is neither a definition duplicate nor a Mathlib leaf. No existing node or unit was changed. All non-elementary assembly facts are explicit cited statements (C1/C4); the only uncited argument is closedness plus the given completeness assumption. The new statements do not depend on the parent, so the new edges cannot form a cycle. The detached blueprint ancestry is retained. The three statements split comparable parts of the original argument, rather than renaming the whole conclusion (D1/D2). No step exceeds 2000 characters.

Small cases: for the trivial group the orbit coordinate set is nonempty, the Cauchy differences are 1 and all constructions reduce to the identity. The empty finite coordinate family has V=G and g_empty=1, so the finite-intersection statement includes its empty case. For a discrete group U={1} forces eventual equality of realizers. Finite nonabelian groups (e.g. S_3 with a nonnormal order-two subgroup) use conjugated stabilizers, so no quotient-group or normality assumption is hidden. Infinite orbits and infinitely many open subgroups use finite subsets of the set D, never a countable sequence assumption. For the extension node empty actions have a unique empty component, zero orbit representatives are needed, and nontransitive actions are handled one point at a time by q_s. Hausdorffness is needed only for the embedding assertion; no compactness/completeness hypothesis was added to these lemmas. The incomplete finitary permutation group is deliberately allowed in the realizer lemma: it supplies a Cauchy net but no limit, demonstrating why that lemma is not the whole reconstruction theorem.

## Preserved argument and allocation to future workers

The following is the returned proof verbatim, with each step assigned to its new node or the assembly. In particular the finite-conjugate-intersection construction, the simultaneous realizer choices, both inverse-coordinate equations, both convergence alternatives, and both topology comparisons are retained for the workers who will split the new nodes.

### Original step 1 → lem-sfb-orbit-translation-topological-embedding

Use [def-nagata-category] for the category axioms: identities and composites of equivariant maps are equivariant. The open subgroups form a set, and each arrow set is a subset of the functions between two quotient sets, so $\mathcal O_G$ is small in the stipulated universes. The underlying-set functor simply keeps these maps. A natural automorphism $\alpha$ is a family of bijections $\alpha_U:G/U\to G/U$ satisfying $f\alpha_U=\alpha_Vf$ for every equivariant arrow $f:G/U\to G/V$. Its inverse family satisfies the same identities.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 2 → lem-sfb-orbit-translation-topological-embedding

For $g\in G$, left translation on every $G/U$ is a bijection, with inverse left translation by $g^{-1}$. Equivariance gives $f(gs)=gf(s)$ for every arrow, so these maps define $\Phi(g)\in\operatorname{Aut}(\omega_G)$. The identities $g(hs)=(gh)s$ and $1s=s$ give a group homomorphism $\Phi$. The pointwise topology on these natural automorphisms is a group topology: to keep $(\alpha\beta)(x)=\alpha(\beta(x))$ fixed it suffices to keep $\beta(x)$ and $\alpha(\beta(x))$ fixed at the given pair; to keep $\alpha^{-1}(x)=y$ fixed it suffices to require $\alpha(y)=x$. Finite intersections give continuity of multiplication and inversion.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 3 → lem-sfb-orbit-translation-topological-embedding

For $x=aU\in G/U$, its stabilizer is $aUa^{-1}$, an open subgroup since conjugation is a homeomorphism. Each fibre of $g\mapsto gx$ is a left coset of this subgroup; it is open and closed, because the complementary cosets are open too. Thus the inverse image under $\Phi$ of a basic pointwise-open set is open. If $\Phi(g)=1$, then $gU=U$ for every open $U$, so $g\in\bigcap_U U=\{1\}$: Hausdorffness provides, for any $g\ne1$, an identity neighborhood missing $g$, and the subgroup basis refines it. Moreover $\Phi^{-1}(\{\alpha:\alpha_U(U)=U\})=U$. These last open subgroups form an identity basis of $G$, so once $\Phi$ is bijective its inverse is continuous at the identity, hence everywhere by translation.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 4 → lem-sfb-orbit-automorphism-cauchy-realizers

Fix $\alpha\in\operatorname{Aut}(\omega_G)$. Given finitely many coordinates $x_j=a_jU_j$, set $V=\bigcap_j a_jU_ja_j^{-1}$, with $V=G$ for the empty list. The formula $q_j(hV)=ha_jU_j$ is well-defined because $V\subseteq a_jU_ja_j^{-1}$ and is equivariant. Choose a representative $b\in G$ of the coset $\alpha_V(V)$. Naturality gives $\alpha_{U_j}(x_j)=q_j(\alpha_V(V))=bx_j$ for every $j$. Thus a single group element realizes any finite list of coordinates of $\alpha$; for the empty list one may use $1$.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 5 → lem-sfb-orbit-automorphism-cauchy-realizers

Let $D=\coprod_{U\text{ open}}G/U$, a set of tagged coordinates. Direct its finite subsets by inclusion. For each finite $F\subseteq D$ choose $g_F\in G$ realizing $\alpha(x)$ at every $x\in F$, using the preceding step. For each coordinate $x$, the net $(g_Fx)_F$ is eventually constant with value $\alpha(x)$. Also put $C_x=\{g\in G:gx=\alpha(x)\}$. Each $C_x$ is a closed coset by step 3, and step 4 says every finite intersection of the $C_x$ is nonempty, including the empty intersection.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 6 → lem-sfb-orbit-automorphism-cauchy-realizers

For an open subgroup $U$, let $x=U\in G/U$ and $y=\alpha_U^{-1}(x)$. Once $F,F\prime$ both contain the two tagged coordinates $x,y$, we have $g_Fx=\alpha_U(x)=g_{F\prime}x$ and $g_Fy=x=g_{F\prime}y$. The first equality gives $g_F^{-1}g_{F\prime}\in U$. The second gives $g_F^{-1}x=y=g_{F\prime}^{-1}x$, hence $g_Fg_{F\prime}^{-1}\in U$. Since the open subgroups refine all identity neighborhoods, this is exactly the two-sided Cauchy condition in the hypothesis. Both $\alpha$ and its inverse are essential here; no normality of $U$ is assumed.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 7 → parent completeness assembly

If the completeness alternative holds, the Cauchy net just constructed converges to some $g\in G$ by the stated assumption. For each coordinate $x$, its tail lies in $C_x$. As $C_x$ is closed, $g\in C_x$: otherwise its open complement would be a neighborhood of the limit eventually containing the net, a contradiction. Consequently $gx=\alpha(x)$ at every coordinate.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 8 → parent compactness assembly

If the compact alternative holds, apply [lem-sfb-compact-closed-finite-intersection] to $X=G$, $I=D$ and the closed sets $C_x$ of step 5. The hypothesis about every open cover having a finite subcover is exactly compactness of $G$, and the finite-intersection hypothesis, including the empty family, is step 4. We obtain $g\in\bigcap_{x\in D}C_x$, so again $gx=\alpha(x)$ at every coordinate.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5 and Example 7.1.6, printed p. 64; compact case via Stacks 005D (lemma-intersection-closed-in-quasi-compact).

### Original step 9 → parent isomorphism assembly

Under either alternative we have $\Phi(g)_U(x)=\alpha_U(x)$ for every $U$ and every $x\in G/U$. Equality of functions and then of natural transformations gives $\Phi(g)=\alpha$. Thus $\Phi$ is surjective and, by step 3, injective. Its multiplication law is step 2 and both directions are continuous by step 3. This proves the asserted topological group isomorphism for the orbit category.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64; elementary orbit-coordinate expansion of its coset-filter argument.

### Original step 10 → lem-sfb-orbit-reconstruction-extension

Let $F_G$ be the underlying-set functor on all discrete continuous left $G$-sets. For any such set $S$ and $s\in S$, its stabilizer $U_s$ is open, since it is the inverse image of the open singleton $\{s\}$ under $g\mapsto gs$. The map $q_s:G/U_s\to S$, $hU_s\mapsto hs$, is well-defined and equivariant. If $\beta\in\operatorname{Aut}(F_G)$ restricts to $\alpha$ on the orbit category, step 9 gives a unique $g$ with $\alpha=\Phi(g)$. Naturality for $q_s$ gives $\beta_S(s)=q_s(\alpha_{U_s}(U_s))=gs$. Conversely the family of translations by any $g$ is natural on all equivariant maps. Hence restriction is bijective, with inverse given by these translation families; it respects multiplication.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64, sentence that every discrete G-set is a disjoint union of G/U; expanded pointwise without choosing orbit representatives.

### Original step 11 → lem-sfb-orbit-reconstruction-extension

Restriction is continuous because every orbit-coordinate evaluation is among the evaluations on all discrete actions. For the inverse restriction map, consider a coordinate $s\in S$ and its equivariant map $q_s$ above. For every $\alpha$, its extension satisfies $\beta_S(s)=q_s(\alpha_{U_s}(U_s))$. Evaluation at $U_s$ is continuous by the pointwise topology, and $q_s$ is continuous between discrete sets. Thus this coordinate of the extension is continuous. A basic open condition specifies only finitely many coordinates, so its inverse image is open. This proves that restriction and its inverse preserve the stated topologies.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 7.1.5, printed p. 64, orbit determination and compact-open (= pointwise on discrete sets) topology.

## What remains

The three new nodes intentionally remain statement-only work items for independent workers. No Lean file was written, no compiler/Lake/build was run, and no SGA source was used. No mathematical statement dispute was found. Required dry run and final push follow this review; their results are recorded below.
