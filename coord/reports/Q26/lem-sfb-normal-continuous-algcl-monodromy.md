# Worker report — Q26

Repair item: lem-sfb-normal-continuous-algcl-monodromy; stage 1 only, 2026-10-22.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-continuous-algcl-monodromy.json: statement unchanged; six-step assembly, 2327 characters; five new tasks cited.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-generic-lisse-cocycle.json: statement; Mathlib verdict no match; status unsplit, empty proof and proof_deps, null proof_origin.
- dag/nodes/sec-six-functors-basics/lem-sfb-complete-nonarchimedean-matrix-group.json: statement; Mathlib verdict no match; status unsplit, empty proof and proof_deps, null proof_origin.
- dag/nodes/sec-six-functors-basics/lem-sfb-completed-frame-generic-comparison.json: statement; Mathlib verdict no match; status unsplit, empty proof and proof_deps, null proof_origin.
- dag/nodes/sec-six-functors-basics/lem-sfb-compact-torsor-associated-lisse.json: statement; Mathlib verdict no match; status unsplit, empty proof and proof_deps, null proof_origin.
- dag/nodes/sec-six-functors-basics/lem-sfb-generic-lisse-scalar-comparison.json: statement; Mathlib verdict no match; status unsplit, empty proof and proof_deps, null proof_origin.
- report.md and citations.json: complete review, original argument allocation and exact statement quotations.

## Attachments

None. The upstream WeilConjectures search found no declaration with the exact item tag or a complete exact statement. The attached project theorem in lean/Sheaf/Paper/NormalContinuousAlgClMonodromy.lean:67 ends in sorry. Neither it nor the related finite-E monodromy node is an attachment for the all-continuous Omega equivalence with its scalar compatibility. No Lean file was written or compiled.

## WANTED

None. The relevant Bhatt–Scholze PDF and Stacks sources are present.

## What was wrong and what changed

The return explicitly requires spreading the former 9671-character proof among at least three independent unsplit tasks; an unchanged push or a condensed account would not repair it. The sandbox initially contained only dispatcher .brief files, no earlier node, report, citations or search log. I therefore copied the current read-only repository item, which contains the reviewed delivery and its nine original steps, and preserved its statement, prior source attribution, metadata and Lean attachment. There was no prior sandbox search to reuse. The reviewed record is historical; this new split still needs the maintainer's independent review.

Five new nodes distribute distinct arguments rather than giving the equivalence another name. The item keeps the elementary assembly. The retained proof route is generic restriction, completion to detect inertia, descent through the generic profinite quotient, compact-image reconstruction, and simultaneous coefficient comparison. No SGA source is used. The blueprint ancestor command returns None; the explicit inherited paragraph (3) place and via chain are retained and extended for each child. Whole-blueprint searches for monodromy, generic restriction, complete general linear, continuous frame, generic cocycle and compact torsor found no node stating these new tasks. The generic-restriction search's geometric exchange and zero-generic-acyclic results concern different cohomological assertions.

## What remains

The five new statement-only nodes need separate proofs by future workers. This is the requested stage-1 one-level split; their proof arguments are preserved below for those workers. The existing geometric generic-section, separable-Cech, and complete-group torsor nodes are reused and not modified. No target statement, definition, unit route, chapter record, library or launcher file changed.

## Review by Q26

I read the item's nine steps and source attribution, the six-functor chapter and stability unit, and Bhatt–Scholze Section 7.1 pp. 63–65 and Section 7.4 pp. 70–71, especially Proposition 7.1.5, Lemmas 7.4.7 and 7.4.10, Remark 7.4.8, and Example 7.1.7. The last example explicitly uses the colimit topology, so it cannot be cited as the norm-topology Omega theorem. Each new source entry therefore identifies an agent expansion of the recorded framework rather than attributing that expansion to the paper. For the generic component reduction and quotient I read Stacks properties.tex lemma-normal-locally-finite-nr-irreducibles (0357) and pione.tex lemma-normal-pione-quotient-inertia (0BTD). I also read sites.tex lemma-glue-maps (04TQ) and lemma-glue-sheaves (04TR) for the original matrix and module gluing arguments. No new node merely packages one of these Stacks results.

New generic-cocycle task: I checked the statements of the existing generic-section bijection, separable-Cech coordinates, internal module definition, continuous realization and set-sheaf gluing nodes. Their hypotheses supply respectively normal integral locally Noetherian base, arbitrary nonarchimedean coefficients without completeness, constant matrices over k^s, actual internal module arrows, all continuous sections, and effective descent on small slice sites with fibre products. The new task says precisely the matrix-extension and cocycle conclusions, including rank and basis changes. It also carries the old integral reduction and total-disconnectedness assertion. It does not assert essential surjectivity over the scheme.

New matrix-group task: I checked the recorded completion leaf, the complete-group torsor hypotheses, and the complete-group forgetful-automorphism node. The latter is conditional on completeness and does not prove completeness for GL. The new task states the missing open congruence subgroups, geometric-series inverse and convergence of a two-sided Cauchy net, including limits of inverses. Matrix size zero is explicit. Mathlib's nonarchimedean completion instance is about additive/ring open subgroup bases, not the multiplicative two-sided completion of GL; Units.ofNearby and the ultrametric open-subgroup lemmas also do not give this whole assertion.

New completed-frame task: I reread the torsor node's pointed pullback, coefficient-group extension and field clauses. The field clause gives pr2*p = pr1*p*c and c(gh)=c(g)c(h); the Cech node supplies entrywise coefficient change. Those exact clauses identify the completed frame cocycle with iota*sigma, without a sign or inverse ambiguity. I included the kernel and continuous quotient conclusion as an explicit output of this new task, preserving the old Step 6 argument. Completion injectivity is necessary; the proof never asserts that arbitrary F-valued matrix entries lie in A. Normality and integrality justify the generic fundamental-group surjection; quasi-compact plus locally Noetherian makes the scheme Noetherian for the torsor correspondence.

New compact associated-module task: the old construction is made a reusable statement for arbitrary compact H, a continuous linear action r, and an H-valued representation theta. It specifies the right-torsor associated-module relation and the frame equation, so there is no hidden convention change. Its completed frame extension and its precise generic cocycle are conclusions to be proved by its worker. In the image case H is compact Hausdorff as the continuous image of profinite pi1; congruence neighborhoods give an open-subgroup basis even if A itself is incomplete. General set-sheaf descent is sufficient to glue addition and scalar action because the identities can be checked on the covering. This construction is strictly smaller than the equivalence: it does not prove full faithfulness or simultaneous scalar compatibility.

New scalar-comparison task: I checked the ordinary internal coequalizer scalar-extension definition and the postcomposition map definition, rather than substituting adic or coefficient-colimit categories. The statement specifies the local and generic entrywise matrices, the scalar-extension unit, every morphism and the action on pure tensors. It does not identify arbitrary B-valued functions with functions in some finite A-subextension. Its final clause assumes the generic actions factor and only asserts that the comparison still intertwines them and any fixed basepoint transport; it does not itself construct the equivalence.

Assembly Step 1 cites only the Noetherian closed-subset lemma and the normal-components lemma. The former supplies the closed-set minimum condition and hence the descending-chain condition, and the latter explicitly gives finite clopen integral components. Connected and nonempty selects exactly one. This is an elementary inference from their statements.

Assembly Step 2 cites the new generic-cocycle node, whose statement explicitly gives the A-linear fully faithful functor, rank, regular object, sums, zero and all arrows. The item supplies its connected normal Noetherian hypotheses. Finite E and Omega both carry their restricted nonarchimedean norms.

Assembly Step 3 cites the completion leaf for its isometric injective inclusion; the new matrix-group node for the open-subgroup basis and two-sided completeness; the new frame node for tau*q = iota*sigma; and the normal Galois quotient node for the continuous surjection q. I opened every one of these statements. The short residual argument identifies the kernel by injectivity, descends each continuous coordinate along a compact-to-Hausdorff quotient, and identifies intertwiner equations by surjectivity. It is not marked elementary, since it assembles the cited substantive lemmas. It claims nothing from the unquoted inertia-generation portion of the Galois node.

Assembly Step 4 cites the new compact associated-module node. Its final clause gives exactly a lisse module with generic cocycle rho*q. The already established surjection identifies its factored representation with rho. Full faithfulness plus this essential surjectivity yields the equivalence. No second classification theorem is imported.

Assembly Step 5 uses paragraph 1 of the existing basepoint-transport node, which explicitly supplies a path and a topological conjugation isomorphism for finite fibre functors. Its adic later paragraphs are unused. The generic-cocycle node supplies regular module, block sums, zero and the linear matrix description. A single chosen path is used for all coefficient fields, so this assembly is elementary and imposes no unsupported notion of a completed coefficient fibre at the prescribed point.

Assembly Step 6 cites the new generic scalar-comparison node: it explicitly states lisseness, the canonical natural tensor comparison, the action formula, and compatibility with both factorization and fixed topological transport. The E-to-Omega map is the continuous field inclusion with the prescribed restricted norm. Hence this last step is substitution in that statement, marked elementary. I checked the verbatim citations.json quotes for every cited node and every step.

Small cases: X = Spec(k) makes q the identity and tests the field cocycle convention. X disconnected would allow varying ranks, so connectedness is retained in the generic-cocycle task. A nodal nonnormal curve is excluded; normality is not dropped. The empty scheme is excluded by nonemptiness. A trivial representation has a trivial associated module. H = {1} tests both the contracted-product relation and the inverse convention. The right relation [ph,v]=[p,r(h)v] gives e_j=e_i*r(h_ij), matching pr2*p=pr1*p*c. Rank zero gives the unique empty matrices, the trivial GL_0 group, and the zero module throughout. E = Q_l and the identity coefficient embedding test the pure-tensor map; on a morphism matrix both naturality composites are the entrywise image. An incomplete normed A is permitted only with its actual completion F when completeness is used; no local compactness assumption is smuggled into the torsor argument.

I checked delivery-errors B through E in full. Each new node introduces its own fields, scheme, points, rings and maps; inline definitions or existing definition nodes give all notions. New nodes have no proofs, no proof sketches disguised as statements, and no proof dependencies. Three search kinds and a second semantic phrasing were run through msearch for each. The two rate-limited LeanSearch responses are recorded unavailable; successful LeanFinder and Loogle searches and source greps are retained with their actual queries. I read all returned hits and inspected the relevant Mathlib Nonarchimedean/Completion, Sheaf/Free and NonabelianCohomology/H1 sources: these are useful ingredients, not an exact match or one-line specialization of a new node. Source/blueprint and project declaration searches were done before writing nodes. None of the extracted arguments is a standalone elementary two-line fact, and none simply restates the full item. No new unsplit node depends on the item. The longest assembly step is below 1000 characters; no assembly step exceeds 2000.

## Not duplicates

lem-sfb-normal-generic-lisse-cocycle vs lem-sfb-normal-generic-continuous-sections: the existing node extends scalar ring sections; the new node extends module morphisms, detects rank and gives the Galois-cocycle functor.

lem-sfb-normal-generic-lisse-cocycle vs lem-sfb-field-separable-cech-coordinates: the existing node gives Cech rings and freeness over a separably closed field; the new node gives full faithfulness over the original normal scheme.

lem-sfb-normal-generic-lisse-cocycle vs lem-a1-normal-proetale-monodromy: the existing equivalence uses finite E and completed integral coefficients; the new task treats generic restriction for arbitrary nonarchimedean all-continuous coefficients, without essential surjectivity.

lem-sfb-complete-nonarchimedean-matrix-group vs lem-sfb-normed-field-completion: the existing leaf completes the coefficient field; the new task proves the multiplicative matrix-group topology and two-sided completeness.

lem-sfb-complete-nonarchimedean-matrix-group vs lem-sfb-complete-group-forgetful-automorphisms: the existing result assumes group completeness; the new result verifies that hypothesis for GL_n of the completed field.

lem-sfb-completed-frame-generic-comparison vs lem-sfb-complete-group-torsor-monodromy: the existing result classifies abstract continuous-function torsors; the new result constructs the completed module frame torsor and computes its exact generic coefficient cocycle and factor.

lem-sfb-completed-frame-generic-comparison vs lem-sfb-field-separable-cech-coordinates: the existing calculation has no frame torsor monodromy or scheme fundamental-group quotient; the new task identifies those with the embedded cocycle.

lem-sfb-compact-torsor-associated-lisse vs lem-sfb-complete-group-torsor-monodromy: the existing torsor classifier has no associated internal module, its descended module operations, or completed frame identification.

lem-sfb-compact-torsor-associated-lisse vs def-sfb-continuous-right-torsor: the existing definition specifies torsors and extension presentations; the new node proves existence and cocycle assertions for associated lisse modules.

lem-sfb-generic-lisse-scalar-comparison vs lem-sfb-field-separable-cech-coordinates: the existing node supplies field-chart formulas only; the new node glues ordinary scalar extension on X and proves its natural generic/factored comparison.

lem-sfb-generic-lisse-scalar-comparison vs lem-sfb-normed-coefficient-realization: the existing node transports derived modules along isometric finite-field isomorphisms; the new node allows an arbitrary continuous coefficient embedding and controls lisse generic descent, including E into Omega.

lem-sfb-generic-lisse-scalar-comparison vs lem-weil-pbc-constant-coefficient-lisse-restriction: the existing result restricts scalars along a surjection of constant discrete rings; the new node extends scalars along a continuous field embedding with all continuous function coefficients.

lem-sfb-generic-lisse-scalar-comparison vs lem-wf-fibre-functor-basepoint-transport: the existing node constructs finite fibre-functor paths and discusses adic fibres; the new node compares generic normed coefficient tensors and only conditionally transports an already factored action.

## Allocation of every original argument

The following is the original reviewed argument verbatim, not a shortened substitute. The new nodes carry its intermediate conclusions as independently provable statements. This section gives their future workers all of the original reasoning and the exact input nodes that were previously used. The small component selection, quotient-map calculation and common-path assembly are also retained explicitly in the item. The five task arguments have comparable workloads (roughly one to two original substantive steps), rather than moving the whole proof into one child.

### Original Step 1 → lem-sfb-normal-generic-lisse-cocycle

First work at a geometric generic point $\bar\eta$. The Noetherian hypothesis gives the descending-chain condition on closed subsets by [lem-weil-pbc-noetherian-scheme-closed-subsets-minimal]. Apply [lem-trf-normal-topologically-noetherian-components]: the normal scheme has finitely many disjoint clopen integral components. Since $X$ is nonempty and connected it has exactly one, so is integral. Write $k=\mathcal O_{X,\eta}$, choose $k^s$, and put $G_k=\operatorname{Aut}_k(k^s)$. For $A=K$ or a complete normed field containing it, use [lem-weil-pbc-condensed-field-continuous-realization] to identify the specified pulled-back ring with $U\mapsto C(|U|,A)$. This identification uses all continuous maps. A nonarchimedean field is totally disconnected: two distinct points are separated by complementary clopen balls of radius less than their distance.

Original cited nodes: lem-weil-pbc-noetherian-scheme-closed-subsets-minimal, lem-trf-normal-topologically-noetherian-components, lem-weil-pbc-condensed-field-continuous-realization.

### Original Step 2 → lem-sfb-normal-generic-lisse-cocycle

Here is the generic restriction argument, including its use on morphisms. Choose an affine pro-etale covering trivializing two lisse modules $L,M$. On each covering object $U$ a map is a rectangular matrix over $R_A(U)$: its columns are the images of the standard basis maps, by the regular module universal property. The ring bijection of [lem-sfb-normal-generic-continuous-sections] extends each matrix of a generic morphism uniquely from $U_\eta$ to $U$. On affine refinements of each overlap, injectivity of that same ring map makes the extended matrices agree with the transition matrices; the generic compatibility equation is therefore also the global one. Use morphism gluing in [lem-pe-set-sheaf-cover-descent] on underlying sheaves; addition and scalar linearity hold locally and hence globally. Thus restriction to $\eta$ is fully faithful on lisse modules. If a generic map is invertible, extend its inverse too; uniqueness makes the two composites identities. Also, every nonempty affine trivializing object has nonempty generic fibre (otherwise the ring bijection would identify a nonzero constant $1$ with $0$). By [lem-sfb-field-separable-cech-coordinates], evaluation at any geometric generic point of this fibre compares its free rank with the dimension of $L$ over $k^s$. Consequently the rank is one fixed integer $n$ on the whole trivializing covering; $n=0$ is allowed.

Original cited nodes: lem-sfb-normal-generic-continuous-sections, lem-pe-set-sheaf-cover-descent, lem-sfb-field-separable-cech-coordinates, sk-def-sfb-module-objects.

### Original Step 3 → lem-sfb-normal-generic-lisse-cocycle

Pull $L|_\eta$ to $\operatorname{Spec}k^s$. By [lem-sfb-field-separable-cech-coordinates] choose a basis of its free rank $n$ module. Its descent isomorphism is a matrix $c\in\operatorname{GL}_n(C(G_k,K))$. Evaluate on $g\in G_k$: $\sigma_L(g)=c(g)$ has continuous entries and the Cech identity gives $\sigma_L(gh)=\sigma_L(g)\sigma_L(h)$ and $\sigma_L(1)=1$. A morphism between two such objects is a constant matrix $B$ over $K$ on $\operatorname{Spec}k^s$, with descent equation $B\sigma_L(g)=\sigma_M(g)B$. Conversely these equations suffice for gluing the map, by [lem-pe-set-sheaf-cover-descent]. Changing the chosen basis conjugates the matrices, so one obtains a functor to representations, independently of a coordinate presentation up to the basis-change isomorphism. Coefficient extension changes every displayed matrix by the coefficient homomorphism, by the same Cech-coordinate node.

Original cited nodes: lem-sfb-field-separable-cech-coordinates, lem-pe-set-sheaf-cover-descent.

### Original Step 4 → lem-sfb-complete-nonarchimedean-matrix-group

Set $F=\widehat K$ and let $\iota:K\hookrightarrow F$ be the isometric field map of [lem-sfb-normed-field-completion]. The nonarchimedean inequality holds on $F$ too, by taking limits in that inequality on the dense subfield $K$. For each $n$, $\operatorname{GL}_n(F)$ satisfies the complete-group hypotheses of [lem-sfb-complete-group-torsor-monodromy]. Indeed the subgroups $1+\{B:\max_{ij}|B_{ij}|<r\}$ for $0<r<1$ form a neighborhood basis of $1$; multiplication preserves this bound and the geometric series converges in the complete matrix ring to the inverse. A two-sided Cauchy net of invertible matrices has both its matrices and its inverses Cauchy entrywise: fix a sufficiently late matrix to bound the norms of the tail and its inverses, then multiply the small relative differences by these bounds. Their limits $a,b$ satisfy $ab=ba=1$, proving completeness for the two-sided uniformity. This also covers $n=0$, when the group is trivial.

Original cited nodes: lem-sfb-normed-field-completion, lem-sfb-complete-group-torsor-monodromy.

### Original Step 5 → lem-sfb-completed-frame-generic-comparison

Form $L_F=R_{F,X}\otimes_{R_{K,X}}L$ along postcomposition by $\iota$. Locally $R_F\otimes_{R_K}R_K^n\cong R_F^n$ by $a\otimes(b_i)\mapsto(a\iota(b_i))$ with inverse $(a_i)\mapsto\sum_i a_i\otimes e_i$; these are identities from the tensor relations. Hence $L_F$ is locally free of rank $n$. Its frame sheaf $P(U)=\operatorname{Isom}_{R_{F,U}}(R_{F,U}^n,L_F|_U)$ is an $F_{\operatorname{GL}_n(F)}$-torsor: in a local basis its sections and action are invertible continuous matrices and matrix multiplication. Apply [lem-sfb-complete-group-torsor-monodromy] at $\bar\eta$, with the frame $p$ induced by the generic $K$-basis over $k^s$, to obtain $\tau_L:\pi_1(X,\bar\eta)\to\operatorname{GL}_n(F)$. By the pointed pullback clause of [lem-sfb-complete-group-torsor-monodromy], the homomorphism of the pullback of $(P,p)$ to $\operatorname{Spec}k$ is $\tau_Lq$, where $q:G_k\to\pi_1(X,\bar\eta)$ is induced by $\operatorname{Spec}k\to X$. By its field clause it is the descent cocycle of the frame $p$ over $k^s$, and by the coefficient formula of [lem-sfb-field-separable-cech-coordinates] that cocycle is the entrywise image $\iota\sigma_L$ of the Step 3 cocycle. Hence $\iota\sigma_L=\tau_Lq$.

Original cited nodes: sk-def-sfb-change-of-scalars, def-sfb-continuous-map-condensed-ring-map, lem-sfb-complete-group-torsor-monodromy, lem-sfb-field-separable-cech-coordinates.

### Original Step 6 → lem-sfb-completed-frame-generic-comparison

The continuous map $q:G_k\to\pi_1(X,\bar\eta)$ is surjective by [lem-dl-a1-normal-scheme-galois-inertia-presentation]. For $h\in\ker q$ the equality $\iota\sigma_L(h)=\tau_L(qh)=1$ and injectivity of $\iota$ give $\sigma_L(h)=1$. It therefore factors uniquely as $\sigma_L=\rho_Lq$ with values in $\operatorname{GL}_n(K)$. This factor is continuous: $G_k$ and $\pi_1(X,\bar\eta)$ are profinite, so the continuous surjection $q$ is a quotient map (images of closed subsets are compact and hence closed in the Hausdorff target); each continuous coordinate of $\sigma_L$ descends through this quotient. For maps, Step 3 and surjectivity of $q$ say exactly that their constant generic matrices intertwine $\rho_L$ and $\rho_M$. Together with Step 2 this proves that $L\mapsto\rho_L$ is $K$-linear and fully faithful. No completion-valued matrix is asserted to lie in $K$ without this surjectivity argument.

Original cited nodes: lem-dl-a1-normal-scheme-galois-inertia-presentation.

### Original Step 7 → lem-sfb-compact-torsor-associated-lisse

For essential surjectivity take $\rho:\pi_1(X,\bar\eta)\to\operatorname{GL}_n(K)$ continuous and let $H=\rho(\pi_1(X,\bar\eta))$ with its subspace topology. It is a compact Hausdorff topological group, and intersections with the small congruence subgroups of $\operatorname{GL}_n(K)$ give an open-subgroup basis. Thus the compact case of [lem-sfb-complete-group-torsor-monodromy] gives a pointed $F_H$-torsor with monodromy $\rho$ viewed as a map into $H$. On a covering trivializing this torsor, glue the free modules $R_K^n$ using the transition functions $H\hookrightarrow\operatorname{GL}_n(K)$. The cocycle identity for the torsor is exactly the matrix gluing identity. Effective sheaf descent and morphism gluing in [lem-pe-set-sheaf-cover-descent] glue the underlying sheaf, addition and $R_K$-action; the module identities hold on the covering and therefore globally. The resulting module is lisse by its local construction. After scalar extension to $F$, its frame torsor is the extension of the $H$-torsor along $H\to\operatorname{GL}_n(F)$, so naturality of torsor monodromy for this map and for the pointed pullback to $\operatorname{Spec}k$, followed by the field clause of [lem-sfb-complete-group-torsor-monodromy], identifies its completed generic cocycle with $\iota\rho q$. The field-coordinate description and injectivity of $\iota$ then identify its generic cocycle with $\rho q$. The functor of Steps 3–6 therefore sends it to $\rho$, proving essential surjectivity.

Original cited nodes: lem-sfb-complete-group-torsor-monodromy, lem-pe-set-sheaf-cover-descent, lem-sfb-field-separable-cech-coordinates.

### Original Step 8 → lem-sfb-generic-lisse-scalar-comparison

Choose a path between the finite fibre functors at $\bar\eta$ and at the prescribed point $\bar x$ using the first paragraph of [lem-wf-fibre-functor-basepoint-transport]. It gives a topological group isomorphism $c_t:\pi_1(X,\bar\eta)\xrightarrow{\sim}\Pi$. Transport each $\rho_L$ by $c_t^{-1}$, using the same path for every coefficient field. This gives the required equivalences $\Phi_K$. The generic-coordinate description sends the regular module to the one-dimensional trivial representation and a finite sum to the direct sum, since its descent matrix is respectively $1$ and the block sum of the descent matrices. The zero module corresponds to $K^0$, and the constructions in Steps 3–7 use the unique empty matrices for rank zero. Identities, composition and sums of maps are the corresponding matrix operations, so these are $K$-linear equivalences.

Original cited nodes: lem-wf-fibre-functor-basepoint-transport.

### Original Step 9 → lem-sfb-generic-lisse-scalar-comparison

Finally fix finite $E\subseteq\Omega$ and a lisse $R_{E,X}$-module $L$. On a local free chart its ordinary scalar extension is $R_{\Omega}^n$, by $a\otimes(b_i)\mapsto(ab_i)$ and inverse $(a_i)\mapsto\sum_i a_i\otimes e_i$. On an overlap its transition matrix is obtained from that of $L$ by entrywise inclusion $E\hookrightarrow\Omega$, because both maps send $a\otimes v$ to $a$ times the image of $v$. Thus it is lisse. On the generic separable-closure chart [lem-sfb-field-separable-cech-coordinates] gives the canonical vector-space comparison $\Omega\otimes_E V\cong V_\Omega$, and its descent action is $a\otimes v\mapsto a\otimes\sigma_L(g)v$. Factoring through the same surjection $q$ and transporting by the same $c_t$ changes this to $a\otimes v\mapsto a\otimes\rho_L(g)v$, as required. For a morphism with generic matrix $B$ both comparison composites have matrix obtained by including the entries of $B$ in $\Omega$, so the comparison is natural. This proves the scalar-extension isomorphism for the specified postcomposition coefficient map, without replacing all continuous functions by finite-subextension-valued ones.

Original cited nodes: lem-sfb-field-separable-cech-coordinates, sk-def-sfb-change-of-scalars, def-sfb-continuous-map-condensed-ring-map.

## Validation

Server review_split was run through srvcheck before the report was written and passed the item. The required deliver.py --no-push is run after this report and all node files are finalized; the push follows only after its successful exit. This report makes no claim of Lean compilation or completed proofs of the five new tasks.
