# O3 repair: lem-sfb-condensed-internal-bar-resolution

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-internal-bar-resolution.json: statement, unchanged; status split; four assembly steps, 2488 characters total.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-free-linearization-tensor.json: new statement, unsplit; no Mathlib match after five recorded searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-condensed-group-algebra-exact-forgetful.json: new statement, unsplit; no Mathlib match after five recorded searches.
- dag/nodes/sec-six-functors-basics/lem-sfb-pointed-free-deletion-contraction.json: new statement, unsplit; no Mathlib match after five recorded searches.
- citations.json: verbatim statement excerpts for each citation of each new assembly step.

All files and research artifacts are in the assigned sandbox. No repository or launcher file was written, no git command was run in the shared repository, and no Lean, compiler or Lake command was used.

## Attachments

None. Searching lean/WeilConjectures for the blueprint tag and the internal homogeneous-bar notion found no theorem stating all clauses. The existing project specification in lean/Sheaf/CategoryTheory/CondensedInternalBarResolution.lean:266 is Profinite.CondensedAction.InternalBar.exists_resolution, with body sorry. Its free and freeAdjunction definitions are already owned by def-sfb-condensed-free-module-adjunction and are reused rather than recreated. The near Mathlib barResolution is for ordinary modules and an abstract group.

## WANTED

WANTED: an independent ordinary condensed-module reference for the internal homogeneous bar resolution over a variable commutative condensed ring, especially the group-algebra action equivalence and the arbitrary-module tensor contraction, for lem-sfb-condensed-internal-bar-resolution and its new children. This is the inherited wanted reference, not a claim that the blueprint supplies a written condensed bar proof.

## What was wrong and what changed

The human return requests spreading the ten-step, 9882-character argument into at least three comparable independent obligations, not merely shortening it. The sandbox initially contained only dispatcher marker files, no node, report or search log. The required initial deliver.py --no-push exited with “FAILED: no node files under .../dag/nodes/”. I copied the current shared node, including its full previously reviewed proof and maintainer's internal-to-section tensor correction. returned-item.json preserves that source snapshot. This is the returned mathematical version: the ten step lengths are exactly 1817, 780, 1165, 500, 799, 657, 1348, 1104, 771 and 941.

The parent retains every word of its statement and every maintainer-owned field. The argument is now distributed as follows:

| New obligation | Former steps inherited | Length of inherited argument |
| --- | --- | --- |
| free-linearization-tensor | 1-2 | 2597 |
| group-algebra-exact-forgetful | 3, 7-8, and the tensor-action part of 9 | 3617 plus the shared tensor-action sentence |
| pointed-free-deletion-contraction | 4-6, 9 (the contraction and exactness parts) | 2727 |
| parent assembly | 10, plus instantiation of the three obligations and the existing exact tensor comparison | 2488 total new proof |

The free node proves a normalized construction and tensor comparison, not another free-module definition. The action node applies to arbitrary equivariant modules and arbitrary condensed action parameters, not just this resolution. The contraction node applies to an arbitrary pointed condensed set, with no group action at all, and retains the actual insertion maps and all degree-zero identities. Each is a separate argument a different worker can undertake. None states the whole parent, none asserts projectivity, and none changes the coefficient category. All three are statement-only: proof [], proof_deps [], proof_origin null, status unsplit. Their intended arguments are preserved verbatim below, outside their statements.

## Searches and source checks

The item’s existing Mathlib searches and results were retained, read and checked against the ordinary bar complex in Mathlib/RepresentationTheory/Homological/Resolution.lean:145-162, 240-260, 393-445 and Condensed.profiniteFree in Mathlib/Condensed/Solid.lean:40-46. The search question for the unchanged item did not change. There was no retained sandbox searches.jsonl to overwrite. Every newly recorded search was run through the required msearch.py command, whose append-only log is searches.jsonl. research-results.json and search-*.txt retain full output, not invented search summaries. Each new node has LeanFinder (two phrasings), LeanSearch, Loogle and source grep. All services answered successfully on these queries.

For the free node, read ModuleCat.FreeMonoidal.μIso and its forward/inverse generator formulas at Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean:148-165; these give only the sectionwise ordinary-module part. Read SheafOfModules.free at Sheaf/Free.lean:40 and its freeHomEquiv:60: these are indexed by a fixed type, not a varying condensed set. PresheafOfModules.freeAdjunction is a presheaf construction. The remaining internal/sheafification/tensor identification is substantial. For the action node, read Rep.linearizationOfMulActionIso in RepresentationTheory/Rep/Basic.lean:1037: this is the ordinary abstract-group representation, not natural C(S,G)-actions. The CondensedMod hits assume an ordinary coefficient ring and do not identify the internal sheafified group algebra. For the pointed node, read ExtraDegeneracy.homotopyEquiv in AlgebraicTopology/ExtraDegeneracy.lean:415-440 and its input structure:78-94. It requires an already constructed augmented simplicial module and extra degeneracy, so does not supply in one line the specified internal free-module maps, the local generator formulas, and their tensor contractions. It is useful future implementation material, not an exact attachment.

Whole-DAG keyword/title/statement scans and blueprint_refs.py searches “free internal”, “homogeneous”, “group algebra”, “pointed”, “tensor products of free” and “equivariant modules” were made before creating nodes. The initial regular-expression query to blueprint_refs.py was literal and found nothing; it was followed by these literal semantic queries. The free-internal hit thm-weil-six-operations is the global six-functor package. Pointed hits concern étale neighbourhoods and torsors. No imported blueprint states the new facts. The ancestor command returns None through the inherited non-blueprint chain; the child blueprint references retain that exact null ancestor, prepend this item to via, and give the former proof steps and paragraph (3) as their precise places. No ancestor was invented.

I read the chapter record, the unit record and the current main-20261015 direct-images proof. Paragraph (3) is the open-direct-image context; it does not spell out the internal bar algebra. Thus the extracted work is explicitly agent-formulated. Read Stacks sites-modules.tex, Tag 03CY, label lemma-sheafification-presheaf-modules (815 onward), Tag 0GMW, label lemma-sheafification-tensor (3606 onward), and Tag 03EO, label lemma-internal-hom-adjoint-tensor (3949 onward). Also read the free-sheaf construction inside lemma-universal-module (5951 onward). These agree with the supporting nodes' universal properties; the internal extension is not attributed to Stacks as a theorem it did not state. Read the current blueprint statements lem-sfb-modobj-kernels, lem-sfb-modobj-cokernels and lem-sfb-modobj-abelian, especially that the monoid need not be commutative and that the latter two require B tensor - to preserve finite colimits.

## Not duplicates

- lem-sfb-condensed-free-linearization-tensor vs def-sfb-condensed-free-module-adjunction: the existing node defines the composite adjunction; the new theorem identifies it with sectionwise free-module sheafification and constructs the normalized product/tensor isomorphism.
- lem-sfb-condensed-free-linearization-tensor vs def-sfb-condensed-free-module-generators: canonical tuple generators are defined there; the new theorem is the sheafification and tensor comparison for arbitrary condensed sets.
- lem-sfb-condensed-free-linearization-tensor vs lem-pe-internal-section-tensor-comparison: the existing theorem identifies two module encodings and their tensors; it does not identify the fixed free object with F_X^# or construct the free product/tensor maps. Its general comparison is reused, including explicitly in parent step 1.
- lem-sfb-condensed-free-linearization-tensor vs lem-pc-sites-module-sheafification-interface: the latter gives the general sheafification adjunction; it does not state free-module realization or the product/tensor formula.
- lem-sfb-condensed-free-linearization-tensor vs lem-pc-sites-module-sheafification-tensor: the latter compares tensor and sheafification for presheaf modules; it does not construct the free-on-condensed-set functor or its local generator normalization.
- lem-sfb-condensed-free-linearization-tensor vs lem-weil-pbc-free-module-sheaf-sheafify-first: that lemma concerns a sheafification isomorphism of indexing presheaves for a constant ring; it does not assert this variable-ring tensor comparison.
- lem-sfb-condensed-group-algebra-exact-forgetful vs lem-sfb-modobj-kernels: generic monoid-module kernels assume the monoid and module category are given; the new theorem constructs the internal group algebra and identifies natural group actions with its modules.
- lem-sfb-condensed-group-algebra-exact-forgetful vs lem-sfb-modobj-cokernels: the existing theorem assumes a monoid with finite-colimit-preserving tensor; the new theorem supplies it and proves the action equivalence and exactness detection for condensed groups.
- lem-sfb-condensed-group-algebra-exact-forgetful vs lem-sfb-modobj-abelian: abelianness for an already supplied monoid does not supply the internal group algebra/action comparison or normalized linearization.
- lem-sfb-condensed-group-algebra-exact-forgetful vs def-sfb-condensed-action-module: the existing node defines natural section actions; it does not assert the group-algebra equivalence or exactness creation.
- lem-sfb-pointed-free-deletion-contraction vs lem-sfb-bar-resolution-cochains: the latter is an ordinary Z[G]-projective resolution with inhomogeneous differential; the new theorem is over a variable condensed ring for an arbitrary pointed condensed set and asserts specified tensor-compatible insertion maps, without projectivity or a group hypothesis.
- lem-sfb-pointed-free-deletion-contraction vs lem-sc-presheaf-free-nerve-exact-eval: positive-degree evaluated presheaf exactness does not give internal variable-ring free modules, the augmentation, specified contraction or arbitrary-module tensor contraction.
- lem-sfb-pointed-free-deletion-contraction vs lem-sc-presheaf-cech-sheaf-resolution: the existing abelian-sheaf Cech resolution gives exact sequences for Z-coefficients, not the specified universally tensor-contractible complex over a variable condensed ring.

- lem-sfb-condensed-free-linearization-tensor vs lem-pc-open-localized-module-sheafification: restriction to the open-localized site commutes with sheafification; it does not construct free modules on condensed sets or their product/tensor isomorphism.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-exterior-dual-pairing-functional: a determinant defines a dual section of a sheaf exterior power on a scheme; it says nothing about free modules on a condensed parameter.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-exterior-dual-pairing-local: an alternating map from dual sections to the dual exterior-power sections is characterized by a determinant; no free-parameter tensor comparison is asserted.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-exterior-sheaf-comparison: two exterior-power sheaf constructions on a scheme are identified, whereas the new theorem concerns the free condensed-set adjunction and its product/tensor comparison.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-exterior-sheaf-dual-ext: extensionality tests dual exterior sections on pure wedges over subopens; it does not identify the free internal module or its tensor.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-hom-tensor-comparison-natural: the tensor/sheafification comparison is natural for maps between already given module sheaves; it neither identifies the fixed free-on-condensed-set object with F_X^# nor constructs its product/tensor isomorphism.
- lem-sfb-condensed-free-linearization-tensor vs lem-sc-hom-tensor-section-natural: the unit-derived pure-tensor section comparison is natural for maps between module sheaves; the free functor and free-on-product isomorphism are not part of its statement.
- lem-sfb-condensed-free-linearization-tensor vs def-pe-finite-discrete-presentation-encoding: this defines supplied encodings between pulled-back coefficient-module categories and constant-coefficient categories on a scheme; the new theorem constructs a free module and tensor isomorphism on the profinite point, not such an encoding.
- lem-sfb-condensed-free-linearization-tensor vs def-sfb-constant-module-coefficient-transport: this defines coefficient transport between two constant-ring sheaf presentations; it does not assert a free-module theorem for varying condensed-set parameters.
- lem-sfb-condensed-free-linearization-tensor vs def-sfb-scalar-extension-pure-tensor-section: this defines a pure-tensor section for extension of scalars along a ring-sheaf map, without asserting a free product/tensor isomorphism.
- lem-sfb-condensed-free-linearization-tensor vs def-weil-pbc-ideal-module-quotients: this defines sheafified quotients by ideal subsheaves and their scalar maps; the new theorem has no ideal or quotient and identifies the free functor on products.

## Review by O3

I checked the unchanged item against both its precise existing Lean specification and its old ten-step proof, including the internal-to-section correction added by the maintainer. The theorem body remains sorry; I do not treat its statement as evidence of a finished proof. I read the current main-20261015 source paragraph and the three Stacks labels named above. The free node's statement is exactly the old free-presheaf construction, the universal generator formula and the two inverse tensor maps, with the internal comparison made explicit. The group-algebra node states the old linearization and action equivalence for general modules and the exactness-creation conclusion; it does not mistake the possibly noncommutative group algebra for a commutative coefficient ring. The pointed node retains the old differential, actual insertion homotopy, degree-zero identities and tensor exactness. Its generalization replaces 1 in G by a specified global point e in X; each cancellation and insertion calculation depends only on that point, so no group property was lost.

Parent step 1 cites the free node for exactly its sheafified free realization, normalized tensor-product formula and generator extensionality. It cites lem-pe-internal-section-tensor-comparison for exactly its exactness and tensor/unit comparison; that node leaves underlying abelian sheaves and maps unchanged. The needed site is small within the coefficient universe, A is commutative, and coherent condensed sheafification carries the stated monoidal structure. The old missing-comparison fault has not returned.

Parent step 2 cites the group-algebra node for linearization of internal actions and equivariant maps, and the additive tensor functor with trivial T. The coordinate-deletion identity is written in the step itself. The target of the augmentation is A with trivial action. No equivariant contraction is asserted. Parent step 3 cites the pointed node for the displayed d-squared-zero and contraction identities, underlying exactness, and arbitrary-T tensor exactness. Its pointed-set hypothesis is met by the constant identity section of the profinite group. It cites the group-algebra node for reflection of exactness, including the epimorphic augmentation. These are sentences of those nodes' statements, not deductions silently borrowed from their future proofs. Parent step 4 retains the complete explicit inverse coordinate formula and its continuity and equivariance calculation; the free node supplies the product/tensor isomorphism and functoriality, and the action node supplies equivariant linearization. At n=0 the second parameter is terminal, so the supplied free-unit isomorphism gives exactly the unit presentation. citations.json has one verbatim excerpt for every step/node pair, selected from the part used there.

For the extracted action argument, I reopened every existing statement it had used: sk-def-sfb-module-objects really allows an arbitrary monoid; lem-pc-sites-module-sheafification-bilinear-extension really extends bilinear maps in both variables; lem-pc-sheaf-modules-tensor-closed supplies the adjunction and additivity; lem-sfb-modobj-kernels/cokernels/abelian give the uniquely induced actions under their stated hypotheses. The required B tensor - preservation is not assumed: the preserved old argument derives its colimit universal property from that adjunction. For the free construction, lem-pc-sites-module-sheafification-interface gives the actual sheafification adjunction and lem-pc-sites-module-sheafification-tensor gives its balanced-tensor comparison. For the contraction, lem-pur-ringed-site-module-category-abelian applies because the site is small and A is a ring sheaf. Each of these is supporting material for an unsplit child, not an omitted uncited invocation in the parent.

I checked B1-B10: new statements introduce all their objects, define the group algebra multiplication and its possibly noncommutative nature, cite the existing definition of every internal-module/free/tensor notion, use single TeX escapes, state propositions rather than proof sketches, and contain no proof steps or proof dependencies. No Mathlib leaf was claimed without an exact declaration. Whole-DAG and blueprint duplicate checks and actual logged searches were completed. I checked C1-C8 against the four steps as above: no source tag substitutes for a node citation; the new parent no longer invokes the old lower-level argument; no dependency on a child reaches the parent; off-unit internal/section comparison remains explicitly declared as a generic tool use. The three new children inherit the parent's unit. D1-D4 were checked by their differing scopes: construction for all condensed sets, group algebra for all action modules, and contraction for pointed sets without groups. Each carries a real separate argument, not one copy of the full target. D5 has no hidden “details omitted” in the parent: its non-elementary content is now explicitly delegated to unsplit statements.

Small cases for E1-E7: A=0 makes all free modules and tensor maps zero, with the unique unit isomorphism. X=empty in the free theorem gives zero on either side of the product/tensor formula, whereas the pointed theorem intentionally requires a global point and so excludes a nontrivial empty X. X=1 in the contraction theorem gives alternating identity/zero maps, epsilon=id and the stated degree-zero identity. At n=0, d_1h_0[x]=[x]-[e] and h_-1 epsilon[x]=[e]. For the trivial group, B=A and the action equivalence reduces to identity. For noncommutative finite G (for example S_3), B is only a monoid object, which the cited kernels/cokernels lemmas permit. For T=0 and for a non-flat T such as Z/2 over constant Z, contraction identities still survive the additive tensor functor; no preservation of arbitrary exact sequences is asserted. Restrictions carry e to e and every continuous tuple map to its restriction, so the formula is sheaf-natural; no false global lifting of arbitrary sheafified sections to generators is used. No statement dispute or source counterexample was found.

The first substantive dry run requested eleven additional same-Tag-03CY duplicate comparisons. I opened all eleven statements and added explicit differences under Not duplicates; their subjects are localization, exterior powers, tensor naturality, coefficient encodings, or ideal quotients, not the new free-parameter construction.

I corrected the one structural fault requested by the return: the workload is now in three comparable statement-only nodes, and the parent is below 3000 characters. No non-elementary assembly step exceeds 2000 characters (lengths 388, 481, 541, 1078). The original arguments, their citations and sources are retained below verbatim so future workers can recover every calculation without consulting a vanished attempt. No mathematical hypothesis was changed and no SGA route is used.

## Preserved arguments for the new obligations

These are report material for future workers, not proofs inserted into the unsplit node files. A child worker will write and verify its own proof, reusing these exact arguments and the cited statements. Step 10 remains word-for-word in the new parent's coordinate calculation except that numbered cross-references were replaced by the new node citations.

### Former step 1 — lem-sfb-condensed-free-linearization-tensor

First transfer the statement to sheaves of modules. Since $A$ is a commutative condensed ring, its reconstructed section-ring sheaf is $A$ itself, and [def-weil-pbc-internal-abelian-sheaf-module-equivalence] gives an equivalence $E_A$ from internal $A$-module objects [sk-def-sfb-module-objects] to $\mathcal M=\operatorname{Mod}(A)$, sheaves of $A$-modules, leaving underlying abelian sheaves, sections and morphisms unchanged; in particular it commutes with the forgetful functors to condensed sets, so it carries free internal modules to free objects of $\mathcal M$, and it carries kernel, image and cokernel subobjects to the same subsheaves. By [lem-pe-internal-section-tensor-comparison], $E_A$ is exact and carries the internal relative tensor product to $\otimes_A$ of $\mathcal M$, with $E_A(A)=A$ and pure tensors $m\otimes n\mapsto m\otimes n$, compatibly with associators and unitors. Hence every assertion of the statement, including the tensored complexes, may be proved in $\mathcal M$, which all remaining steps do. For a condensed set $X$, form the presheaf $F_X(S)=A(S)[X(S)]$ of free $A(S)$-modules; restriction sends $a[x]$ to $a|_T[x|_T]$. By [lem-pc-sites-module-sheafification-interface], its module sheafification $F_X^\#$ exists and maps from it to an $A$-module sheaf $M$ are exactly presheaf-module maps $F_X\to M$. Such a map is uniquely specified by a natural assignment $x\mapsto m_x\in M(S)$, by the formula $\sum a_x[x]\mapsto\sum a_xm_x$. These assignments are exactly maps of condensed sets $X\to M$. Thus $F_X^\#$ realizes the free module $A[X]$ specified in the statement. For any map $u:X\to Y$, its linearization is $[x]\mapsto[u(x)]$; equalities between linearized maps can be checked on these generators before sheafification. For the terminal sheaf $1$, $F_1=A$, so $A[1]=A$.

Uses: def-weil-pbc-internal-abelian-sheaf-module-equivalence, lem-pe-internal-section-tensor-comparison, lem-pc-sites-module-sheafification-interface.

Source: literature/stacks-project/sites-modules.tex; Tag 03CY, lemma-sheafification-presheaf-modules; free-module construction in proof of lemma-universal-module, applied to A[X].

### Former step 2 — lem-sfb-condensed-free-linearization-tensor

For condensed sets $X,Y$, sectionwise bilinear extension gives inverse maps
$$A(S)[X(S)]\otimes_{A(S)}A(S)[Y(S)]\ \rightleftarrows\ A(S)[X(S)\times Y(S)],\qquad [x]\otimes[y]\longleftrightarrow[(x,y)].$$
The inverse respects the tensor relations because $(\sum a_x[x],\sum b_y[y])$ is sent to $\sum_{x,y}a_xb_y[(x,y)]$; both composites are the identity on generating tensors or generators. These maps commute with restriction. Sheafify and use [lem-pc-sites-module-sheafification-tensor] with ring presheaf $A=A^\#$ to obtain
$$A[X]\otimes_A A[Y]\cong A[X\times Y].$$
The displayed maps, their inverses and their compatibility with maps of $X,Y$ are retained. This is a calculation with free modules, not an assertion that their sections after sheafification are sectionwise free.

Uses: lem-pc-sites-module-sheafification-tensor.

Source: literature/stacks-project/sites-modules.tex; Tag 0GMW, lemma-sheafification-tensor.

### Former step 3 — lem-sfb-condensed-group-algebra-exact-forgetful

If a condensed group acts on $X$, linearize its action map $\underline G\times X\to X$ and use the isomorphism of step 2 to obtain $A[\underline G]\otimes_A A[X]\to A[X]$. On generators this is $[g]\otimes[x]\mapsto[gx]$; the group laws are verified on $[g]\otimes[h]\otimes[x]$. Consequently the diagonal actions on $P_n$ are internal $A$-linear actions. Deleting coordinate $i$ is a continuous equivariant map $G^{n+1}\to G^n$, since deletion of $(gg_0,\ldots,gg_n)$ is $g$ times the deleted tuple. Its linearization is therefore an equivariant module map. Their signed sum is $\partial_n$. The map to $A=A[1]$ induced by $\underline G\to1$ is the stated augmentation and is equivariant for the trivial action. For actions on an arbitrary module sheaf, sectionwise extension on $A(S)[G(S)]\times M(S)$ is bilinear and natural; [lem-pc-sites-module-sheafification-bilinear-extension] uniquely extends it after sheafifying the first factor, since the second factor and target are already sheaves. The tensor universal property then gives the corresponding action map. Its uniqueness justifies checking equivariance on group generators and arbitrary module sections.

Uses: lem-pc-sites-module-sheafification-bilinear-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 4 — lem-sfb-pointed-free-deletion-contraction

On a generator $[g_0,g_1]$, $\epsilon\partial_1=1-1=0$. In $\partial_n\partial_{n+1}$, fix two original indices $0\le i<j\le n+1$. Deleting $j$ and then $i$ contributes sign $(-1)^{j+i}$; deleting $i$ and then original $j$ (now at index $j-1$) contributes $(-1)^{i+j-1}$. The resulting tuple is identical and the coefficients sum to zero. Every ordered double deletion belongs to exactly one such pair. Thus the composite is zero on every generator and hence zero as an internal module map by step 1.

Uses: elementary identities from previous constructions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 5 — lem-sfb-pointed-free-deletion-contraction

Forget the $G$-action for the following maps. The continuous insertion $G^{n+1}\to G^{n+2}$, $(g_0,\ldots,g_n)\mapsto(1,g_0,\ldots,g_n)$, gives $h_n:P_n\to P_{n+1}$. Set $h_{-1}:A\to P_0$ to be $a\mapsto a[1]$. Then $\epsilon h_{-1}=\mathrm{id}_A$. Expanding the differential on an inserted tuple gives, for $n\ge1$,
$$\partial_{n+1}h_n[g_0,\ldots,g_n]=[g_0,\ldots,g_n]-h_{n-1}\partial_n[g_0,\ldots,g_n].$$
Indeed deleting the inserted $1$ is the first term, and deleting original coordinate $i$ has sign $(-1)^{i+1}$, the negative of its sign in $h_{n-1}\partial_n$. In degree zero the expansion is $\partial_1h_0[g]=[g]-[1]$, so $\partial_1h_0+h_{-1}\epsilon=\mathrm{id}_{P_0}$. These generator equalities give identities of sheaf-module morphisms. No equivariance of $h_n$ is required or claimed.

Uses: elementary identities from previous constructions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 6 — lem-sfb-pointed-free-deletion-contraction

The underlying module category is abelian by [lem-pur-ringed-site-module-category-abelian], applied to the small site in the statement and its commutative ring sheaf $A$. Put $d_0=\epsilon$ and $d_n=\partial_n$ for $n\ge1$. For the kernel inclusion $k_n:K_n\to P_n$, step 5 yields
$$k_n=d_{n+1}h_nk_n+h_{n-1}d_nk_n=d_{n+1}h_nk_n.$$
Thus $k_n$ factors through $d_{n+1}$, so $\ker d_n\subseteq\operatorname{im}d_{n+1}$. The reverse inclusion follows from step 4. This proves exactness at every $P_n$ in underlying modules. The identity $\epsilon h_{-1}=\mathrm{id}_A$ proves that the augmentation is a split epimorphism there, giving exactness at $A$ as well.

Uses: lem-pur-ringed-site-module-category-abelian.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 7 — lem-sfb-condensed-group-algebra-exact-forgetful

To justify exactness in equivariant modules, set $B=A[\underline G]$ in $\mathcal M=\operatorname{Mod}(A)$. Step 2 linearizes group multiplication to $B\otimes_A B\to B$ with $[g]\otimes[h]\mapsto[gh]$, and gives unit $A\to B$, $1\mapsto[1]$. Associativity and unity are generator equalities. An internal linear $G$-action on $M$ gives the $B$-module action $[g]\otimes m\mapsto gm$ by linear extension; conversely restrict a $B$-module action to the generators $g\mapsto[g]$. These constructions are inverse because linear maps from a free module are determined on its generators; the module laws become the group-action laws, and $g^{-1}$ provides the inverse action. The morphism conditions also agree. Thus equivariant modules and their forgetful functor are the $B$-module objects [sk-def-sfb-module-objects] in $\mathcal M$ and their forgetful functor. Here $B$ is a monoid object; it is not assumed commutative. More explicitly, the map $A(S)[G(S)]\times M(S)\to M(S)$ sends $(\sum a_g[g],m)$ to $\sum a_g(gm)$ and is $A(S)$-bilinear. It is natural in $S$. By [lem-pc-sites-module-sheafification-bilinear-extension] it uniquely extends to $B\times M\to M$ as a bilinear sheaf map, hence to $B\otimes_A M\to M$. This construction, rather than global lifting of arbitrary sections to generators, supplies the claimed action and its uniqueness.

Uses: sk-def-sfb-module-objects, lem-pc-sites-module-sheafification-bilinear-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 8 — lem-sfb-condensed-group-algebra-exact-forgetful

The tensor of $\mathcal M$ is additive and closed by [lem-pc-sheaf-modules-tensor-closed]. For fixed $B$, its tensor functor preserves finite colimits: if $L=\operatorname{colim}_i M_i$, the adjunction identifies maps $B\otimes_A L\to N$ with maps $L\to\mathcal Hom_A(B,N)$, hence with compatible maps $M_i\to\mathcal Hom_A(B,N)$, hence with compatible maps $B\otimes_A M_i\to N$. This proves the colimit universal property. In particular [lem-sfb-modobj-abelian] makes the category of $B$-module objects abelian. Then [lem-sfb-modobj-kernels] and [lem-sfb-modobj-cokernels] apply to $B$ in $\mathcal M$: equivariant kernels and cokernels are computed in underlying modules, with their uniquely induced actions. Images, being kernels of cokernels, are computed there as well. If the underlying image and kernel coincide, their action structures agree by uniqueness on the same subobject; the resulting identification is equivariant. Similarly a zero underlying cokernel is a zero equivariant cokernel. Consequently the exactness and augmentation surjectivity proved in step 6 hold in equivariant modules.

Uses: lem-pc-sheaf-modules-tensor-closed, lem-sfb-modobj-kernels, lem-sfb-modobj-cokernels, lem-sfb-modobj-abelian.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 9 — lem-sfb-pointed-free-deletion-contraction (tensor-action sentence also inherited by lem-sfb-condensed-group-algebra-exact-forgetful)

Let $T$ be any internal $A$-module with trivial action. By [lem-pc-sheaf-modules-tensor-closed], $-\otimes_A T$ is an additive functor and $A\otimes_A T\cong T$. Apply this functor to the identities of steps 4 and 5. The maps $h_n\otimes\mathrm{id}_T$ and $h_{-1}\otimes\mathrm{id}_T$ satisfy the same contracting identities for the augmented tensored complex, with augmentation to $T$. The kernel-factorization argument of step 6 now proves exactness in underlying modules, including the split surjectivity onto $T$. The tensor actions $g(p\otimes t)=(gp)\otimes t$ make the differentials and augmentation equivariant. Step 8 proves exactness in equivariant modules. This argument uses additivity and the explicit contraction, so it imposes no flatness condition on $T$.

Uses: lem-pc-sheaf-modules-tensor-closed.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

### Former step 10 — parent step 4

Define $c_n:G^{n+1}\to G\times G^n$ by
$$c_n(g_0,\ldots,g_n)=(g_0,g_0^{-1}g_1,\ldots,g_{n-1}^{-1}g_n).$$
Its inverse sends $(a,b_1,\ldots,b_n)$ to $(a,ab_1,ab_1b_2,\ldots,ab_1\cdots b_n)$. The composites are identities by cancellation of adjacent inverse factors. Both maps are continuous because multiplication and inverse in $G$ are continuous and only finitely many coordinates occur. For $u\in G$, $(ug_{i-1})^{-1}(ug_i)=g_{i-1}^{-1}g_i$, while the first coordinate becomes $ug_0$; thus $c_n$ is equivariant for left translation on the first factor and trivial action on the other factors. Linearizing $c_n$ and its inverse, then applying the product/free-tensor identification of step 2, gives
$$P_n\cong A[\underline G]\otimes_A A[\underline G^n]$$
with precisely the stated action. At $n=0$, $G^0=1$ and this is the unit isomorphism $A[\underline G]\cong A[\underline G]\otimes_A A$. No projectivity assertion enters the construction.

Uses: elementary identities from previous constructions.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md; Paragraph (3), open direct image: agent expansion of the internal homogeneous bar input.

## Unfinished work

No part of this stage-1 repair is intentionally left incomplete. The three new unsplit obligations are the requested parallel work items; no proofs or Lean implementations for those children are part of this delivery. Dry-run and push results follow below once completed.
