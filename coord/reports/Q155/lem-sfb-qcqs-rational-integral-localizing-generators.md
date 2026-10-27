# Q155 stage-1 repair report

1. Files written: the item JSON, four new statement-only JSON nodes, and citations.json. The item statement is byte-for-byte unchanged; its proof is now 2018 characters in four steps (was 10807 in fourteen).

- lem-sfb-qcqs-integral-scalar-extension-ctf: statement, unsplit; no Mathlib match in five executed searches (two LeanFinder phrasings, LeanSearch, Loogle, source grep).
- lem-sfb-qcqs-lisse-stratified-integral-lattices: statement, unsplit; no Mathlib match in five executed searches (two LeanFinder phrasings, LeanSearch, Loogle, source grep).
- lem-sfb-qcqs-constructible-integral-lattice-tree: statement, unsplit; no Mathlib match in five executed searches (two LeanFinder phrasings, LeanSearch, Loogle, source grep).
- lem-sfb-qcqs-lattice-tree-reconstruction: statement, unsplit; no Mathlib match in five executed searches (two LeanFinder phrasings, LeanSearch, Loogle, source grep).

2. Attachments: none. The upstream WeilConjectures notion/tag search found no exact declaration. The local Sheaf.Paper.QcqsRationalIntegralLocalizingGenerators module contains the two corresponding theorem proofs as sorry at lines 236 and 381; these are not attachments.

3. WANTED: none for this repair. All cited sources were available locally.

4. Returned fault repaired: the mathematical argument was too large for one worker. It is now divided into four independent statement-only tasks of comparable argument size. The conditional refinement task does not duplicate the lattice-existence task: it takes any chosen lattice partitions and supplies actual scheme-theoretic factoring refinements. Reconstruction takes an already supplied finite tree and leaf models; it does not prove their existence or the bounded-complex theorem. The last truncation induction remains in the item.

5. Unfinished: proofs of the four new unsplit nodes, intentionally left to subsequent parallel workers. No Lean was written or compiled.

## Review by Q155

I read the current repository item and its chapter and compactification-coherence unit, then compared the returned 14-step proof with the requested repair. The sandbox initially contained no retained files or report, so the current repository JSON is the retained head used here. Its statement already has the finite-subextension-valued algebraic-closure correction; I kept it verbatim and did not revive the all-norm-continuous coefficient clause. The existing source and split metadata recording that earlier dispute remain in the item except for the worker-owned split report. No new statement dispute is introduced.

I read the current blueprint refinement proof (2), the lattice proof (rank, the lattice scheme, and the trace image), and the lisse finite-coefficient descent proof (1). I also read Hemo–Richarz–Scholbach Theorem 7.7 and the surrounding coefficient conventions: its derived-lisse theorem is context, not a substitute for the finite constant scalar-model assertion here. The scalar task keeps the module-object/section-ring comparison and the flat-resolution Tor argument as separate obligations in its handoff below. Its statement includes flatness, exact termwise realization, the cohomology identification, finite free rational models and the same Tor interval; it is stronger and more precise than just the first clause of the item.

For the lattice task I read Stacks Tag 03S0, etale-cohomology.tex lemma-etale-stratified-finite, including its proof. Both source and target must be qcqs, which the finite affine subcover of the separated etale lattice scheme supplies. The statement retains actual embedded lattices spanning the rational module, not merely an abstract locally free image. The local trace is the sum over the nonempty finite sheets; no degree is inverted. This is why the argument also applies when the degree is divisible by ell. Finite-subextension descent is used only on a lisse sheaf over a qcqs leaf, never on the input complex or connecting arrows. The rank decomposition is finite and clopen, with zero rank allowed.

For the refinement task I read the full statement of lem-fix-constructible-open-closed-refinement. It gives qcqs vertices, quasi-compact branch morphisms, and genuine morphisms to the original strata. The task retains both uses of refinement, before the lisse lattice argument and afterwards, and the pullback of the integral module and its actual scalar-extension isomorphism. It does not infer scheme factorization from set-theoretic containment, or assume affine intersections on a merely quasi-separated scheme.

For reconstruction I read Stacks Tag 09AH, proetale.tex lemma-ses-associated-to-open and proof, and the ringed open/closed, Tor-local-detection, tensor-pullback and detection node statements. The quasi-compact open hypothesis holds at every edge. The task includes preservation of finite scalar models, the zero complementary model, preservation of flatness, both scalar-comparison maps, the branch integral models and finite triangle reconstruction. It assumes the flatness supplied by the scalar task. No non-elementary preservation statement is discarded as an elementary step.

The new assembly uses exactly these statement clauses. Step 1 uses the scalar task's finite-model and same-Tor-interval assertion and its flatness clause. Step 2 uses the refinement task first for lisse leaves, then the lattice task for the finite lattice partitions, then the conditional refinement assertion for the final integral-model leaves. Step 3 uses the reconstruction task's integral branch complexes and derived scalar isomorphisms and its finite-triangle conclusion. Step 4 reads the definition of bounded constructibility and uses the actual displayed truncation triangles from lem-weil-pbc-truncation-triangle. The lower and upper cohomology bounds make the first truncation zero and the last isomorphic to K. All connecting maps stay in the ambient ordinary derived category. I copied the exact relevant statement passages into citations.json and checked that each occurs verbatim.

Small cases checked: empty V, a tree with a single vertex, zero modules, rank-zero leaves, repeated ranks, and cohomology in a single degree. The zero integral module supplies empty leaves; a one-vertex tree has the identity branch extension; a sheaf in one degree needs no extra truncation extensions. For a nodal curve with unbounded integral monodromy, the lattice task asserts stratified lattices rather than a global lattice, as required. No task adds a Noetherianity, characteristic, dimension or invertibility hypothesis. I checked all new node statements introduce their objects, cite the definitions they use, contain no proof steps, and preserve the actual derived isomorphism in the branch comparison. The only per-degree cohomology assertion is a consequence included in the scalar theorem alongside its derived functor identification.

I checked delivery-errors B–E: statement-only form and self-contained hypotheses (B); exact statement citations, all non-elementary obligations and no new cycles (C); four strictly smaller arguments rather than one renamed whole theorem (D); the qcqs, finite-sheet, coefficient topology, scheme-factorization and finite-Tor conditions (E). The item has no proof step longer than 2000 characters. I searched the whole DAG by the lattice, tree, scalar-constructibility and Stacks-tag concepts, searched blueprint_refs across all chapters, and read the nearby candidate statements listed next. Mathlib search output is retained unmodified in the search-result files; searches.jsonl is the command's own log. The first dry run requested explicit comparisons with the other nodes using Tags 03S0 and 09AH. I opened all twenty additional statements, distinguished their exact conclusions and hypotheses below, and retained the four tasks because none is stated by one of those nodes. The successful search services returned ordinary algebraic module and scheme results and generic sheaf finite-presentation definitions, not any of these four results.

## Not duplicates

- lem-sfb-qcqs-integral-scalar-extension-ctf vs lem-sfb-extend-scalars-bounded-constructible: That existing theorem only asserts bounded constructibility for integral-to-finite-field extension. This task also identifies exact termwise scalar extension and its cohomology, treats the finite-subextension-valued closure, and preserves each specified Tor interval.
- lem-sfb-qcqs-integral-scalar-extension-ctf vs det-prop-scalar-six-ctf: The existing package assumes the standing separated finite-type characteristic-p setting. This task applies on arbitrary qcqs schemes and gives exact cohomology and same-interval Tor control.
- lem-sfb-qcqs-integral-scalar-extension-ctf vs lem-sfb-constructible-exact-scalar-triangulation: The existing statement assumes a Noetherian underlying space and starts at rational E coefficients. This task starts at integral coefficients on any qcqs scheme and includes finite-model and Tor assertions.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs sk-lem-stratified-lattice: The imported theorem assumes standing separated finite-type schemes over the fixed positive-characteristic field. This task has arbitrary qcqs schemes and also finite-subextension-valued algebraic-closure lisse inputs.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs det-lem-stratified-lattice-trace: The trace theorem assumes a Noetherian base and an already supplied finite etale lattice cover. This task constructs a constructible lattice partition on any qcqs base, with lisse-object coefficient descent.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs det-lem-stratified-lattice-scheme: The lattice-scheme theorem constructs a separated etale lattice scheme and universal lattice for constant-rank finite-field inputs. It does not produce finite constructible lattice partitions by finite etale trace.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-sfb-continuous-finite-etale-trace-lattice: That theorem assumes an existing finite etale cover and only proves the trace image is locally free, explicitly without rationalization of its inclusion. This task obtains a partition and embedded lattices whose actual inclusion spans the rational module.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-etale-stratified-finite: Tag 03S0 only makes an already given etale morphism finite on strata. It does not produce coefficient-field descent, integral lattices, trace images, or spanning inclusions.
- lem-sfb-qcqs-constructible-integral-lattice-tree vs lem-fix-constructible-open-closed-refinement: The generic refinement theorem supplies factoring morphisms for given scheme partitions. This task also supplies lisse restrictions from scalar-field local models and transports given integral models and their scalar isomorphisms along a second attached refinement.
- lem-sfb-qcqs-constructible-integral-lattice-tree vs lem-sfb-pullback-constant-model-constructible: Pullback stability does not construct a finite binary open/closed tree or refine a family of lattice-bearing partitions with actual factoring morphisms.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-sfb-scalar-model-immersion-extension: That statement assumes Noetherian schemes and only preserves constructibility. This task preserves flatness, proves coefficient comparison and integral branch Tor bounds, and gives finite-tree reconstruction on arbitrary qcqs schemes.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-sfb-bounded-finite-model-generation: The older generation criterion assumes Noetherian underlying space and given generator membership. This task works on a supplied qcqs tree and constructs integral branch generators with a derived scalar isomorphism.
- lem-sfb-qcqs-lattice-tree-reconstruction vs det-sf-flat-model-generation: That theorem has finite discrete coefficients on Noetherian schemes. This task is ordinary continuous integral/rational coefficient reconstruction on a supplied qcqs tree.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-proetale-ringed-open-closed: Tag 09AH supplies exact edge operations and a localization sequence, not their constructibility/flatness/scalar comparisons or the resulting integral branch models and finite-tree reconstruction.

- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-closed-immersion-scalar-change: Only the scalar/closed-direct-image comparison for one immersion is asserted there. This task additionally has open edges, flatness and finite-model preservation, integral branch Tor bounds, and finite-tree reconstruction.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-condensed-open-closed-recollement: The bounded-below recollement statement supplies adjunctions and triangles for one decomposition, without integral lattices, coefficient comparison, finite-model preservation or Tor control for branch extensions.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-continuous-constructible-supported: The supported-constructibility theorem assumes a Noetherian base and proves neither flatness nor branch scalar comparison and finite reconstruction on an arbitrary qcqs tree.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-continuous-module-localization: This is the exact adjunction unit/counit sequence for one continuous coefficient ring and one decomposition; it does not construct integral branch models or prove scalar comparison and finite Tor bounds.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-integral-model-open-closed-pieces: The existing two-piece theorem assumes a noetherian finite-dimensional base with ell invertible. This task has arbitrary qcqs trees, includes algebraic-closure finite-valued coefficients and flat branch models, and gives a derived isomorphism and finite reconstruction.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-localization-equivalence-transport: This is abstract transport of adjunctions and exactness across equivalences. It asserts no constructibility, flatness, coefficient extension or integral-model theorem.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-noetherian-stratum-detection: That theorem only detects vanishing from restrictions to strata of a Noetherian scheme. It does not construct branch extensions or integral scalar models and does not imply their Tor bounds.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-proetale-abelian-closed-support: This identifies an abelian sheaf supported on a closed subset with its closed pushforward. It does not prove preservation of flatness or finite scalar models, scalar comparison, or reconstruction from a lattice tree.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-proetale-closed-underived-projection: This is the ordinary projection formula for one closed immersion, without tree construction, open edges, constructibility or flatness assertions, integral branch models or their finite reconstruction.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-proetale-ringed-localization-sequence: This states exactness of the two ringed localization maps for one pair. The new task also treats branch scalar comparison, preservation of flat finite-model modules and integral branch objects of Tor amplitude zero.
- lem-sfb-qcqs-lattice-tree-reconstruction vs lem-weil-pbc-wcontractible-closed-localization: This constructs a pro-etale covering and localized ring near a closed subset of an affine scheme. It makes no assertion about module coefficients, integral branch extensions or derived reconstruction.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-per-noetherian-constructible-galois-partition: This is a finite etale Galois trivialization theorem for discrete constructible sheaves on Noetherian schemes with Noetherian scalar rings. The new task concerns continuous rational coefficients and embedded integral lattices on arbitrary qcqs schemes.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-affine-basic-set-difference: This is Boolean subtraction of affine basic constructible subsets. It states no lattice or sheaf result.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-affine-basic-sets-disjoint-refinement: This disjointifies finitely many affine basic subsets. It has no module sheaves, coefficient descent, or embedded integral lattices.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-constructible-stratification-assembly: This combines existing local stratifications and predicates. It does not construct a lattice in any rational lisse module or prove a spanning inclusion.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-etale-affine-cover-gluing: This makes a given etale affine cover finite etale on strata and proves separatedness. It does not construct integral lattices, their trace images or coefficient descent.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-etale-stratification-local-gluing-core: This produces a global scheme stratification factoring through given local strata. It asserts no coefficient descent or existence of integral lattices.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-etale-stratification-local-gluing: This glues already available finite-etale stratifications of a given etale morphism. The new task starts with a lisse rational module and produces actual integral lattices spanning it.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-immersion-affine-constructible-pieces: This decomposes an immersed constructible subset into affine scheme pieces, with no module-sheaf, rational coefficient or lattice assertions.
- lem-sfb-qcqs-lisse-stratified-integral-lattices vs lem-weil-pbc-lisse-lattice-reduced-open: The existing theorem assumes a nonempty reduced noetherian finite-dimensional scheme with ell invertible, and only supplies a lattice on some nonempty open. The new theorem permits any qcqs scheme and supplies a finite constructible partition covering it, also for finite-valued closure coefficients.

## Complete retained argument and task allocation

The following are the original proof paragraphs, verbatim, with their citations and source locations. They are a handoff for the workers of the statement-only tasks, not proof steps installed in those nodes. No argument has been shortened, summarized away or replaced by an unproved adjective. Old step 14 remains in the item, with its step numbers updated.

### lem-sfb-qcqs-integral-scalar-extension-ctf

Retained old steps 1, 2, 3; original argument length 2490 characters.

Old step 1:

Work with the section-ring sheaves of the pulled-back ring objects. The equivalence [lem-sfb-module-object-ringed-site-derived-comparison] leaves underlying sheaves and maps unchanged, and [lem-pe-internal-section-tensor-comparison] identifies relative tensor, flatness and K-flatness. Thus finite scalar presentations, cohomology, Tor bounds and the specified derived scalar extensions have exactly their ringed-site meanings. At the end this equivalence transports the argument back to module objects. It preserves ambient coproducts by their universal property; all categories and coproducts use [def-weil-size-convention].

Uses: lem-sfb-module-object-ringed-site-derived-comparison, lem-pe-internal-section-tensor-comparison, def-weil-size-convention

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Coefficient conventions, before the lattice construction"}

Old step 2:

For every scheme $T$, $A_T\to F_T$ is a flat localization by [det-prop-sfb-qlbar-colimit-x-invert-ell]. For the finite-subextension-valued algebraic closure, $F_T\to\Lambda_T$ is flat by [lem-sfb-qlbar-flat]. Their composite is flat: its tensor functor is the composite of the two exact scalar-extension functors, by $(b\otimes f)\otimes m\mapsto b\otimes fm$ and its inverse $b\otimes m\mapsto(b\otimes1)\otimes m$. These maps follow directly from the balancing relations. Consequently $T_{F,T}$ is exact termwise scalar extension, triangulated by [lem-sf-exact-functor-derived-triangulated], and its cohomology is the scalar extension of the original cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]. Only the finite-valued algebraic-closure coefficient is used here.

Uses: det-prop-sfb-qlbar-colimit-x-invert-ell, lem-sfb-qlbar-flat, lem-sf-exact-functor-derived-triangulated, lem-weil-pbc-exact-functor-complex-cohomology

Source: {"document": "literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf", "place": "Rationalization and finite-subextension scalar extension"}

Old step 3:

Let $J\in D_{\mathrm{ctf}}(V,A)$. Each local scalar model of each $H^q(J)$ has the two-term finite-free scalar resolution of [lem-sfb-finite-constant-model-two-term-free-resolution]. After step 2 its scalar matrix is over the field $\Lambda(*)$; its cokernel is a finite-dimensional vector space, so its realized cokernel is finite free. Hence $H^q(T_{F,V}J)$ has finite constant models on the same finite constructible stratification. Boundedness follows from the cohomology identification in step 2. For a Tor interval $[a,b]$ of $J$, [lem-pe-coefficient-tor-flat-model] supplies a flat complex supported in $[a,b]$. Base change carries flat modules to flat modules: tensoring the base-changed module with an arbitrary target-module sheaf equals tensoring the original module with that sheaf after scalar restriction, by the same balancing relations. The base-changed flat complex therefore has the same support and represents $T_{F,V}J$ by [lem-pur-derived-change-of-rings]. Apply the Tor/flat-model criterion again. This proves $\mathcal G_V\subset D_{\mathrm{ctf}}(V,\Lambda)$.

Uses: lem-sfb-finite-constant-model-two-term-free-resolution, lem-pe-coefficient-tor-flat-model, lem-pur-derived-change-of-rings

Source: {"document": "literature/hemo-richarz-scholbach-constructible-sheaves_arXiv-2305.18131.pdf", "place": "Generator constructibility and finite Tor bounds"}

### lem-sfb-qcqs-lisse-stratified-integral-lattices

Retained old steps 5, 6, 7, 8; original argument length 2805 characters.

Old step 5:

On a qcqs leaf $T$, the lisse module is already over $E_T$ when $\Lambda=E$. When $\Lambda=\Omega^{\mathrm{fin}}$, apply clause (1) of [det-lem-coefficient-finite-descent-lisse] on this qcqs $T$, obtaining a finite subextension $F$ and lisse $F_T$-module $L$ whose extension is $M|_T$. This result applies to lisse objects, not to the full complex or its arrows. Split $T$ into its finitely many clopen constant-rank pieces using [det-lem-stratified-lattice-rank] for $L$. All pieces remain qcqs, and rank zero is permitted.

Uses: det-lem-coefficient-finite-descent-lisse, det-lem-stratified-lattice-rank

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/sk-lem-coefficient-finite-descent-lisse.proof.md", "place": "Finite coefficient models on lisse pieces"}

Old step 6:

For a constant-rank lisse $F_T$-module $L$ on qcqs $T$, [det-lem-stratified-lattice-scheme] gives a separated etale surjection $q:\mathrm{Lat}(L)\to T$ and a universal lisse integral lattice in $q^*L$. Images of affine opens of $\mathrm{Lat}(L)$ are open by [lem-weil-pbc-etale-morphism-open-map]. Quasi-compactness [def-weil-pbc-quasi-compact-scheme] selects finitely many whose images cover $T$. Their disjoint union $P$ is qcqs, and $p:P\to T$ is separated, etale and surjective. Restrict the universal lattice to $P$. Apply [lem-weil-pbc-etale-stratified-finite] (Stacks Tag 03S0) to $p$. It supplies a finite constructible locally closed partition of $T$ such that every $p_S:P\times_T S\to S$ is finite etale and surjective. This use of 03S0 requires only qcqs, not Noetherianity.

Uses: det-lem-stratified-lattice-scheme, lem-weil-pbc-etale-morphism-open-map, def-weil-pbc-quasi-compact-scheme, lem-weil-pbc-etale-stratified-finite

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Sheaf of lattices and finite-etale stratification; replace the narrower blueprint trace hypotheses by Tag 03S0"}

Old step 7:

Fix one such $S$, with lattice $N\subset p_S^*L$. Split $p_S$ on an etale covering using [lem-weil-pbc-finite-etale-etale-local-split]. On a splitting with sheets indexed by a finite set $I$, define $p_{S*}p_S^*L\to L$ by $(s_i)\mapsto\sum_i s_i$. Two splittings differ locally by a permutation of the sheets, which leaves this sum unchanged; hence these local maps glue by the sheaf condition. Define $L_0$ as the image of $p_{S*}N\to L$. Over a splitting it is the sum of the sheet lattices. The set $I$ is nonempty since $p_S$ is surjective. This constructs the trace and its image without dividing by the degree.

Uses: lem-weil-pbc-finite-etale-etale-local-split

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Pushing down by the trace: construct the sum map on finite splittings"}

Old step 8:

Trivialize $L$ further pro-etale locally. Clause (1) of [det-lem-stratified-lattice-scheme] identifies a lattice in this trivialization with a section of the constant sheaf on $\mathrm{GL}_r(F)/\mathrm{GL}_r(\mathcal O_F)$. Thus on a further common covering the finitely many sheet lattices are fixed scalar lattices $B_i\subset F^r$. Apply [lem-sfb-continuous-lattice-sum]: their sheaf sum is the sheaf of continuous functions into $\sum_iB_i$, is finite free over the integral coefficients, and its actual inclusion spans the rational coefficient module. The comparison [lem-weil-pbc-continuous-coefficient-realizations] identifies this calculation with the pulled-back condensed coefficients, including the inclusion. Therefore $L_0$ is lisse over $\mathcal O_{F,S}$ and $F_S\otimes L_0\cong L|_S$. This is a direct local sum calculation, with no Noetherian hypothesis on $S$.

Uses: det-lem-stratified-lattice-scheme, lem-sfb-continuous-lattice-sum, lem-weil-pbc-continuous-coefficient-realizations

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Pushing down by the trace: finite sums of actual continuous lattices"}

### lem-sfb-qcqs-constructible-integral-lattice-tree

Retained old steps 4, 9; original argument length 1706 characters.

Old step 4:

Fix a constructible $\Lambda_V$-module $M$. Apply [lem-fix-constructible-open-closed-refinement] to a finite constructible locally closed stratification witnessing its constructibility. This gives a finite binary tree with qcqs vertices, each cut by a quasi-compact open and its closed complement, and genuine scheme morphisms from leaves to original strata. Along each branch use the exact inverse-image composition of [det-pe-topos-functoriality-inverse-image] and the coefficient isomorphism [lem-sfb-alpha-iso]. Pull back the trivializing covers and scalar presentations. On a leaf the pulled scalar module is finite-dimensional over $\Lambda(*)$, hence its realization is finite free. Thus each leaf restriction of $M$ is lisse. The use of actual factoring morphisms avoids inferring factorization merely from containment of underlying sets.

Uses: sk-def-sfb-constructible, lem-fix-constructible-open-closed-refinement, det-pe-topos-functoriality-inverse-image, lem-sfb-alpha-iso

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Finite constructible refinement before lattice construction"}

Old step 9:

Apply [lem-fix-constructible-open-closed-refinement] on each qcqs $T$ from step 5 to the finite partition just obtained. Its leaves have actual maps to the lattice-bearing strata. Pull back $L_0$ and its spanning isomorphism, using [lem-sfb-alpha-iso] and [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]. A locally free integral module remains locally free under this pullback, because the pulled trivializing cover and basis remain a cover and a basis. Coefficient extension also pulls back by the cited tensor comparison. Attach these finite trees to the original tree of step 4. We obtain one finite qcqs open/closed tree over $V$; on every nonempty terminal leaf $W$ there are a finite coefficient field $F$ (equal to $E$ in the finite-field case), an integral lisse module $B_W$, and an isomorphism $\Lambda_W\otimes_{\mathcal O_{F,W}} B_W\cong M|_W$.

Uses: lem-fix-constructible-open-closed-refinement, lem-sfb-alpha-iso, lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Refine the two finite stratifications by scheme-theoretic open/closed pullbacks"}

### lem-sfb-qcqs-lattice-tree-reconstruction

Retained old steps 10, 11, 12, 13; original argument length 3057 characters.

Old step 10:

For an edge of this tree, extension from an open child means $j_!$, and extension from a closed child means $i_*$. These are exact, restrict to the identity on the child, and vanish on the other child by [lem-weil-pbc-proetale-ringed-open-closed]. If a child module has finite constant models on a finite constructible partition, its extension has the same models on those strata and the zero model on the complementary child. All these subsets are constructible in the parent: a quasi-compact open is constructible, its complement is constructible, and relative constructible subsets compose in such a constructible locally closed subset [def-weil-constructible-subset]. Thus the extensions preserve the finite scalar-model constructibility used here. A locally free module has Tor amplitude $[0,0]$ by its local free tensor calculation; [lem-sfb-tor-interval-local-detection] tests this on the trivializing cover and then on complementary children. Consequently either edge extension of a flat module is flat, and iteration preserves Tor amplitude $[0,0]$.

Uses: lem-weil-pbc-proetale-ringed-open-closed, def-weil-constructible-subset, lem-sfb-tor-interval-local-detection

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Exact edge extensions, constructibility and flatness on a qcqs binary tree"}

Old step 11:

These edge extensions commute with the exact coefficient extension of step 2. For $j_!$ take the map $j_!(\Lambda_U\otimes B)\to\Lambda_T\otimes j_!B$ adjoint to its identity restriction on $U$. For $i_*$ take $\Lambda_T\otimes i_*B\to i_*(\Lambda_Z\otimes B)$ adjoint to its identity restriction on $Z$. The restriction comparisons are [lem-weil-pbc-ringed-topoi-derived-tensor-pullback], with coefficient identifications [lem-sfb-alpha-iso]. Each map restricts to an isomorphism on its own child and to $0\to0$ on the other by [lem-weil-pbc-proetale-ringed-open-closed]. The kernel and cokernel have both restrictions zero; [lem-exc-open-closed-detection] makes them zero. This proves both comparison isomorphisms, and iteration proves the comparison along any branch.

Uses: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-alpha-iso, lem-weil-pbc-proetale-ringed-open-closed, lem-exc-open-closed-detection

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Coefficient/edge comparison by the two restrictions"}

Old step 12:

For a terminal leaf $W$, extend its $B_W$ to $V$ along its branch, using the edge operations of step 10, and denote the resulting integral sheaf by $J_W$. Step 10 gives bounded constructibility and Tor amplitude $[0,0]$, so $J_W[0]\in D_{\mathrm{ctf}}(V,\mathcal O_F)$. Step 11 and the leaf isomorphism of step 9 identify $T_{F,V}(J_W[0])$ with the branch extension of $(M|_W)[0]$. It therefore lies in $\mathcal G_V$. The empty leaf contributes zero, for which the zero integral module is a model.

Uses: 

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-stratified-lattice/sk-lem-stratified-lattice.proof.md", "place": "Identify the integral branch generators from the preceding constructions"}

Old step 13:

At each internal vertex $T$, the localization sequence of [lem-weil-pbc-proetale-ringed-open-closed] applied to $M|_T$ is $0\to j_!(M|_U)\to M|_T\to i_*(M|_Z)\to0$. Extend it to $V$ by the exact edge functors along the branch. By [lem-sf-derived-ses-triangle] this is a distinguished triangle. Induct upward through the finite tree: its terminal branch extensions are in $\mathcal G_V$ by step 12, and its middle vertex is an extension of the two child vertices. Thus $M[0]$ is obtained from finitely many objects of $\mathcal G_V$ by finitely many triangle extensions. This is a finite-tree induction, with the terminal case already proved; it does not assume that an original stratum is open in the union of the remaining strata.

Uses: lem-weil-pbc-proetale-ringed-open-closed, lem-sf-derived-ses-triangle

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Finite open/closed devissage, Tag 09AH"}

### Bounded-complex assembly retained in the item

Old step 14:

For $K\in D_{\mathrm{ctf}}(V,\Lambda)$ choose $a\le b$ containing its cohomology. Every $H^q(K)[0]$ is constructible, so step 13 gives its finite construction from $\mathcal G_V$. Apply the truncation triangles of [lem-weil-pbc-truncation-triangle]: $\tau_{\le a-1}K=0$, and for $q=a,\ldots,b$ the triangle has vertices $\tau_{\le q-1}K$, $\tau_{\le q}K$, and $H^q(K)[-q]$. Induction gives $\tau_{\le b}K\simeq K$ in the finite shift-and-extension closure of $\mathcal G_V$, hence in its ambient localizing hull. No connecting map is descended to $F$; all triangles and their arbitrary $\Lambda_V$-linear maps stay in the ambient category. Together with step 3 this proves both clauses. The zero complex, empty $V$ and rank-zero leaves are included.

## Dependency-statement verification for the retained handoff

I opened every statement used by the old proof. To make the handoff independently checkable, their full statements follow. These are not new proof dependencies on an unsplit node; the next worker must choose and verify the precise dependencies of that node when splitting it.

### def-weil-constructible-subset

Let $X$ be a topological space (for instance the underlying space of a scheme). A subset $U\subseteq X$ is *retrocompact* if $U\cap W$ is quasi-compact for every quasi-compact open $W\subseteq X$. A subset $E\subseteq X$ is *constructible* if it is a finite union of subsets of the form $U\cap(X\setminus V)$ with $U,V\subseteq X$ open and retrocompact. The constructible subsets form a Boolean subalgebra of the power set of $X$ (closed under finite unions, finite intersections and complements, Stacks Lemma 005H); it is the Boolean subalgebra generated by the retrocompact open subsets. Every constructible subset is a finite union of locally closed subsets [def-weil-locally-closed-subset]; when $X$ is a Noetherian topological space (for instance a scheme of finite type over a field) every subset is retrocompact and, conversely, every finite union of locally closed subsets is constructible (Stacks Lemma 005L). Without a Noetherian hypothesis the converse fails: in a quasi-compact space, an open subset that is not quasi-compact is locally closed but not constructible.

### def-weil-pbc-quasi-compact-scheme

A topological space $T$ is *quasi-compact* if every open covering of $T$ has a finite subcovering (no Hausdorff condition). A scheme $X$ [def-pc-scheme] is *quasi-compact* if its underlying topological space is quasi-compact.

### def-weil-size-convention

Fix Grothendieck universes $\mathcal U\in\mathcal V$ containing the schemes
and coefficient rings under consideration. Replace every site by a
$\mathcal V$-small skeleton within the chosen bound. Derived categories and
filtered colimits are formed in $\mathcal V$.

### det-lem-coefficient-finite-descent-lisse

Let $X$ be a qcqs scheme.

1. For every lisse $\QbarX$-module $L$ there are a finite $E/\mathbf Q_\ell$, a lisse $E_X$-module
   $L_E$ and an isomorphism $\QbarX\otimes_{E_X}L_E\cong L$.
2. For lisse $E_X$-modules $M,N$, the map
   $\varinjlim_{F\supseteq E}\Hom_{F_X}(M_F,N_F)\to\Hom_{\QbarX}(M_{\Qlb},N_{\Qlb})$ is bijective.

Coefficient and locality conventions: fix a prime $\ell$ and an algebraic closure $\Qlb$ of $\mathbf Q_\ell$. Finite coefficient fields are the subextensions inside this closure [def-weil-finite-subextension-directed-set]. Work on the small pro-etale site [def-weil-pbc-proetale-site]. Here $E_X=p_X^*\underline E$ [def-sfb-subfield-coefficient-ring], and $\QbarX=p_X^*\underline{\Qlb}$ [sk-def-sfb-pulled-back-coefficients], where $\underline{\Qlb}$ is the condensed ring whose continuous sections have values in a finite subextension [sk-def-sfb-qlbar-condensed]. The inclusions are [def-sfb-subfield-coefficient-map] and [def-sfb-subfield-to-qlbar-coefficient-map]. Modules and their linear maps are the module objects of [sk-def-sfb-module-objects]. A module over a ring sheaf $A$ is lisse here if on a covering $\{V_i\to X\}$ its restrictions to the slice sites [def-pur-localized-ringed-site] are isomorphic to $(A|_{V_i})^{r_i}$ with each $r_i$ a finite nonnegative integer. Thus rank zero and varying local ranks are allowed. Scalar extension means the ordinary relative tensor product [sk-def-sfb-change-of-scalars]; $M_F=F_X\otimes_{E_X}M$ and $M_{\Qlb}=\QbarX\otimes_{E_X}M$, and similarly for $N$. The index in (2) is the directed poset of finite $F$ containing the given finite $E$; transition maps on Hom are scalar extension. The displayed colimit is the set of representatives $(F,\phi_F)$ modulo the equivalence generated by scalar extension to a larger field. Quasi-compact means that $X$ has a finite affine open cover, and quasi-separated has the diagonal meaning of [def-weil-quasi-separated-morphism].

### det-lem-stratified-lattice-rank

Fix a prime $\ell$ and a finite extension $E/\mathbf Q_\ell$ with its $\ell$-adic topology [def-weil-l-adic-coefficient-extension]. Let $X$ be a scheme [def-pc-scheme] and put $E_X=p_X^*\underline E$ [sk-def-sfb-condensed-ring, sk-def-sfb-pulled-back-coefficients]. Let $L$ be an $E_X$-module sheaf [sk-def-sfb-module-objects] that is lisse: it is locally isomorphic to $E_U^{\oplus n}$, for finite $n\geq0$, on a covering of the small pro-etale site [sk-def-pe-site]. For $r\geq0$, let $X_r\subseteq|X|$ consist of points $x$ such that, for some (equivalently every) object $U\to X$ in a trivializing covering with $x$ in its image, $L|_U$ has rank $r$ near a preimage of $x$. This rank is independent of the trivializing covering and of the preimage. Then the $X_r$ are open and closed, only finitely many are nonempty if $X$ is quasi-compact [def-weil-pbc-quasi-compact-scheme], and $X=\coprod_{r\geq0}X_r$, with $L|_{X_r}$ of constant rank $r$. Each $X_r$ is given its open subscheme structure [def-weil-open-immersion].

### det-lem-stratified-lattice-scheme

Fix a prime $\ell$, a finite extension $E/\mathbf Q_\ell$ and its topological valuation ring $A=\cO_E$ [def-weil-l-adic-coefficient-extension]. Use universes containing the schemes, coefficient rings and the set of lattices below [def-weil-size-convention]. On the small pro-étale site [def-weil-pbc-proetale-site], $E_X$ and $A_X$ are the pullbacks of the condensed topological rings $E$ and $A$ [sk-def-sfb-pulled-back-coefficients]; modules are module objects [sk-def-sfb-module-objects]. Here lisse means pro-étale locally free of finite rank, and a lattice is an embedded lisse $A_X$-module whose localization at $\ell$ is the ambient rational module. Constant sheaf means sheafification of the constant presheaf [def-weil-pbc-constant-sheaf]. A scheme is qcqs if its underlying space is quasi-compact and its diagonal is quasi-compact [def-weil-pbc-scheme-conventions]. Separated and étale have the meanings of [def-weil-proper-morphism] and [def-weil-etale-morphism].

Let $X$ be a qcqs scheme and $L$ a lisse $E_X$-module of constant rank $r$. Let $\mathcal{L}\mathit{at}$
be the sheaf on $X_{\mathrm{proét}}$ with $\mathcal{L}\mathit{at}(U)$ the set of lisse
$\cO_{E,U}$-submodules $M\subseteq L|_U$ with $M[1/\ell]=L|_U$.

1. If $L|_V\cong E_V^r$ on $V$, then $\mathcal{L}\mathit{at}|_V$ is the constant sheaf on the discrete set
   $\GL_r(E)/\GL_r(\cO_E)$ of $\cO_E$-lattices in $E^r$.
2. $\mathcal{L}\mathit{at}$ is represented by a separated étale $X$-scheme $\mathrm{Lat}(L)\to X$, which is
   surjective.
3. There is a universal lattice $M^{\mathrm{univ}}\subseteq q^*L$ on $\mathrm{Lat}(L)$,
   $q\colon\mathrm{Lat}(L)\to X$.

### det-pe-topos-functoriality-inverse-image

Let $f\colon X\to Y$ be a morphism of schemes and let
$u\colon Y_{\mathrm{proét}}\to X_{\mathrm{proét}}$ be base change, $u(V)=V\times_YX$.

1. $u$ preserves finite limits (it sends $Y$ to $X$ and fibre products to fibre products)
   and sends coverings to coverings.
2. $f_*G:=G\circ u$ defines a functor
   $f_*\colon\Sh(X_{\mathrm{proét}})\to\Sh(Y_{\mathrm{proét}})$, and
   $f^{-1}F:=\bigl(\operatorname{Lan}_{u^{\mathrm{op}}}F\bigr)^{\#}$ (left Kan extension
   followed by sheafification) is left adjoint to it.
3. $f^{-1}$ preserves all colimits and finite limits, so
   $(f^{-1},f_*)$ is a geometric morphism $f_{\mathrm{proét}}$.
4. On abelian sheaves, $f^{-1}$ (computed on underlying sheaves of sets) is exact.
5. For $g\colon Y\to Z$ there are canonical isomorphisms $(g\circ f)_*\cong g_*\circ f_*$
   and $(g\circ f)^{-1}\cong f^{-1}\circ g^{-1}$, so
   $(g\circ f)_{\mathrm{proét}}\cong g_{\mathrm{proét}}\circ f_{\mathrm{proét}}$.

### det-prop-sfb-qlbar-colimit-x-invert-ell

Let $E/\mathbf Q_\ell$ be finite and $X$ a scheme. Let $\cO_{E,X}[1/\ell]$ denote the colimit,
in sheaves of $\cO_{E,X}$-modules on $X_{\mathrm{proét}}$, of
$$
\cO_{E,X}\xrightarrow{\ \ell\ }\cO_{E,X}\xrightarrow{\ \ell\ }\cO_{E,X}\xrightarrow{\ \ell\ }\cdots,
$$
with its ring structure as the localization of $\cO_{E,X}$ at $\ell$. Then the map
$\varphi\colon\cO_{E,X}\to E_X$ of [def-sfb-integers-to-subfield], together with the maps
$\ell^{-m}\varphi$ on the $m$-th term, induces an isomorphism of sheaves of rings
$$
\cO_{E,X}[1/\ell]\xrightarrow{\ \sim\ }E_X .
$$
In particular $\ell$ acts invertibly on $E_X$, and $E_X$ is a flat $\cO_{E,X}$-module.

### lem-exc-open-closed-detection

Let $i:Z\hookrightarrow X$ be a closed immersion, with complementary quasi-compact open immersion $j:U\hookrightarrow X$. Let $R_X$ be a sheaf of commutative rings on $X_{\mathrm{proet}}$, and use the identified inverse-image coefficient sheaves and module operations of [def-weil-pbc-proetale-operations]. If an $R_X$-module sheaf $F$ has zero inverse images $j^*F=0$ and $i^*F=0$, then $F=0$.

### lem-fix-constructible-open-closed-refinement

Let $W$ be a quasi-compact quasi-separated scheme [def-pc-scheme, def-weil-quasi-separated-morphism]. Suppose finitely many finite partitions of the underlying set of $W$ are given by locally closed subschemes $s_\alpha:S_\alpha\hookrightarrow W$ [def-weil-closed-immersion, def-weil-open-immersion], and every stratum image is constructible [def-weil-constructible-subset]. Then each given immersion admits a factorization $S_\alpha\hookrightarrow O_\alpha\hookrightarrow W$ with the first morphism closed, the second open, and both $O_\alpha$ and $O_\alpha\setminus S_\alpha$ quasi-compact. There exists a finite rooted binary tree of locally closed subschemes with root $W$, in which each internal vertex $T$ is partitioned into a quasi-compact open subscheme and its closed complement. Its branches are obtained by scheme-theoretic pullbacks [def-pc-fibre-product] of the chosen immersions $O_\alpha\hookrightarrow W$, $S_\alpha\hookrightarrow O_\alpha$, and their complementary immersions. Every vertex is quasi-compact and quasi-separated, every branch morphism is quasi-compact [def-weil-finite-type-morphism], and the nonempty leaves partition $W$. For every nonempty leaf $T$ and every original partition there is a stratum $S_\alpha$ of that partition and a morphism $T\to S_\alpha$ whose composite with $s_\alpha$ is the canonical morphism $T\to W$.

### lem-pe-coefficient-tor-flat-model

For a small site (C,J) in universe w, a commutative ring sheaf R with modules in the same universe, K in its standard derived localization, and integers a <= b, the coefficient-model Tor test in [a,b] holds if and only if there is a complex P with flat terms, zero below a and above b, and Q(P) isomorphic to K. The predicate is HasCoefficientModelTorAmplitude and the flatness predicate is SheafOfModules.IsFlat.

### lem-pe-internal-section-tensor-comparison

Let $C$ be a site whose objects and morphisms lie in the coefficient universe. Assume abelian sheafification exists, its local equivalences are monoidal, and the category $\mathcal A=\operatorname{Sh}(C,\operatorname{Ab})$ has the closed symmetric monoidal structure given by sheafified objectwise tensor over $\mathbf Z$ [det-def-sfb-sheaf-tensor-structure, sk-def-sfb-sheaf-tensor]. Let $R$ be a commutative ring object of $\mathcal A$, let $R_{\mathrm{sec}}$ be its reconstructed section-ring sheaf, and let
$$E_R:\operatorname{Mod}_R(\mathcal A)\simeq\operatorname{Mod}(R_{\mathrm{sec}})$$
be the equivalence of [def-weil-pbc-internal-abelian-sheaf-module-equivalence], which leaves underlying abelian sheaves and maps unchanged. Give the source the coequalizer relative tensor [def-sfb-modobj-relative-tensor] and the target the sheafification of sectionwise balanced tensor [def-pur-sheaf-tensor-product]. Then $E_R$ is exact and has natural isomorphisms
$$E_R(M\otimes_RN)\cong E_R(M)\otimes_{R_{\mathrm{sec}}}E_R(N),\qquad E_R(R)\cong R_{\mathrm{sec}},$$
characterized on local pure tensors by $m\otimes n\mapsto m\otimes n$. These comparisons respect associators, unitors and symmetry. Applied termwise to cochain complexes [def-weil-abstract-derived-category], $E_R$ identifies the direct-sum total tensor complexes [def-pc-tensor-complex-sheaves] and preserves and reflects acyclicity, flat modules [def-pc-flat-sheaf-modules] and K-flat complexes [def-pc-kflat-complex]; in the internal category, flatness and K-flatness mean the same exact-tensor and acyclic-total-tensor tests.

### lem-pur-derived-change-of-rings

Let $\mathcal C$ be a site and $\varphi:\mathcal O\to\mathcal O'$ a morphism of sheaves of commutative rings on $\mathcal C$; let $D(\mathcal O)$, $D(\mathcal O')$ be the derived categories [def-weil-abstract-derived-category] of the abelian categories of sheaves of $\mathcal O$-modules and of $\mathcal O'$-modules [def-weil-sheaf-of-modules-category]. For a complex $\mathcal P^\bullet$ of $\mathcal O$-modules write $\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'$ for the complex of $\mathcal O'$-modules obtained by applying the change of rings $-\otimes_{\mathcal O}\mathcal O'$ [def-pur-sheaf-tensor-product] termwise. Then: (1) if $\alpha:\mathcal P^\bullet\to\mathcal Q^\bullet$ is a quasi-isomorphism [def-pc-quasi-iso-modules] between K-flat complexes of $\mathcal O$-modules [def-pc-kflat-complex], the induced map $\alpha\otimes1:\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'\to\mathcal Q^\bullet\otimes_{\mathcal O}\mathcal O'$ is a quasi-isomorphism of complexes of $\mathcal O'$-modules; (2) consequently there is an exact functor of triangulated categories $L\varphi^*=-\otimes^{\mathbf L}_{\mathcal O}\mathcal O':D(\mathcal O)\to D(\mathcal O')$, the left derived functor of the termwise change of rings $K(\mathcal O)\to D(\mathcal O')$, $\mathcal G^\bullet\mapsto\mathcal G^\bullet\otimes_{\mathcal O}\mathcal O'$, which is everywhere defined and computed by K-flat complexes: for every K-flat resolution $\mathcal P^\bullet\to\mathcal G^\bullet$ [def-pc-kflat-complex, lem-pc-kflat-resolution] the canonical map $L\varphi^*\mathcal G^\bullet\to\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'$ (inverse of the map induced by the resolution) is an isomorphism in $D(\mathcal O')$, and for two K-flat resolutions $\mathcal P^\bullet\to\mathcal G^\bullet$, $\mathcal P'^\bullet\to\mathcal G^\bullet$ the resulting isomorphism $\mathcal P^\bullet\otimes_{\mathcal O}\mathcal O'\cong\mathcal P'^\bullet\otimes_{\mathcal O}\mathcal O'$ in $D(\mathcal O')$ is canonical (compatible with composition for a third resolution).

### lem-sf-derived-ses-triangle

Let $\mathcal C$ be an abelian category with derived category $D(\mathcal C)$ [def-weil-abstract-derived-category], a triangulated category [def-weil-triangulated-category], and for an object $A$ of $\mathcal C$ write $A[0]$ for the complex with $A$ in degree $0$. For every short exact sequence $0\to A\xrightarrow{f}B\xrightarrow{g}C\to0$ in $\mathcal C$ there is a morphism $\delta:C[0]\to A[0][1]$ in $D(\mathcal C)$ such that $A[0]\xrightarrow{f}B[0]\xrightarrow{g}C[0]\xrightarrow{\delta}A[0][1]$ is a distinguished triangle.

### lem-sf-exact-functor-derived-triangulated

Let $F:\mathcal C_1\to\mathcal C_2$ be an exact (additive, preserving finite limits and colimits) functor between abelian categories, with derived categories $D(\mathcal C_1)$, $D(\mathcal C_2)$ [def-weil-abstract-derived-category]. Applying $F$ termwise to complexes induces a functor $F:D(\mathcal C_1)\to D(\mathcal C_2)$ which is triangulated [def-weil-triangulated-category] (it commutes with the shift and carries distinguished triangles to distinguished triangles) and which carries a complex $A[n]$ concentrated in one degree to $F(A)[n]$.

### lem-sfb-alpha-iso

Let $\Lambda$ be a condensed ring and let $f\colon X\to Y$ be any morphism of
schemes. Then $\alpha_f\colon f^*\Lambda_Y\to\Lambda_X$ ([def-sfb-alpha]) is
an isomorphism.

### lem-sfb-continuous-lattice-sum

Fix a prime $\ell$ and a finite extension $E/\mathbf Q_\ell$ with its $\ell$-adic topology and valuation ring $A=\mathcal O_E$ with the subspace topology [def-weil-l-adic-coefficient-extension]. For each scheme $T$ [def-pc-scheme], use its small pro-étale site [def-weil-pbc-proetale-site], continuous coefficient ring sheaves $A_T(U)=C(|U|,A)$ and $E_T(U)=C(|U|,E)$ [def-weil-pbc-continuous-integral-coefficients], and sheaves of modules [def-weil-sheaf-of-modules-category]. Let $r\geq0$, let $J$ be a nonempty finite set, and let $\Lambda_j\subseteq E^r$ admit $A$-bases that are also $E$-bases. Equip all lattices and $\Lambda=\sum_j\Lambda_j$ with their subspace topologies. The sum map $q:\bigoplus_j\Lambda_j\to\Lambda$ has a continuous $A$-linear right inverse, with the finite product topology on its domain. Consequently, for every topological space $Z$, the map $\bigoplus_j C(Z,\Lambda_j)\to C(Z,\Lambda)$ is surjective. On the pro-étale site of any scheme $S$, the sum of the submodule sheaves $U\mapsto C(|U|,\Lambda_j)$ inside $E_S^r$ is exactly $U\mapsto C(|U|,\Lambda)$. This sheaf is free of rank $r$ over $A_S$, and its inclusion becomes an isomorphism after extension to $E_S$.

### lem-sfb-finite-constant-model-two-term-free-resolution

Let $\ell$ be a prime, $E/\mathbf Q_\ell$ a finite extension with valuation ring $\mathcal O_E$ [def-weil-l-adic-coefficient-extension], and $T$ any scheme [def-pc-scheme]. Choose either $A=\mathcal O_E$, $\Lambda=\underline{\mathcal O_E}$, or $A=E$, $\Lambda=\underline E$, with the usual condensed coefficient rings [sk-def-sfb-condensed-ring]. On the small pro-étale site of $T$ [def-weil-size-convention, def-weil-pbc-proetale-site], put $B_T=p_T^*\Lambda$ [sk-def-sfb-pulled-back-coefficients]. For an $A$-module $Q$, write $\underline Q$ for its constant module sheaf [def-weil-pbc-constant-sheaf], with the canonical map $\underline A\to B_T$. Let $P$ be a finitely presented $A$-module, meaning that it is the cokernel of a map $A^s\to A^t$ with $s,t$ finite, and put $L=B_T\otimes_{\underline A}\underline P$ [def-sfb-modobj-relative-tensor, sk-def-sfb-constructible]. There are finite nonnegative integers $a,b$ and an exact scalar sequence $0\to A^a\xrightarrow{u}A^b\xrightarrow{v}P\to0$ whose constant sheafification followed by extension of scalars yields an exact sequence of $B_T$-module sheaves [def-weil-sheaf-of-modules-category]
$$0\longrightarrow B_T^a\xrightarrow{1\otimes\underline u}B_T^b\xrightarrow{1\otimes\underline v}L\longrightarrow0.$$
Thus the augmented cochain complex $[B_T^a\to B_T^b]\to L[0]$, with free terms in degrees $-1,0$, is a quasi-isomorphism [def-pc-cochain-complex-modules, def-pc-quasi-iso-modules]. In the case $A=E$ one may take $a=0$, so $L$ is finite free. No Noetherianity assumption on $T$, torsion-freeness assumption on $P$, or completion of the derived category is imposed.

### lem-sfb-module-object-ringed-site-derived-comparison

Let $X$ be a scheme [def-pc-scheme], with its pro-étale site taken small in the chosen universe [def-weil-size-convention, def-weil-pbc-proetale-site]. Let $\Lambda$ be a commutative condensed ring [sk-def-sfb-condensed-ring] and put $B=p_X^*\Lambda$ [sk-def-sfb-pulled-back-coefficients], a commutative ring object of abelian sheaves with the sheafified pointwise tensor over $\mathbf Z$ [sk-def-sfb-sheaf-tensor]; write $B_{\mathrm{sec}}$ for its section-ring sheaf. Let $\mathcal A$ be the category of $B$-module objects [sk-def-sfb-module-objects], $\mathcal M=\operatorname{Mod}(B_{\mathrm{sec}})$ the category of sheaves of $B_{\mathrm{sec}}$-modules [def-weil-sheaf-of-modules-category], and $F:\mathcal A\simeq\mathcal M$ the equivalence of [def-weil-pbc-internal-abelian-sheaf-module-equivalence], which leaves underlying abelian sheaves, sections and morphisms unchanged. Let $D(F)$ be its termwise extension to the ordinary uncompleted unbounded derived categories [sk-def-sfb-derived-categories], and identify the K-flat derived relative tensor [def-sfb-modobj-relative-tensor, sk-def-sfb-derived-tensor-hom] with the ordinary ringed-site K-flat derived tensor through the comparison of [lem-pe-internal-section-tensor-comparison]. Let $\operatorname{RHom}^{\mathcal A}_B$ be the derived internal Hom of $D(\mathcal A)$, defined as the right adjoint of this derived relative tensor in [sk-def-sfb-derived-tensor-hom], and let $R\mathcal Hom_{B_{\mathrm{sec}}}$ be the functorial K-injective sheaf-Hom model of [def-pur-derived-internal-hom]. Then for all $K,N\in D(\mathcal A)$ there are isomorphisms
$$D(F)\bigl(\operatorname{RHom}_{B}^{\mathcal A}(K,N)\bigr)\cong R\mathcal Hom_{B_{\mathrm{sec}}}(D(F)K,D(F)N),$$
natural in $K$ (contravariantly) and $N$, which carry the evaluation morphism $K\otimes^{\mathbf L}_B\operatorname{RHom}^{\mathcal A}_B(K,N)\to N$, transported by $D(F)$ and the tensor comparison, to the ringed-site evaluation $D(F)K\otimes^{\mathbf L}_{B_{\mathrm{sec}}}R\mathcal Hom_{B_{\mathrm{sec}}}(D(F)K,D(F)N)\to D(F)N$. For every object $U$ of $X_{\mathrm{pro\acute et}}$, restricting these isomorphisms to the slice site $X_{\mathrm{pro\acute et}}/U$ [def-pur-localized-ringed-site] gives the corresponding isomorphisms for the ring object $B|_U$ and its section-ring sheaf.

### lem-sfb-qlbar-flat

For a finite extension $E$ of $\mathbf Q_\ell$ inside $\Qlb$ and every scheme $X$, the extension
of scalars $\overline{\mathbf Q}_{\ell,X}\otimes_{E_X}-\colon\Mod_{E_X}\to\Mod_{\overline{\mathbf Q}_{\ell,X}}$ along
$E_X\to\overline{\mathbf Q}_{\ell,X}$ ([def-sfb-subfield-to-qlbar-coefficient-map],
[sk-def-sfb-change-of-scalars]) preserves finite limits; that is, $\overline{\mathbf Q}_{\ell,X}$ is flat over
$E_X$.

### lem-sfb-tor-interval-local-detection

Let $X$ be a scheme, $A$ a sheaf of commutative rings on its small pro-étale site [def-weil-pbc-proetale-site], and $K\in D(\operatorname{Mod}(A))$ [def-weil-sheaf-of-modules-category], [def-weil-abstract-derived-category]. For integers $c\leq d$, say that a complex has Tor amplitude in $[c,d]$ when its derived tensor with every module sheaf in degree zero has zero cohomology outside $[c,d]$; use K-flat derived tensor [def-pc-kflat-complex]. For a scheme morphism $f:Y\to X$ use the inverse-image ring $f^{-1}A$ and module inverse image [def-weil-proetale-inverse-image]. (i) If $\{V_i\to X\}$ is a pro-étale covering family and every $K|_{V_i}$ has Tor amplitude in the same interval $[c,d]$, then $K$ has Tor amplitude in $[c,d]$. (ii) If $i:Z\hookrightarrow X$ is a closed immersion with complementary quasi-compact open immersion $j:U\hookrightarrow X$ [def-weil-closed-immersion], [def-weil-open-immersion], and $i^{-1}K,j^{-1}K$ have Tor amplitude in $[c,d]$, then $K$ has Tor amplitude in $[c,d]$. No quasi-coherence, Noetherian or finite-cover hypothesis is imposed.

### lem-weil-pbc-continuous-coefficient-realizations

Let X be a scheme and E,F be topological rings in Type 0. The canonical morphism from the condensed continuous E coefficient object pulled to X to the sheaf U↦C(U,E) is an actual adjoint of composition with the profinite test projection. It is a monoid morphism and, for totally disconnected E, is an isomorphism. For a continuous ring map φ:E→F, this comparison intertwines the pulled condensed coefficient map with postcomposition of continuous functions by φ. In particular the integral-to-field comparison square commutes.

### lem-weil-pbc-etale-morphism-open-map

Let $f:U\to X$ be an etale morphism of schemes [def-weil-etale-morphism]. Then the map of underlying topological spaces of $f$ is open: the image $f(W)$ of every open subset $W\subseteq U$ is open in $X$. In particular the image of $f$ is open.

### lem-weil-pbc-etale-stratified-finite

Let $X$ be a quasi-compact and quasi-separated scheme [def-weil-pbc-scheme-conventions], and let $j:U\to X$ be an etale morphism [def-weil-etale-morphism] with $U$ quasi-compact and quasi-separated. Then there exists a finite partition $X=\coprod_i X_i$ by constructible locally closed subschemes [def-weil-constructible-subset], forming a stratification [def-constructible-stratification], such that each base change $U_i:=U\times_X X_i\to X_i$ is finite etale [def-weil-pbc-finite-etale-category]. The fibre products are those of [def-pc-fibre-product]. This is Stacks Project Lemma Tag 03S0 (lemma-etale-stratified-finite).

### lem-weil-pbc-exact-functor-complex-cohomology

Let $\mathcal A,\mathcal B$ be abelian categories [def-sp-abelian] and $F:\mathcal A\to\mathcal B$ an exact functor (additive, preserving finite limits and finite colimits). For a cochain complex $K=(K^r,d^r)$ of $\mathcal A$ let $F(K)=(F(K^r),F(d^r))$ be the complex obtained by applying $F$ termwise, and let $H^r(K)=\ker d^r/\operatorname{im}d^{r-1}$ be its $r$-th cohomology object [def-weil-abstract-derived-category]. Then for every $r\in\mathbf Z$ there is an isomorphism $c^r_K:H^r(F(K))\xrightarrow{\sim}F(H^r(K))$, natural in the complex $K$ (i.e. an isomorphism of functors $H^r\circ F\cong F\circ H^r$ from cochain complexes of $\mathcal A$ to $\mathcal B$); $c^r_K$ is induced by the identifications $\ker F(d^r)=F(\ker d^r)$ and $\operatorname{im}F(d^{r-1})=F(\operatorname{im}d^{r-1})$ as subobjects of $F(K^r)$, so it is compatible with the inclusions of cycles and the projections onto cohomology.

### lem-weil-pbc-finite-etale-etale-local-split

Let $f:Y\to X$ be a finite etale morphism of schemes [def-weil-pbc-scheme-conventions] and $x\in X$. Then there are an etale morphism $g:U\to X$ [def-weil-etale-morphism], a point $u\in U$ with $g(u)=x$, a finite set $J$ and a decomposition $Y\times_XU=\coprod_{j\in J}V_j$ of the fibre product [def-pc-fibre-product] into pairwise disjoint open and closed subschemes $V_j$ such that, for every $j\in J$, the composite $V_j\hookrightarrow Y\times_XU\xrightarrow{\mathrm{pr}_2}U$ is an isomorphism of schemes.

### lem-weil-pbc-proetale-ringed-open-closed

Let $X$ be a scheme [def-pc-scheme], $i:Z\hookrightarrow X$ a closed immersion with complementary quasi-compact open immersion $j:U\hookrightarrow X$ [def-weil-closed-immersion, def-weil-open-immersion, def-weil-finite-type-morphism]. Let $A$ be a sheaf of commutative rings on $X_{\mathrm{proet}}$ [def-weil-pbc-small-proetale-site], and use $i^{-1}A,j^{-1}A$ on $Z,U$. The inverse images and direct images are those of [def-weil-proetale-inverse-image], and $j_!$ is the sheafification [def-weil-presheaf-modules-sheafification] of the extension-by-zero presheaf [def-weil-extension-by-zero-presheaf]: the presheaf value at $V\to X$ is the given module evaluated at $V\to U$ if this factorization exists, and is zero otherwise. The localization of sites is [lem-weil-proetale-weakly-etale-localization], with their induced module actions [def-weil-sheaf-of-modules-category]. The module functor $j_!$ is left adjoint to $j^{-1}$. These functors satisfy $i^{-1}i_*\cong\operatorname{id}$, $j^{-1}j_!\cong\operatorname{id}$, $j^{-1}i_*=0$, and $i^{-1}j_!=0$. The functors $j_!$ and $i_*$ are exact. For every $A$-module sheaf $M$ the counit and unit give a short exact sequence [def-weil-pbc-exact-sequence] $0\to j_!j^{-1}M\to M\to i_*i^{-1}M\to0$. If $X$ is quasi-compact and quasi-separated [def-weil-pbc-scheme-conventions], $i_*$ commutes with small filtered colimits of module sheaves [def-weil-pbc-category-colimit, def-weil-size-convention].

### lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Let $\mathcal C,\mathcal D$ be sites small relative to the universe of module sheaves, with sheaves of commutative rings $R,S$, and let $u:\operatorname{Sh}(\mathcal D)\to\operatorname{Sh}(\mathcal C)$ be a morphism of topoi, meaning an adjunction $u^{-1}\dashv u_*$ whose left adjoint preserves finite limits. Equip it with a ring map $u^{-1}R\to S$. Write $D(R)$ and $D(S)$ for the unbounded derived categories of the abelian categories of sheaves of modules over these rings [def-weil-sheaf-of-modules-category, def-weil-abstract-derived-category]. Module pullback is $u^*M=S\otimes_{u^{-1}R}u^{-1}M$, using the sheaf tensor product [def-pur-sheaf-tensor-product]; $Lu^*:D(R)\to D(S)$ is its total left derived functor, computed by applying $u^*$ to K-flat resolutions with flat terms [def-pc-kflat-complex, lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-derived-pullback]. Here a sheaf of modules is flat when tensoring with it is exact [def-pc-flat-sheaf-modules]. If $P$ is K-flat with flat terms, then $u^*P$ is K-flat with flat terms. Derived tensor is computed by the total tensor complex [def-pc-tensor-complex-sheaves] of K-flat resolutions [lem-weil-pbc-site-derived-tensor-descent]. For all $F,G\in D(R)$ there is a canonical isomorphism
$$
 Lu^*(F\otimes_R^{\mathbf L}G)
 \xrightarrow{\sim}Lu^*F\otimes_S^{\mathbf L}Lu^*G
$$
in $D(S)$, natural simultaneously in $F$ and $G$.

### lem-weil-pbc-truncation-triangle

Let $\mathcal A$ be an abelian category with derived category $D(\mathcal A)$ [def-weil-abstract-derived-category], a triangulated category [def-weil-triangulated-category], with cohomology functors $H^n$ and shift $[1]$, $(M[1])^r=M^{r+1}$, $d_{M[1]}=-d_M$. For a complex $K$ of $\mathcal A$ and $q\in\mathbf Z$ let $\tau_{\leq q}K$ be the canonical truncation, the subcomplex $\cdots\to K^{q-2}\to K^{q-1}\to\Ker(d^q_K)\to0\to\cdots$ of $K$ (the truncation of the standard t-structure [def-sbc-standard-tstructure-derived-category]), so that $\tau_{\leq q-1}K\subseteq\tau_{\leq q}K$, and let $H^q(K)[-q]$ be the complex with the single object $H^q(K)$ placed in degree $q$. Let $i_q:\tau_{\leq q-1}K\to\tau_{\leq q}K$ be the inclusion and $j_q:\tau_{\leq q}K\to H^q(K)[-q]$ the morphism of complexes which in degree $q$ is the projection $\Ker(d^q_K)\to H^q(K)$ and zero in the other degrees. Then there is a unique morphism $k_q:H^q(K)[-q]\to(\tau_{\leq q-1}K)[1]$ in $D(\mathcal A)$ such that
$$
 \tau_{\leq q-1}K\xrightarrow{\,i_q\,}\tau_{\leq q}K\xrightarrow{\,j_q\,}H^q(K)[-q]\xrightarrow{\,k_q\,}(\tau_{\leq q-1}K)[1]
$$
is a distinguished triangle $T_q(K)$ of $D(\mathcal A)$ (namely $k_q=\delta\circ\bar j_q^{-1}$, where $\delta$ is the boundary morphism of the distinguished triangle of the short exact sequence of complexes $0\to\tau_{\leq q-1}K\to\tau_{\leq q}K\to\tau_{\leq q}K/\tau_{\leq q-1}K\to0$ and $\bar j_q:\tau_{\leq q}K/\tau_{\leq q-1}K\to H^q(K)[-q]$ is the quasi-isomorphism induced by $j_q$). The triangle is functorial in $K$: $\tau_{\leq q}$, $\tau_{\leq q-1}$ and $H^q(-)[-q]$ preserve quasi-isomorphisms and so act on morphisms of $D(\mathcal A)$ [lem-weil-pbc-truncation-descends], and for every morphism $f:K\to L$ of $D(\mathcal A)$ between complexes $K,L$ the triple $(\tau_{\leq q-1}f,\tau_{\leq q}f,H^q(f)[-q])$ is a morphism of triangles $T_q(K)\to T_q(L)$. If $K$ is bounded below (as a complex, or only in cohomology: $H^n(K)=0$ for $n\ll0$), so are the three terms; in particular for $\mathcal A=\Ab(T_{\Et})$ the triangle lies in $\Dplus(T_{\Et})$ [def-weil-pbc-derived-categories].

### sk-def-sfb-constructible

The definition of a constructible sheaf makes sense for any condensed ring. Recall that for
$g\colon Z\to X$ the restriction $M|_Z=g^*M$ of a $\Lambda_X$-module is a
$\Lambda_Z$-module, since $g^{-1}\Lambda_X\simeq\Lambda_Z$
([sk-def-sfb-pulled-back-coefficients], [sk-def-sfb-transport]); thus
$g^*\colon\Mod(X_{\mathrm{proét}},\Lambda)\to\Mod(Z_{\mathrm{proét}},\Lambda)$.

Let $\Lambda$ be a commutative condensed ring.

1. A $\Lambda_X$-module $M$ has a *finite constant local model* if there is a pro-étale
   cover $\{U_i\to X\}$ ([def-weil-pbc-proetale-site]) and finitely presented modules $P_i$
   over the scalar ring $\Lambda(*)$ such that
   $$
   M|_{U_i}\simeq\Lambda_{U_i}\otimes_{\Lambda(*)}P_i .
   $$
   Here $\Lambda(*)$ and $P_i$ are constant sheaves on $U_i$, acting through
   $\Lambda(*)\to\Lambda_{U_i}$. Equivalently, on each $U_i$ the module $M$ has a
   presentation by a finite matrix with entries in the scalar ring $\Lambda(*)$.
2. For qcqs $X$, a $\Lambda_X$-module $M$ is *constructible* if there is a finite
   stratification $X=\coprod_aX_a$ by constructible locally closed subschemes
   ([def-constructible-stratification]) such that each $M|_{X_a}$ has a finite constant
   local model. On an arbitrary scheme this condition is imposed locally on affine opens.
   The word constructible requires each stratum to be a constructible subset; for
   Noetherian schemes this is automatic for locally closed strata.

We write $\Cons(X,\Lambda)\subset\Mod(X_{\mathrm{proét}},\Lambda)$ for the full subcategory
of constructible sheaves, and $\Dbc(X,\Lambda)\subset D(X_{\mathrm{proét}},\Lambda)$ for the
full subcategory of bounded complexes with constructible cohomology sheaves (compare
[sk-def-sfb-bounded-constructible]). A complex $K$ has *Tor amplitude in $[a,b]$* if
$K\otimes^{\mathbf L}_{\Lambda_X}N$ has cohomology only in $[a,b]$ for every sheaf $N$ of
$\Lambda_X$-modules. We write $\Dctf(X,\Lambda)$ for the full subcategory of
$\Dbc(X,\Lambda)$ of complexes of finite Tor amplitude (compare [sk-def-sf-categories]).
