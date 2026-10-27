# Stage-1 repair: lem-trf-bounded-above-coherent-rhom

## Worker report

Files written (all relative to this sandbox):
- dag/nodes/sec-trace-formula/lem-trf-bounded-above-coherent-rhom.json: existing statement unchanged; three assembly steps, two new proof dependencies.
- dag/nodes/sec-trace-formula/lem-trf-finite-module-target-rhom.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-noetherian-quadrant-abutment.json: statement, unsplit; no Mathlib match.
- citations.json and report.md.

Attachments: none. The project declaration DerivedCategory.boundedAbove_coherent_rhom in lean/Sheaf/Algebra/Homology/BoundedAboveCoherentRHom.lean has a sorry. Searches of lean/WeilConjectures by the blueprint tag and bounded-above/coherent/RHom and spectral-sequence finite-generation notions found no exact closed declaration. The upstream source is not evidence of completion.

WANTED: none.

The provided sandbox initially contained only dispatcher marker files, with no DAG node, report, citations or search log. I copied the live item without using git; its five steps exactly match the returned character counts (704, 521, 681, 815, 971). Thus the live node supplies the returned mathematical work. No earlier sandbox work was discarded. All maintainer-owned metadata, including the Lean record and reviews, is retained without alteration. The handoff head is e2a95534abdca96856ae1c3b80c5b78fb624dc06. Delivery tooling performs the required rebase onto current server state.

The only defect repaired is the returned proof granularity: no statement dispute or mathematical error was found. The unit and chapter route are unchanged. Nothing remains unfinished within this split; proofs of the two new unsplit nodes intentionally belong to future workers.

## Return repaired: spreading the work

The return requires at least two independent, comparably sized arguments with statement-only new nodes and an item assembly under 3000 characters. The finite-module-target node carries old steps 2--3 (1202 characters of original argument), while the generic quadrant node carries old steps 1 and 5 (1675 characters). These are separate tasks: the first applies the source hyper-Ext theorem and module Ext finiteness to complexes; the second proves the purely module-theoretic spectral-sequence finiteness/stabilization theorem without any derived Hom. Neither is the whole item, and the generic node is not a clause of it. Old step 4 (815 characters), including the one-object-site identification, remains explicit in the item assembly. Both new nodes have empty proof, empty proof_deps and null proof_origin, and are unsplit. Their statements contain conclusions and hypotheses only, not proof sketches.

Every original argument is preserved below. Future proof of the finite-module-target node uses the existing lem-trf-source-hyperext-module-target, lem-sc-ext-noetherian-finite, and the new generic quadrant node with a=0,b=-u. Future proof of the generic quadrant node uses lem-weil-pbc-noetherian-submodule-finite and the generator/finite-filtration argument. These are development notes here, not premature proof dependencies on unsplit nodes. The two new nodes can be assigned independently; the first may cite the second's statement while its proof is being developed.

## Original arguments retained, with destinations

### Original step 1 → lem-trf-noetherian-quadrant-abutment

We will use the following elementary finite-generation argument over the given Noetherian ring $A$. By [lem-weil-pbc-noetherian-submodule-finite], a submodule of a finite $A$-module is finite. A quotient is finite because the images of any finite generating set generate it [def-weil-finitely-generated-module]. Thus subquotients are finite. If $0\to B\to C\to D\to0$ is exact with $B,D$ finite, choose generators of $B$ and lifts in $C$ of generators of $D$; their union generates $C$, since subtracting a linear combination of the lifts leaves an element of $B$. Induction on the number of successive quotients now shows that a module with a finite filtration and finite successive quotients is finite.

Original citations: lem-weil-pbc-noetherian-submodule-finite, def-weil-finitely-generated-module.

### Original step 2 → lem-trf-finite-module-target-rhom

Fix the integers $u,v$ in the hypothesis and first let $N$ be any finite $A$-module placed in degree zero. Apply [lem-trf-source-hyperext-module-target] to $K,N,u$. Its $E_2$ terms are $\operatorname{Ext}^i_A(H^{-j}(K),N)$ for $i\geq0$, and are zero outside $i\geq0$, $j\geq-u$. The two module arguments are finite by the hypothesis on $K$ and our choice of $N$, and $A$ is Noetherian, so [lem-sc-ext-noetherian-finite] makes every such $E_2$ term finite. The negative $i$ terms are zero by the source-sequence statement.

Original citations: lem-trf-source-hyperext-module-target, lem-sc-ext-noetherian-finite.

### Original step 3 → lem-trf-finite-module-target-rhom

In this spectral sequence every $E_{s+1}^{i,j}$ is a quotient of a submodule of $E_s^{i,j}$. Step 1 therefore proves by induction on $s\geq2$ that all pages have finite terms. A fixed bidegree eventually stabilizes by [lem-trf-source-hyperext-module-target], so its $E_\infty$ term is finite too; this uses eventual stabilization, not finiteness of an infinite intersection. In total degree $p$ the same node gives a finite filtration of $H^p(R\operatorname{Hom}_A(K,N[0]))$ with graded terms indexed by $-u\leq j\leq p$. Step 1 makes the abutment finite. This proves finite generation for every $p\in\mathbf Z$ and every finite module $N$, including the zero abutments for $p<-u$.

Original citations: lem-trf-source-hyperext-module-target, lem-weil-pbc-noetherian-submodule-finite.

### Original step 4 → item assembly step 2

Now apply [lem-per-bounded-above-rhom-hyperext] on the one-object site with only the identity covering, with coefficient ring $A$, and with its parameters $r=u$, $c=v$. Sheaves on this site are precisely modules, so its derived category and cohomology are the ordinary ones. Its internal Hom is exactly the $R\operatorname{Hom}_A$ in the statement: the Hom-complex/K-injective formula in [def-pur-derived-internal-hom] is unchanged on this site. The bounds required by that node are exactly the assumed upper bound on $K$ and lower bound on $L$. We obtain an $A$-module spectral sequence
$$E_2^{p,q}=H^p(R\operatorname{Hom}_A(K,H^q(L)[0]))\quad\Longrightarrow\quad H^{p+q}(R\operatorname{Hom}_A(K,L)),$$
zero outside $p\geq-u$, $q\geq v$, with a finite exhaustive separated abutment filtration in each total degree.

Original citations: lem-per-bounded-above-rhom-hyperext, def-pur-derived-internal-hom.

### Original step 5 → lem-trf-noetherian-quadrant-abutment

Each $H^q(L)$ is finite by hypothesis, so Step 3, with $N=H^q(L)$, makes every $E_2^{p,q}$ of Step 4 finite. As before, kernels are finite by [lem-weil-pbc-noetherian-submodule-finite], quotients are generated by images of generators, and induction on pages makes every term of every finite page finite. For fixed $(p,q)$ the incoming differential is zero when $s>p+u$, while the outgoing differential is zero when $s>q-v+1$, by the support bounds of [lem-per-bounded-above-rhom-hyperext]; hence $E_\infty^{p,q}$ is a finite-page term and is finite. In total degree $n$, that node supplies a finite filtration with graded pieces $E_\infty^{p,n-p}$ and only $v\leq n-p\leq n+u$ contributing. Step 1 gives finite generation of $H^n(R\operatorname{Hom}_A(K,L))$. If $n<v-u$ the interval is empty, so every graded piece is zero; a finite exhaustive separated filtration with zero graded pieces has zero abutment. This is the required vanishing and completes both conclusions.

Original citations: lem-weil-pbc-noetherian-submodule-finite, lem-per-bounded-above-rhom-hyperext.

## Searches and sources

Read perfect.tex Tag 0D0C, lemma-coherent-internal-hom, in full, especially the ordinary-ring algebra problem and both displayed Ext sequences. Read injectives.tex Tag 0G20, remark-spectral-sequences-ext-variant, including the renumbering and bounded convergence; read algebra.tex Tag 08YR, lemma-ext-noetherian, and Tag 00IK, lemma-Noetherian-basic, including its generator induction; read homology.tex Tag 0BK5, lemma-ss-converges-trivial. Both new nodes isolate exactly the final finite-generation inference in 0D0C; neither changes the coefficient category nor assumes finite injective/projective dimension. The generic shifted-quadrant statement makes explicit the support, differential bidegrees and finite filtration which that inference uses.

Read GOAL.md, the three levels in SETUP.md, chapter sec-trace-formula, unit sk-i-curve-zero and the current main-20261015 lem-trf-local-term-locality proof. This algebra input follows the existing long relative-duality branch of that ancestor; the repair does not replace any geometric argument. blueprint_refs.py ancestor returns lem-trf-local-term-locality; new from.via is the old item's via with the item prepended. Their from.place specifies the old proof steps and the two-sequence algebra problem.

Before creating either node I searched all dag/nodes for 0D0C, 0G20, finite-abutment/finite-spectral-sequence/coherent-RHom notions, inspected candidate statements, and searched the whole imported blueprint via blueprint_refs.py for spectral sequence, module target, coherent Hom, finite cohomology, Noetherian, finite abutment, and bounded above. The spectral-sequence hits define the notion or prove comparison/convergence, not finite generation of modules; finite cohomology/bounded-above hits concern perfectness, pullback or constructible geometric objects. No blueprint node states either new assertion. same_as is consequently empty. The existing source-hyperext node gives the first sequence without finiteness, and is reused in the development plan, not duplicated.

Every new node has two LeanFinder phrasings, Loogle, a natural-language LeanSearch attempt, and a Mathlib grep, all run through msearch.py and recorded verbatim from searches.jsonl. LeanSearch returned rate-limit errors and is honestly marked unavailable. Read the returned hits: ModuleCat.finite_ext at Algebra/Category/ModuleCat/Ext/Finite.lean:27-35 handles two modules only; the small localized Hom and injective dimension hits do not give finite generation. FGModuleCat.Abelian (instance at line 35) and its finite limits give closure under kernels/finite diagrams but no spectral-sequence theorem. SpectralSequence/Basic.lean:127-134 concerns a finite number of rows, not finite generation. These are ingredients, not one-line matches. The old item's already logged Mathlib searches and results are retained.

## Review by NX

I checked the return against the actual five-step proof, not just its length. The original finite-generation generator argument, both spectral sequences, each finite-page induction, each stabilization assertion, the finite filtration ranges and the empty-interval vanishing all have explicit destinations above. The assembly is below 3000 characters and has no step over 2000. The new nodes require different arguments of comparable size and are delivered statement-only.

For assembly step 1 I opened lem-trf-finite-module-target-rhom: its statement explicitly quantifies over all t, permits K unbounded below, assumes precisely finite cohomology of K and a finite target module, and uses the same one-object-site RHom. Substituting N=H^q(L) meets every hypothesis. No finiteness of terms of a representative complex is assumed.

For assembly step 2 I opened lem-per-bounded-above-rhom-hyperext and def-pur-derived-internal-hom. The former explicitly gives the displayed E2, A-linearity after specialization, differential of bidegree (s,1-s), support p>=-u,q>=v, and a finite exhaustive separated filtration with stable graded pieces. The latter explicitly specifies the Hom-complex/K-injective formula. The one-object identity-covering site is small and all module presheaves are sheaves; its complexes, quasi-isomorphisms and Hom-complex formulas are the ordinary module ones. Thus this is a definitional specialization, not an unproved derived comparison. The existing split_report.tool_uses declaration for the off-unit generic hyper-Ext theorem is retained; no tool_uses maintainer field is changed.

For assembly step 3 I opened lem-trf-noetherian-quadrant-abutment. Its statement covers exactly the available spectral sequence with a=-u and b=v, finite second page from step 1 and finite filtrations from step 2, and concludes both finiteness and zero below a+b=v-u. All quotes in citations.json are full verbatim node statements, one for every uses entry; no proof of a cited node is being used as though it were its statement.

I checked small cases: K=0 or N=0 gives the zero derived Hom; A=0 gives only zero modules and is not excluded; for A=k a field and K=k[-u], N=k the only nonzero degree is -u, so the strict lower bound is correct. For K=k[-u], L=k[-v], RHom is concentrated in v-u, testing the item's endpoint and signs. K may extend indefinitely left: at a fixed total degree the source sequence still has the finite range -u<=j<=t, so no infinite extension is used. For the generic lemma the incoming source is (p-s,q+s-1), zero if s>p-a, and the outgoing target is (p+s,q-s+1), zero if s>q-b+1. Taking s at least 2 and larger than their maximum gives stable finite-page terms, not finiteness of an infinite intersection. Only b<=q<=n-a occur on a total-degree diagonal. If n<a+b there is no such q, and a finite exhaustive separated filtration with all graded pieces zero has zero underlying module. A single nonzero E2 term at (a,b) with zero differentials tests the nonzero endpoint n=a+b. An arbitrary non-Noetherian ring is deliberately not included, since submodules of finite modules need not be finite there.

Against delivery-errors B--E: all objects and hypotheses are introduced locally; notions cite their actual definition nodes; TeX is encoded once; sources use tags and labels, not unstable section numbers. Every new node is unsplit with no proof fields populated. The item uses only the statements just read, with matching hypotheses and verbatim citations. DAG and blueprint duplicate searches preceded creation. No circular proof dependency on the item is introduced; new nodes have no proof dependencies. No elementary standalone lemma was manufactured: the generic node combines page induction, differential support/stabilization and finite filtered abutments; module-target finiteness combines the independent source sequence and module Ext finiteness. Both remain necessary proof tasks after removing elementary observations. There is no SGA source. No Lean file or compiler/build tool was used. The statement and all maintainer-owned fields are preserved exactly.

## Not duplicates

lem-trf-finite-module-target-rhom vs lem-trf-bounded-above-coherent-rhom: the item allows an arbitrary bounded-below coherent target; the new node handles only a finite module target.

lem-trf-finite-module-target-rhom vs lem-trf-source-hyperext-module-target: the existing node constructs a spectral sequence over any commutative ring with no finiteness assumptions or finite-generation conclusion.

lem-trf-finite-module-target-rhom vs lem-trf-coherent-rhom-finite-injective-dimension: the existing node allows an unbounded source and assumes a target of finite injective dimension; the new module target need not have finite injective dimension.

lem-trf-finite-module-target-rhom vs lem-sc-ext-support-cohomology-vanishing: the existing node gives support dimension and global cohomology bounds for sheaf Ext on a regular finite-dimensional scheme.

lem-trf-finite-module-target-rhom vs lem-sc-sheaf-ext-coherent: the existing node has two coherent sheaves in degree zero on a locally Noetherian scheme; the new node has a possibly unbounded-below source complex.

lem-trf-finite-module-target-rhom vs lem-per-algebraic-dualizing-ext-bounds: the existing node requires a normalized dualizing target over a nonzero local ring and proves dimension-indexed bounds.

lem-trf-finite-module-target-rhom vs lem-per-algebraic-dualizing-quotient: the existing node constructs a dualizing complex on a quotient ring, rather than giving finite-module-target derived-Hom cohomology.

lem-trf-noetherian-quadrant-abutment vs lem-trf-bounded-above-coherent-rhom: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the item allows an arbitrary bounded-below coherent target; the new node handles only a finite module target.

lem-trf-noetherian-quadrant-abutment vs lem-trf-source-hyperext-module-target: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node constructs a spectral sequence over any commutative ring with no finiteness assumptions or finite-generation conclusion.

lem-trf-noetherian-quadrant-abutment vs lem-trf-coherent-rhom-finite-injective-dimension: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node allows an unbounded source and assumes a target of finite injective dimension; the new module target need not have finite injective dimension.

lem-trf-noetherian-quadrant-abutment vs lem-sc-ext-support-cohomology-vanishing: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node gives support dimension and global cohomology bounds for sheaf Ext on a regular finite-dimensional scheme.

lem-trf-noetherian-quadrant-abutment vs lem-sc-sheaf-ext-coherent: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node has two coherent sheaves in degree zero on a locally Noetherian scheme; the new node has a possibly unbounded-below source complex.

lem-trf-noetherian-quadrant-abutment vs lem-per-algebraic-dualizing-ext-bounds: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node requires a normalized dualizing target over a nonzero local ring and proves dimension-indexed bounds.

lem-trf-noetherian-quadrant-abutment vs lem-per-algebraic-dualizing-quotient: the new node is an abstract A-linear shifted-quadrant spectral-sequence finiteness/stabilization theorem, with no derived Hom, schemes or dualizing objects; the existing node constructs a dualizing complex on a quotient ring, rather than giving finite-module-target derived-Hom cohomology.

Additional concept candidates: neither lem-sp-edge-collapse (collapse/edge isomorphisms) nor thm-sp-half-plane-convergence (convergence) gives finite generation over Noetherian rings. ModuleCat.finite_ext is already the Mathlib leaf lem-sc-ext-noetherian-finite and remains a tool for the future proof, not another new node.

## Validation

Server dry run completed successfully: deliver.py NX lem-trf-bounded-above-coherent-rhom --no-push exited 0 and printed OK (not pushed), preflight passed, temporary commit 2dbe80d7929. The server ran its DAG, split-review and delivery preflight checks. A local consistency read also confirmed that only proof, proof_deps and split_report changed on the item, that the statement is byte-for-byte unchanged, and that all four citation quotes are verbatim. The assembly is 1400 characters; its longest step is 715 characters. This report corrects the inspected FGModuleCat abelian-instance line to 35; the final report is rechecked by another dry run before push.
