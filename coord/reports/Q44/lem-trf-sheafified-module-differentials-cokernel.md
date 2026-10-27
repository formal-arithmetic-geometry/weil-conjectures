# Q44 repair: lem-trf-sheafified-module-differentials-cokernel

## Files written

- dag/nodes/sec-trace-formula/lem-trf-sheafified-module-differentials-cokernel.json: unchanged statement, three assembly steps, 2126 proof characters.
- dag/nodes/sec-trace-formula/lem-trf-differential-presheaf-relation-cokernel.json: statement-only unsplit; no Mathlib match; 1684 statement characters.
- dag/nodes/sec-trace-formula/lem-trf-sheafified-free-relation-comparison.json: statement-only unsplit; no Mathlib match; 2362 statement characters.
- dag/nodes/sec-trace-formula/lem-trf-sheaf-derivation-relation-representability.json: statement-only unsplit; no Mathlib match; 1745 statement characters.
- citations.json: five entries, one per parent step/node citation, each quoting the cited statement verbatim.

## Attachments

None. CategoryTheory.SheafifiedDifferentials.sheafified_differentials_cokernel in lean/Sheaf/CategoryTheory/Sites/SheafifiedDifferentialsCokernel.lean ends in sorry. Searching lean/WeilConjectures for the exact blueprint tag and for sheafification/differential notions found no finished declaration covering the item. TangentSpace.lean defines scheme-specific differentials but does not prove this general site result.

## WANTED

None: all literature is present.

## What was wrong and what is repaired

The human return requires spreading the 5641-character proof over at least two comparable statement-only tasks, keeping the parent statement and at most 3000 assembly characters. The dispatched sandbox had no node files, report or searches, only .brief marker files. I copied the current repository item; its seven proof steps have exactly the lengths in the return. Its later maintainer-owned metadata is retained. The retained attempt recorded no git command, Lean write, compiler or Lake command. During this promotion repair I accidentally ran a read-only git status/log inspection in the shared repository; it changed no files. I disclosed this and stopped all direct git use. No Lean file, compiler, Lake, repository file, or launcher file was written or run.

Three new tasks carry every old argument: old 1-2 -> differential-presheaf-relation-cokernel; old 3-5 -> sheafified-free-relation-comparison; old 6-7 -> sheaf-derivation-relation-representability. The old steps are reproduced verbatim at the end of this report, with that assignment. The last normalization of old 7 also appears as the explicit calculation in parent step 3. No argument is discarded or replaced by a shorter description. The new tasks have self-contained hypotheses and notation, proof=[], proof_deps=[], proof_origin=null, status=unsplit. They have no dependencies on one another or the parent, so each can be assigned independently.

The first task is natural presheaf algebra and exact sheafification. The second is the free-generator and relation comparison. The third starts from any supplied cokernel of the sheaf relation map and proves representability and normalized uniqueness. None identifies a sheafified sectionwise differential module with a sheaf derivation representative; the parent establishes that by combining all three. Repeated relation formulas make each task readable on its own. The parent statement, all original hypotheses, and the coefficient category are unchanged.

## Review by Q44

I read Stacks sites-modules.tex section-differentials in full through lemma-differentials-sheafify: definition-derivation (04BK), lemma-universal-module (04BL), equation-define-module-differentials, definition-module-differentials (04BN), and lemma-differentials-sheafify (08TP), including the proofs. For the first new task, 08TP's displayed presheaf map and its sectionwise cokernel are the source; its last sentence is exact sheafification. I also read sites-modules.tex lemma-sheafification-presheaf-modules (03CY) and lemma-sheafification-exact (03EI), algebra.tex's three-relation construction, definition-differentials (07BK) and lemma-universal-omega (00RO). I opened the existing module-sheafification interface, abelian exactness, module-sheaf category, free-module and Kähler definition node statements. Each says the required ingredient: the interface is explicitly over a presheaf ring, exactness includes cokernels, and the Kähler definition contains the explicit quotient. The module-presheaf notion is written inline because the existing presheaf-module definition assumes a sheaf coefficient ring. The new task keeps semilinear restrictions, the actual maps r and p, and the unit formula, not just an abstract exact sequence.

For the second task I read the free-term identification in 08TP and the full free-generator construction in 04BL. I opened the statements of lem-pc-sites-sheafification-underlying-sets, lem-weil-pbc-site-sheafification-sections-local, the site definition, and the recently landed lem-trf-free-module-sheaf-universal-property. I read sites.tex lemma-sections-sheafification (00WK) and the alpha-to-zeta clauses of section-sheaves-algebraic-structures (00YR). Local representatives and local equality plus common refinements justify the binary-product comparison on arbitrary sites. The existing free-module sheaf universal-property lemma is a future proof input, not recreated. The new task includes the additional change of variable presheaf coefficients, arbitrary presheaf generators, normalization, comparison of direct sums, and the relation-map square. I checked the directions c_F r# = bar-r c_E and c_T(eta[t]) = i(eta t), including compatibility on all sheafified sections; equality on original generators is not mistaken for objectwise surjectivity of the unit.

For the third task I read 04BL from the free relation map through the final derivation factorization, and 04BN's representing-pair definition. It has an arbitrary supplied cokernel q and defines sheaf derivations by all three identities. Its conclusions include the inverse of the Hom/derivation bijection, naturality in the target, the unique isomorphism to any other representing pair, generator normalization and the cokernel map after this isomorphism. This is precisely the separate argument of old 6-7. It does not assume the conclusion of the parent or any presheaf-to-sheaf differential comparison.

I opened each of the three new statements after writing them and checked each assembly citation. Step 1 takes exactly r,p,P, the sheafified module cokernel and unit formula from the first task. Its explicit size wording follows the small site convention in the parent's definition node; it adds no parent hypothesis. Step 2 takes precisely the normalized free isomorphisms and relation square from the second task. The transfer of the cokernel is written as the correspondence of annihilating maps and unique factorization problems, a routine consequence of the two isomorphisms. Step 3 applies the third task to the actual sheaves A#, B#, psi=phi# and the transferred cokernel. The other two citations give the two equalities of its displayed normalization. Every one of the five citations.json quotations is a verbatim statement substring. No non-elementary fact is taken from a cited proof or left as an unnamed comparison. No parent step exceeds 2000 characters.

I tested all three statements on the one-object trivial site (ordinary rings), A=B (zero differential module), the zero ring, empty free generators (zero module), A -> A[x] (the generator [x] gives dx), and a non-sheaf ring presheaf with distinct locally equal sections. The last case uses local equality rather than unit injectivity. An empty covering forces terminal ring and zero module values on the covered object and all formulas still hold. There is no flatness, finite-type, scheme, enough-points, or exact-global-sections assumption.

Against delivery-errors B I checked self-contained objects, definition dependencies, single TeX escaping, source tags/labels and statement-only new nodes. Against C I checked actual cited statements and coefficient categories; all non-elementary parent inputs are cited and none is a definition substituted for a theorem. Old generic tools remain available to the future workers and are not falsely cited as giving the larger comparison. Against D the parent requires three independent arguments and its normalization calculation, not one relocated restatement; the new statements have no back edge. Against E the cokernels after sheafification are in sheaf modules rather than objectwise quotients, and restrictions are semilinear. The chapter and unit route are unchanged: this is generic module algebra below the inherited cotangent comparison, not a replacement trace argument. No SGA source is used.

## Search review

For each new id, two differently phrased LeanFinder searches, Loogle, grep and LeanSearch ran with the required msearch.py. All services answered this time. Exact outputs are retained in search-result-*.txt and searches.jsonl; the node records reproduce the actual query text (with grep's subdirectory appended). I read every hit. The pinned Mathlib Differentials/Presheaf.lean:185-242 supplies relativeDifferentials', derivation', relativeDifferentials'_map_d and isUniversal', only for presheaf differentials. Universal and Universal.mk at 85-175 quantify presheaf modules, not the sheaf relation cokernel. Presheaf/Free.lean:67-108 and Presheaf/Sheafification.lean:86-142 give separate free and sheafification adjunctions, not the normalized variable-generator relation comparison. Sheaf/Free.lean:39-75 has free sheaves indexed by a constant type; B(U) is a variable presheaf of generators. Quasicoherent.lean:38-130,150-180 supplies Presentation, presentationOfIsCokernelFree and mapRelations for supplied constant-index free presentations, not these differential maps. None is a one-line specialization giving a task.

Whole-DAG searches by tag, title and statement, and blueprint_refs searches for differentials, derivation, free module, sheafified free and cokernel found no existing blueprint statement equal to a new task. blueprint_refs ancestor returns lem-trf-local-term-locality. New via lists prepend this item to its existing via list. same_as remains [] for all four files. The inherited current blueprint locality proof was read to verify this remains a supporting underived cotangent input.

## Not duplicates

lem-trf-differential-presheaf-relation-cokernel vs lem-trf-sheafified-module-differentials-cokernel: the task constructs the natural presheaf relation map and its sheafified cokernel; it does not identify that quotient with the representing sheaf differential object.

lem-trf-differential-presheaf-relation-cokernel vs lem-trf-topos-inverse-image-differentials: the existing node concerns geometric inverse image between sites, not a natural presheaf presentation and its exact sheafification.

lem-trf-differential-presheaf-relation-cokernel vs lem-sfb-standard-sheaf-cotangent-augmentation: the existing node is a degree-zero homology and natural augmentation theorem for a polynomial cotangent resolution; the new task has no resolution or derived augmentation.

lem-trf-sheafified-free-relation-comparison vs lem-trf-sheafified-module-differentials-cokernel: the task compares free terms and relation maps before any quotient; it does not assert the differential comparison proved by the parent.

lem-trf-sheafified-free-relation-comparison vs lem-trf-topos-inverse-image-differentials: the existing node compares sheaf differentials under geometric inverse image, not ring/module sheafification of variable generators.

lem-trf-sheafified-free-relation-comparison vs lem-sfb-standard-sheaf-cotangent-augmentation: the existing node identifies the degree-zero homology of a polynomial resolution and its augmentation; this task compares free generator terms and a specified three-relation square.

lem-trf-sheafified-free-relation-comparison vs lem-trf-free-module-sheaf-universal-property: the existing node supplies the universal property for an already sheafified ring and generator sheaf; this task changes a presheaf coefficient ring and arbitrary presheaf generators to their sheafifications, including the binary-product comparison and relation square. The existing lemma can be reused in its future proof.

lem-trf-sheaf-derivation-relation-representability vs lem-trf-free-module-sheaf-universal-property: the existing node represents arbitrary maps out of a free generator sheaf. The task passes to the relation cokernel, represents derivations rather than arbitrary set maps and identifies arbitrary derivation representatives with the quotient.

lem-trf-sheaf-derivation-relation-representability vs lem-trf-sheafified-module-differentials-cokernel: the task starts from a supplied sheaf relation cokernel; it has no presheaf ring input or comparison to sheafified sectionwise differentials.

lem-trf-sheafified-free-relation-comparison vs lem-weil-pbc-free-module-sheaf-sheafify-first: the existing node has a constant coefficient ring R and only invariance under a generator map becoming an isomorphism, not simultaneous variable coefficient/generator sheafification and the relation square.

lem-trf-sheafified-free-relation-comparison vs lem-weil-pbc-free-module-sheafification-local-iso: likewise, constant-R local-isomorphism invariance is not the variable coefficient and relation comparison.

lem-trf-differential-presheaf-relation-cokernel vs lem-trf-geometric-inverse-image-free-module: the existing statement compares free module sheaves under geometric inverse image; it assumes sheaf coefficients and generators, whereas this task concerns presheaf differential presentation, presheaf-to-sheaf comparison, or a supplied differential-relation cokernel, respectively.

lem-trf-differential-presheaf-relation-cokernel vs lem-trf-geometric-free-module-hom-equivalence: the existing Hom chain assumes a geometric morphism between sheaf topoi and sheaf generators; it has no presheaf-ring differential relations or ring-sheafification comparison.

lem-trf-differential-presheaf-relation-cokernel vs lem-trf-normalized-free-module-comparison-calculus: the existing statement assumes normalized comparisons for finite-limit functors between sheaf topoi and proves their coherence; this task constructs the differential presentation, establishes presheaf-to-sheaf free comparisons, or proves derivation representability, respectively.

lem-trf-differential-presheaf-relation-cokernel vs lem-sfb-scheme-cotangent-transitivity: the existing theorem is the derived transitivity triangle and its augmentation for scheme morphisms; it does not state this arbitrary-site underived generator/relation task.

lem-trf-differential-presheaf-relation-cokernel vs lem-weil-pbc-sheaf-flat-separator: the existing theorem asserts existence of a flat separator in a sheaf category, not a differential presentation or comparison.

lem-trf-sheafified-free-relation-comparison vs lem-trf-geometric-inverse-image-free-module: the existing statement compares free module sheaves under geometric inverse image; it assumes sheaf coefficients and generators, whereas this task concerns presheaf differential presentation, presheaf-to-sheaf comparison, or a supplied differential-relation cokernel, respectively.

lem-trf-sheafified-free-relation-comparison vs lem-trf-geometric-free-module-hom-equivalence: the existing Hom chain assumes a geometric morphism between sheaf topoi and sheaf generators; it has no presheaf-ring differential relations or ring-sheafification comparison.

lem-trf-sheafified-free-relation-comparison vs lem-trf-normalized-free-module-comparison-calculus: the existing statement assumes normalized comparisons for finite-limit functors between sheaf topoi and proves their coherence; this task constructs the differential presentation, establishes presheaf-to-sheaf free comparisons, or proves derivation representability, respectively.

lem-trf-sheafified-free-relation-comparison vs lem-sfb-scheme-cotangent-transitivity: the existing theorem is the derived transitivity triangle and its augmentation for scheme morphisms; it does not state this arbitrary-site underived generator/relation task.

lem-trf-sheafified-free-relation-comparison vs lem-weil-pbc-sheaf-flat-separator: the existing theorem asserts existence of a flat separator in a sheaf category, not a differential presentation or comparison.

lem-trf-sheaf-derivation-relation-representability vs lem-trf-geometric-inverse-image-free-module: the existing statement compares free module sheaves under geometric inverse image; it assumes sheaf coefficients and generators, whereas this task concerns presheaf differential presentation, presheaf-to-sheaf comparison, or a supplied differential-relation cokernel, respectively.

lem-trf-sheaf-derivation-relation-representability vs lem-trf-geometric-free-module-hom-equivalence: the existing Hom chain assumes a geometric morphism between sheaf topoi and sheaf generators; it has no presheaf-ring differential relations or ring-sheafification comparison.

lem-trf-sheaf-derivation-relation-representability vs lem-trf-normalized-free-module-comparison-calculus: the existing statement assumes normalized comparisons for finite-limit functors between sheaf topoi and proves their coherence; this task constructs the differential presentation, establishes presheaf-to-sheaf free comparisons, or proves derivation representability, respectively.

lem-trf-sheaf-derivation-relation-representability vs lem-sfb-scheme-cotangent-transitivity: the existing theorem is the derived transitivity triangle and its augmentation for scheme morphisms; it does not state this arbitrary-site underived generator/relation task.

lem-trf-sheaf-derivation-relation-representability vs lem-weil-pbc-sheaf-flat-separator: the existing theorem asserts existence of a flat separator in a sheaf category, not a differential presentation or comparison.

## Exact accounting of the returned argument

The following is the original proof verbatim, retained in the report, not proof steps of any new unsplit node. Each argument has a named new task. The parent keeps the normalization calculation as well.

### Old step 1 -> lem-trf-differential-presheaf-relation-cokernel

Write $\varphi:\mathcal A\to\mathcal B$. For a presheaf of sets $T$, put $\mathcal B[T](U)=\bigoplus_{t\in T(U)}\mathcal B(U)[t]$, with restrictions sending $b[t]$ to $b|_V[t|_V]$; this is the free module in the sense of [def-weil-pbc-free-module]. Form $F=\mathcal B[\mathcal B]$ and $E=\mathcal B[\mathcal B\times\mathcal B]\oplus\mathcal B[\mathcal B\times\mathcal B]\oplus\mathcal B[\mathcal A]$. Define $r:E\to F$ by $[(a,b)]\mapsto[a+b]-[a]-[b]$ on the first summand, $[(f,g)]\mapsto[fg]-g[f]-f[g]$ on the second, and $[h]\mapsto[\varphi(h)]$ on the third. Restrictions commute with these formulas because they preserve addition, multiplication and $\varphi$. The sectionwise quotient $P(U)=F(U)/\operatorname{im}r_U$ is $\Omega_{\mathcal B(U)/\mathcal A(U)}$ with $d_U(b)$ the class of $[b]$, by the explicit quotient construction in [def-weil-pbc-kahler-differentials]. Thus $P$ is the desired presheaf of differentials, with restrictions $d_U(b)\mapsto d_V(b|_V)$.

Existing inputs: def-weil-pbc-free-module, def-weil-pbc-kahler-differentials.

### Old step 2 -> lem-trf-differential-presheaf-relation-cokernel

Apply [lem-pc-sites-module-sheafification-interface] with the presheaf ring $\mathcal O=\mathcal B$ to $E,F,P$. Their abelian sheafifications acquire the canonical $\mathcal B^\#$-module structures and $r$ and $F\to P$ sheafify to linear maps. By [lem-weil-pbc-sheafification-exact], the abelian cokernel presentation $E\xrightarrow r F\to P\to0$ sheafifies to a cokernel presentation. The cokernel in $\mathcal B^\#$-module sheaves has the same underlying abelian cokernel by [def-weil-sheaf-of-modules-category]. Consequently $Q=P^\#$, with $q:F^\#\to Q$, is the cokernel of $r^\#:E^\#\to F^\#$ in module sheaves.

Existing inputs: lem-pc-sites-module-sheafification-interface, lem-weil-pbc-sheafification-exact, def-weil-sheaf-of-modules-category.

### Old step 3 -> lem-trf-sheafified-free-relation-comparison

By [lem-pc-sites-sheafification-underlying-sets], the underlying set maps $\mathcal A\to\mathcal A^\#$ and $\mathcal B\to\mathcal B^\#$ are set sheafifications. The map $\mathcal B\times\mathcal B\to\mathcal B^\#\times\mathcal B^\#$ is also a set sheafification: by [lem-weil-pbc-site-sheafification-sections-local], a pair of sheafified sections lifts locally to two original sections after taking a common covering refinement, and two lifts of the pair agree after a further common refinement. Given a map from $\mathcal B\times\mathcal B$ into any sheaf of sets, apply it to these local lifts; local equality makes their values agree on overlaps, so they glue uniquely. This is exactly the universal property of sheafification. The common refinements are obtained by the covering pullback and composition axioms in [def-weil-pbc-sites-and-cohomology].

Existing inputs: lem-pc-sites-sheafification-underlying-sets, lem-weil-pbc-site-sheafification-sections-local, def-weil-pbc-sites-and-cohomology.

### Old step 4 -> lem-trf-sheafified-free-relation-comparison

For each $T=\mathcal B,\mathcal B\times\mathcal B,\mathcal A$ and any sheaf $N$ of $\mathcal B^\#$-modules, [lem-pc-sites-module-sheafification-interface] gives $\operatorname{Hom}_{\mathcal B^\#}(\mathcal B[T]^\#,N)=\operatorname{Hom}_{\mathcal B}(\mathcal B[T],N)$. A map on the right is uniquely the linear extension of a map of set presheaves $T\to|N|$: send $\sum b_t[t]$ to $\sum b_t v(t)$. Conversely evaluating at $[t]$ recovers $v$, and both constructions commute with restrictions. By the universal property [def-weil-pbc-sheafification] and Step 3 this equals $\operatorname{Hom}_{\mathrm{Sh}(\mathcal C)}(T^\#,|N|)$. Thus $\mathcal B[T]^\#$ is the free $\mathcal B^\#$-module sheaf on $T^\#$, with its specified generators. In particular $F^\#$ is free on $\mathcal B^\#$.

Existing inputs: lem-pc-sites-module-sheafification-interface, def-weil-pbc-sheafification.

### Old step 5 -> lem-trf-sheafified-free-relation-comparison

The same adjunction identifies $E^\#$ with the sum of the two free sheaves on $\mathcal B^\#\times\mathcal B^\#$ and the free sheaf on $\mathcal A^\#$: a map from $E^\#$ to $N$ is just three maps from its summands, by [lem-pc-sites-module-sheafification-interface]. Under these identifications $r^\#$ is the sheaf relation map with the three formulas of Step 1, now for sheafified sections. Indeed both maps take the original generators to those displayed relations; equality on the original generators implies equality before sheafification by linear extension and then after sheafification by uniqueness in that adjunction. This also proves that sheafifying introduces no additional choice in the relation map.

Existing inputs: lem-pc-sites-module-sheafification-interface.

### Old step 6 -> lem-trf-sheaf-derivation-relation-representability

Let $j:\mathcal B^\#\to|F^\#|$ be the free-generator map from Step 4 and put $d=qj$. The three relations of Step 5 vanish in $Q$, so $d(a+b)=d(a)+d(b)$, $d(fg)=g\,d(f)+f\,d(g)$ and $d(\varphi^\#(h))=0$ for sections of the sheafified rings. Thus $d$ is a sheaf $\mathcal A^\#$-derivation. For any $\mathcal B^\#$-module sheaf $N$ and any such derivation $D:\mathcal B^\#\to N$, Step 4 extends $D$ uniquely to a linear map $v:F^\#\to N$. Each of the three generator formulas for $vr^\#$ is zero by the corresponding derivation identity, hence $vr^\#=0$. The cokernel property of Step 2 gives a unique $\alpha:Q\to N$ with $\alpha q=v$, and therefore $\alpha d=D$. Conversely a linear map $\alpha$ produces the derivation $\alpha d$. These constructions are inverse: $\alpha q$ is determined by its generator values and a map out of the cokernel is determined after $q$. This verifies the representing property for sheaf derivations directly.

Existing inputs: the preceding steps.

### Old step 7 -> lem-trf-sheaf-derivation-relation-representability

It follows that $(Q,d)$ is a module of differentials of $\mathcal A^\#\to\mathcal B^\#$. If $(\Omega,d_{\mathrm{sh}})$ is any other representing module, apply the two universal properties to obtain maps $Q\to\Omega$ and $\Omega\to Q$ carrying the universal derivations to each other. Each composite fixes the universal derivation and hence is the identity by uniqueness. This gives the canonical isomorphism $P^\#=Q\cong\Omega_{\mathcal B^\#/\mathcal A^\#}$. For $b\in\mathcal B(U)$, the image of $d_U(b)$ in $Q(U)$ is $q([\eta_{\mathcal B}(b)])=d(\eta_{\mathcal B}(b))$, so the isomorphism carries every sectionwise universal derivation to $d_{\mathrm{sh}}$. Steps 2 and 5 give exactly the asserted common sheafified-cokernel presentation, completing all clauses.

Existing inputs: the preceding steps.


## Repair of the promotion refusal (2026-10-22)

The return says the independently approved side-project completion was never promoted to the live DAG read by the queue. I retained the delivered three tasks, their complete old-proof accounting, and the logged searches instead of recreating them. The required first dry run rebuilt these files over the delivery tool's freshly fetched server DAG and passed, producing dry-run receipt 22fd8749fe4 (not a push). I compared original-item.json with the current live parent JSON: every field agrees. Comparing the retained parent to live shows only the intended proof, proof_deps, and split_report differences; the statement, source, definition dependencies, blueprint ancestry and all maintainer-owned stage-2/review records agree. The three new task ids remain absent from the shared live DAG, so the side completion has not silently superseded this delivery. The live released stage-1 keep_plan repair note still orders at least two tasks and at most 3000 parent proof characters.

I re-read all six current definition statements used by these files: sites-and-cohomology, free-module, kahler-differentials, sheafification, presheaf-modules-sheafification, and sheaf-of-modules-category. None is merged or has a blueprint_update. In particular the site definition is small; the module-sheafification definition assumes a sheaf coefficient ring and is used only for R[S]; the presheaf-ring action in the other construction is stated explicitly; and the module-category statement describes cokernels as sheafified sectionwise cokernels. I re-read Stacks 08TP/04BL/04BN with the three retained task statements open. They still supply every clause used by the assembly, with no changed hypothesis to repair. I also read the current scheme-only relativeDifferentialsHomEquiv in WeilConjectures/AlgebraicGeometry/Modules/Differentials.lean: it concerns the structure sheaf and presheaf inverse image of a scheme morphism, and does not state the arbitrary-site presheaf-ring theorem or its relation presentation. The general parent declaration in Sheaf still ends in sorry.

The split adjustment is explicit in step 2: an annihilating h on the sheaf free term gives h c_F, whose composite with r# is h bar-r c_E = 0; the first task's cokernel gives unique alpha with alpha q = h c_F, equivalently alpha bar-q = h. This checks the direction of both comparison isomorphisms without appealing to an unnamed transport. I replaced the final step's two generic citation quotes with the exact generator normalization and unit formula that its displayed calculation uses. All five quotes remain literal substrings of the cited task statements. No statement or search question changed, so I read the saved search outputs and reused searches.jsonl without repeating or inventing a search. The next dry run rejected the short unit-formula quote under its 40-character minimum; I expanded it to the full formula sentence including its unit definition. The quote remains verbatim. The final dry run and push are rebuilt after these report, citation, and assembly changes.

The current same-tag search also found the geometric-free-module Hom and normalized-comparison tasks landed since the retained report. I read their statements: they take already sheafified generators and coefficients and a functor between sheaf topoi. Neither states the change from ring presheaves and set presheaves to their sheafifications. They may be future tools, but neither replaces any retained task or the 08TP route.

## Current-DAG promotion retry verification (2026-10-22)

The required initial dry run completed with OK (not pushed), head e67e8a069dc. I compared the saved original-item.json against the current shared item field by field; there are no changed fields. Therefore none of its cited definitions or its inherited Lean/review records calls for a statement change. I re-opened all three retained task statements, all six definition statements they use, the released stage-1 keep_plan order, and Stacks sites-modules.tex lines 5915-6085 (04BK, 04BL, 04BN, 08TP). The site is small, the free sheaf construction uses sheaf coefficients, and the presheaf coefficient action is explicitly extended under sheafification. These hypotheses remain exactly those of the old route.

This retry makes an additional mathematical check explicit in parent step 2: the proposed transferred cokernel actually annihilates the transferred relation map, by bar-q bar-r = q c_F^{-1} bar-r = q r# c_E^{-1} = 0. Together with the already explicit unique factorization, this verifies both parts of the cokernel claim and both inverse directions without an implicit transport. Step 1 still supplies the presheaf cokernel, and step 3 still uses the generator-normalized comparison and unit formula; I checked all five citation quotes against the retained statements. The statement is unchanged and the complete old seven-step argument remains preserved below.

I repeated the attachment inspection in the current library: the exact parent tag occurs in Sheaf with a sorry proof, while the matching notions in WeilConjectures concern scheme-relative differentials and do not give the arbitrary-site theorem. I re-read the saved search outputs and log, retaining the existing searches because neither a task statement nor a search question changed. Whole-DAG tag and blueprint concept searches still distinguish the presheaf-to-sheaf comparisons from the geometric inverse-image tools. The three task ids remain absent from current live. No direct git command, Lean writing, or compiler/build command was used in this retry. The delivery tool will build and push the revised assembly and this report over its fetched server DAG; promotion and landing remain the maintainer's operation.

## Promotion return repaired against current DAG (2026-10-23)

The return is the promotion refusal, not a mathematical rejection: L approved the side delivery but the queue still reads the old live split. The mandatory initial dry run completed with OK (not pushed) at 90ec613e71f. I compared the saved original-item.json and the shared live parent field by field: no fields changed. The retained delivery differs from live only in proof, proof_deps and split_report. I rebuilt the parent from that current live JSON and reapplied those three fields, preserving its statement, blueprint, statement dependencies, source, inherited reviews and Lean metadata. The three supplied prerequisite ids are still absent from live. The delivery command, rather than a direct git operation, rebases the delivery over its freshly fetched server DAG.

With the current statements open, I rechecked all six definition dependencies: the site convention is small; free modules allow empty index sets; the algebraic differentials definition gives all three relations; sheafification is its adjunction; module sheafification over a fixed sheaf ring is used for R[S]; and module cokernels are sheafified sectionwise cokernels. None of these nodes is merged or carries a blueprint_update. I also re-read the released stage-1 keep_plan repair order, the chapter and unit records, and sites-modules.tex lines 5915-6088 (04BK, 04BL, 04BN and 08TP). No changed citation or hypothesis requires changing a retained task statement. Step 1 uses the first task's actual presheaf and sheaf cokernel. Step 2 uses the second task's normalized comparison square, with its vanishing and unique factorization checked explicitly. Step 3 uses the third task's representing property, and the other two tasks' exact generator and unit formulas. I checked all five citation quotes as literal substrings of the corresponding current task statements.

This retry changes the final assembly step mathematically: it now names the chosen target's universal derivation d_sh, records e d = d_sh, and applies e_U to the normalization identity to give e_U(eta_P(d_U b)) = d_sh,U(eta_B b) explicitly. Thus the compatibility clause is verified in the chosen target, with the directions of e and the sheafification units visible. The old seven-step argument remains preserved in this report; the three tasks remain independent and statement-only. Every parent step is below 2000 characters and the total stays below 3000.

I repeated the project attachment search: the exact arbitrary-site theorem in Sheaf/CategoryTheory/Sites/SheafifiedDifferentialsCokernel.lean:133 still ends in sorry at line 175. The source in WeilConjectures gives scheme-relative differentials (relativeDifferentialsHomEquiv in AlgebraicGeometry/Modules/Differentials.lean), with scheme structure sheaves as hypotheses, rather than this arbitrary-site presheaf-ring relation comparison. I read the saved search outputs and searches.jsonl and retained them because neither the task statements nor their search questions changed. The blueprint concept search and whole-DAG tag search still distinguish the ring-presheaf comparison from the existing geometric free-module tools and the condensed tensor/action results. The latter assume condensed sheaf rings on the profinite site and do not state any of these three arbitrary-site tasks.

For the B-E review in this retry, I checked the new statements introduce their own objects, retain the explicit relations and sources, and have no proofs or back edges; the parent uses statements rather than hidden arguments from cited proofs. On the trivial one-object site the assembly is the ordinary differential relation quotient. For A=B or the zero ring the universal derivation is zero and both sides are zero. With noninjective sheafification units the displayed normalization still uses only their naturality and generator formulas, never injectivity; empty generators and empty coverings cause no exception. No additional flatness, enough-points, finite-type or global-section exactness hypothesis entered. All writes and the rebase preparation in this retry were confined to the sandbox; no direct git, Lean edit, compiler or Lake command was used.

## Unfinished work

The three new tasks intentionally remain unsplit for other workers. All work required for the assigned parent split is complete, subject to the required server dry run and push.
