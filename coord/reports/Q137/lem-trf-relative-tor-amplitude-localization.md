# Worker report: lem-trf-relative-tor-amplitude-localization

## Files written

- lem-trf-relative-tor-amplitude-localization: statement unchanged, four assembly steps, 2639 proof characters.
- lem-trf-relative-tensor-test-model-restriction: statement, unsplit, no Mathlib match.
- lem-trf-relative-tensor-localized-resolution-comparison: statement, unsplit, no Mathlib match.
- citations.json: exact statement quotations for every cited node in every parent step.

## Attachments

None. The project declaration `CochainComplex.relative_tensor_homology_vanish_iff_prime_localizations` in `lean/Sheaf/Algebra/Homology/RelativeTorAmplitudeLocalization.lean` ends in sorry. Searches under WeilConjectures by blueprint id and relative Tor-amplitude terminology found no exact completed declaration. Existing mixed-tensor restriction is a cochain comparison, not the new comparison with the fixed derived tensor.

## WANTED

None. All mathematical sources were available locally.

## Return repaired

The sandbox initially held only launcher marker files, not the purported retained split or report. I copied the current repository node, whose seven proof steps agree with the returned proof lengths, and continued that version. No repository or launcher file was changed. The current item statement is unchanged. The return asks for at least two statement-only nodes of comparable argumentative size; the two comparisons carry old step 1 (1263 characters, plus the explicit naturality of its roof) and old steps 3--4 (2156 characters). The parent keeps exact-localization reasoning and the two vanishing implications. Both new nodes have empty proof and proof_deps, null proof_origin and status unsplit. Their proofs can be assigned independently; neither asserts Tor-amplitude vanishing or either clause of the item. The entire old argument is recorded below, rather than discarded or compressed out of the task.

## What was wrong / unfinished

The existing proof was mathematically correct but carried too much comparison work in one item. No statement dispute or change of route was needed. The two new comparisons are intentionally unproved at stage 1 and ready for separate workers. No Lean was written or compiled.

## Review by Q137

### Repair against the current DAG (2026-10-23)

The sole current return is the side/live-completion landing refusal. I retained the returned sandbox delivery, including its two new statements, old-proof allocation, citations and actual search log. The required first dry run now passed on the freshly fetched server base at `04c867408da`. The current read clone still has the seven-step proof, not this four-step assembly; its item differs from the retained version only in proof, proof dependencies and split report. All other fields, including the historical review and Lean statement, agree. The released 2026-10-22 stage-1 repair order remains explicit and requires these two new nodes. Neither new id occurs in the current DAG. Thus this is a re-split of the live baseline under that order, and does not infer completion from the side project's review.

I reread every current parent citation and every definition used by either new statement. Step 1's resolution theorem supplies an arbitrary-unbounded K-flat resolution; the first new statement supplies the A-complex and its prescribed D(R) tensor comparison; exact localization and exact-functor cohomology apply with no boundedness. In step 2 the second new statement gives both a localized augmentation quasi-isomorphism and K-flatness, and an isomorphism specifically in D(A_q). I repaired the assembly's phrase “is K-flat” to “is a K-flat resolution” and named D(A_q) there, so its application of the first comparison over R_p has both hypotheses explicitly supplied. Restriction leaves the underlying kernels, images and cohomology groups unchanged. Step 3 uses invertible denominators on the restricted R_p-module L. Step 4 uses a proper annihilator, a containing maximal ideal, its written primality argument and the localization zero criterion. Every one of the ten citation quotes is still verbatim in its current statement, with no missing or extra step-node pair. No changed cited hypothesis or conclusion requires a replacement node.

I reopened Stacks more-algebra.tex at 0B67, 06Y1, 06Y4, definition-derived-tor and the signed tensor flip. The test-model comparison retains the A-action on K while resolving over R; the localized comparison uses exactly r/t mapped to phi(r)/phi(t). Its two inverse chain formulas respect both differentials and the unchanged Koszul sign; every total-complex element has finite support even for unbounded complexes. These are the two separate arguments requested by the re-split order, not the vanishing clauses of the item. The omitted forward implication of 0B67 remains proved by restricting the arbitrary localized test module. The reverse implication uses annihilators with no finite-generation assumption. Tests with R=A, Z to Z/2, K=0, N=0, A=0 and a=b still pass. No new statement or search question changed, so I reread and reused searches.jsonl; no unrun search was added. The renewed whole-blueprint searches for 0B67 and tensor localization returned no matching blueprint statement. The current project theorem in Sheaf/Algebra/Homology/RelativeTorAmplitudeLocalization.lean still ends in sorry, so it cannot close this item.

This repair changes the assembly and records its current-base justification, rather than only re-pushing the old branch. The delivery tool performs the rebase; no git command, Lean write, compiler, repository mutation or launcher edit was used. The preceding detailed review and complete old proof below remain retained.


### Continuation after the provider interruption

The initial dry run of this retry exited normally with `OK (not pushed)` at `cd9c4ef772d`; no delivery was left running and no push had occurred. I compared all three retained node files with the current read clone: both new ids remain absent, and the item differs only in proof, proof dependencies and split report. Its statement, statement dependencies, source, ancestry, Lean fields and maintainer fields agree with the current baseline. The current released stage-1 order still requires the two independent comparison nodes and a parent proof below 3000 characters. I retained both statements and all recorded searches, and made step 1 explicitly request a **K-flat resolution over R**, the hypothesis needed by the first comparison, rather than merely naming its augmentation. This is a clarification of the assembly on the current baseline, not a new hypothesis of the item.

For this retry I reopened every existing parent citation and both new comparison statements. The resolution statement applies to arbitrary unbounded module complexes, the localization theorem to arbitrary module sequences, the exact-functor theorem to every degree of an arbitrary complex, and the derived-category definition includes factored cohomology. The fraction definition includes the zero criterion and invertibility of denominators, and the maximal-ideal theorem applies to the proper annihilator without finite generation. All ten quotation entries are verbatim in the current statements and cover every step-node pair. I also reopened the K-flat and signed total-tensor definitions, and Stacks more-algebra.tex at definition-K-flat, lemma-base-change-K-flat (06Y1), lemma-K-flat-resolution (06Y4), definition-derived-tor, lemma-flip-douoble-tensor-product and lemma-tor-amplitude-localization (0B67). The derived comparisons preserve the contracted-prime base map; the formulas still cover arbitrary unbounded direct-sum totals. For the nonflat map Z to Z/2 no A-resolution is treated as R-flat. The zero complex, zero module, zero algebra and singleton interval need no additional assumption. No statement or citation changed, so the retained search results were reread and reused. The new nodes remain statement-only. The final dry run and push construct their rebased commits through the required delivery tool.


### Current-DAG repair of the landing refusal (2026-10-22)

The return names immutable delivery head `6b25945f9b7`, approved mathematically but refused because side completion had not been promoted to the live DAG. I continued the retained node files, report, citation packet and search log supplied for that delivery. Comparing the retained item to the current read clone shows differences only in `proof`, `proof_deps` and `split_report`: the current baseline still has the seven-step proof reproduced below, while the retained delivery has the two new comparison statements and four assembly steps. The item statement, statement dependencies, source, blueprint ancestry, Lean attachment and maintainer metadata agree. Neither new id exists in the current DAG. The released stage-1 re-split order remains present, so the old passing stage-1 review does not supersede this repair. The delivery tool constructs the actual rebased commit on freshly fetched `origin/sheaf-dag`; the initial dry run exited successfully at `4654ca4fa41` before this final clarification.

I opened every current cited statement rather than relying on the old review: `lem-pc-source-module-kflat-resolution` still supplies resolutions for arbitrary unbounded complexes; `lem-weil-pbc-localization-module-exact` still gives exactness for arbitrary module sequences; `lem-weil-pbc-exact-functor-complex-cohomology` explicitly supplies the natural cohomology comparison for an additive exact functor; `def-weil-abstract-derived-category` explicitly gives the factored cohomology functors; `def-weil-pbc-module-localization` still includes the fraction equality and zero criteria; and `lem-weil-pbc-proper-ideal-contained-in-maximal` still applies to every proper ideal. Their current statements contain all the retained quotation text. I also re-read `def-pc-module-kflat-complex` and `def-pc-tensor-complex-sheaves`, the definition inputs of both new statements. No changed hypothesis invalidates an application, and no citation needs replacing.

I adjusted assembly step 2 to say explicitly how the isomorphism in D(A_q) is used for cohomology over R_p: restrict scalars along the stated structural map; kernels and images are the same groups with the restricted action. This fills the categorical transition rather than leaving it implicit in the comparison. The two new statements and all prior argument allocations remain intact. Step 1 uses a resolution over R, step 2 uses its resolution over R_p, step 3 tests an arbitrary R_p-module by restriction to R, and step 4 uses arbitrary A-modules with no finite-generation assumption. I re-read Stacks 0B67, 06Y4, 06Y1 and the derived-tensor construction in more-algebra.tex and checked the nonflat map Z to Z/2, zero test module, zero complex, a=b and zero algebra cases again. Search results in searches.jsonl were re-read and reused because neither new statement nor its search question changed. No Lean or compiler command was run.


I read Stacks more-algebra.tex, lemma-tor-amplitude-localization (0B67), including its displayed cohomology identity and its omitted forward implication. Its R/A naming is reversed relative to this item, and it imposes no boundedness, flatness or finiteness. I also read the K-flat definition, quasi-isomorphism criterion, base-change lemma (06Y1), resolution existence (06Y4), definition-derived-tor and signed flip, and the derived-change-of-rings construction in the same file. These supply the source for both new comparisons. For the localization and final detection I read algebra.tex Proposition 00CS, Lemma 00HN and the maximal-ideal input's statement.

Parent step 1 uses the existing resolution theorem for arbitrary unbounded R-complexes, hence for N[0], and the new test-model node for the actual A-complex and its derived R-identification. The localization node states exactness of arbitrary module sequences, and the exact-functor node explicitly gives the natural cohomology isomorphism for arbitrary complexes. Additivity is the direct fraction formula, so this application has all its hypotheses. No source-algebra flatness was inferred.

Parent step 2 uses the new localized-resolution statement, which gives both K-flatness and the augmentation over R_p as well as an isomorphism in D(A_q), not just isomorphisms of groups. Applying the cohomology functor is part of the cited abstract-derived-category definition. Applying the first new node over R_p to A_q is legitimate because the second node supplies the localized K-flat resolution. Exact localization from step 1 then gives precisely the stated cohomology comparison. Every factor has the specified R_p to A_q map; it is never replaced by absolute Tor over A.

Parent step 3 uses the fraction definition: a pre-existing R_p-action makes all denominators invertible, so the two written maps really are inverse. The quantifier over all R-modules in (1) includes the restricted L. Parent step 4 uses only the proper-ideal/maximal-ideal statement, which really supplies the required containing maximal ideal, and the zero-fraction criterion, which really supplies an annihilating denominator. Primality of the maximal ideal is proved explicitly, not taken from an unstated node. No finite generation is used. These steps are elementary after the comparison.

For the first new node I checked the stronger compatibility claimed in its statement: in the old two-resolution roof, maps on either factor commute with the augmentation maps by tensor functoriality. A common K-flat refinement compares choices. This gives compatibility for maps of augmented test resolutions; multiplication on K is one such map. The existing fixed-second-factor derived functor constructs an A-valued functor but does not identify its restriction with the prescribed monoidal tensor in D(R), and the existing mixed restriction comparison is only a cochain comparison; these are tools for the future proof, not duplicate statements.

For the second new node I checked that t outside p implies phi(t) outside q, so every written denominator and the local ring map exist. Termwise localization of P is R_p tensor P by the explicit fraction maps recorded below. Scalar extension preserves K-flatness, and exactness preserves its augmentation quasi-isomorphism. The displayed chain formulas respect balancing, finite total sums, both differentials and the Koszul sign. The new statement gives the derived isomorphism represented by this chain isomorphism; no per-degree surrogate is substituted for it.

Edge cases checked for both nodes and parent: K=0; N=0; identity and nonflat ring maps (e.g. integers to integers mod 2); unbounded P,K with finite support for each element of a direct sum; a=b; zero A with empty spectrum. For nonflat maps all resolutions stay over the actual tensor base. No inversion or finite-generation hypothesis is needed. All non-elementary parent steps are under 2000 characters. I checked delivery-errors B--E: self-contained statements and notions, exact sources and recorded searches, derived forms, no new-node proof, verbatim citation coverage, no clause renaming, no route change, and no hidden SGA input.

## Preserved old proof and allocation

### Old step 1: New test-model restriction node.

Fix an $R$-module $N$, placed in degree zero. By [lem-pc-source-module-kflat-resolution] choose K-flat quasi-isomorphisms $P^\bullet\to N[0]$ and $F^\bullet\to\operatorname{Res}_R K^\bullet$. The tensor-model theorem [lem-pc-source-kflat-module-tensor-model] computes $K^\bullet\otimes_R^{\mathbf L}N$ by $\operatorname{Tot}(F^\bullet\otimes_R N[0])$. K-flatness [def-pc-module-kflat-complex] says tensoring on either side preserves quasi-isomorphisms. Since $P^\bullet$ is K-flat, the map $\operatorname{Tot}(F^\bullet\otimes_R P^\bullet)\to\operatorname{Tot}(K^\bullet\otimes_R P^\bullet)$ is a quasi-isomorphism; since $F^\bullet$ is K-flat, the map $\operatorname{Tot}(F^\bullet\otimes_R P^\bullet)\to\operatorname{Tot}(F^\bullet\otimes_R N[0])$ is also one. Hence $C_N^\bullet=\operatorname{Tot}(K^\bullet\otimes_R P^\bullet)$ computes the desired derived tensor. This argument applies to any supplied K-flat resolution of the test module. With the total differential of [def-pc-tensor-complex-sheaves], multiplication on the unchanged $K$ factor commutes with both differential terms, making $C_N^\bullet$ and $H^i(C_N^\bullet)$ actual $A$-modules. The auxiliary $F^\bullet$ is resolved over $R$; we never assert that an $A$-K-flat resolution is $R$-K-flat.

Original cited nodes: lem-pc-source-module-kflat-resolution, lem-pc-source-kflat-module-tensor-model, def-pc-module-kflat-complex, def-pc-tensor-complex-sheaves.

### Old step 2: Parent step 1; also the exactness input to the localized-resolution node.

For any commutative ring $B$, multiplicative subset $T\subseteq B$ and arbitrary $B$-complex $D^\bullet$, [lem-weil-pbc-localization-module-exact] says that termwise localization is exact. It is additive by the fraction formulas, so [lem-weil-pbc-exact-functor-complex-cohomology] gives $H^i(T^{-1}D^\bullet)\cong T^{-1}H^i(D^\bullet)$ in every degree. In particular localization preserves quasi-isomorphisms. We will use this first over $R$ with $T=R\setminus\mathfrak p$ and then over $A$ with $T=A\setminus\mathfrak q$; neither application needs a bounded complex.

Original cited nodes: lem-weil-pbc-localization-module-exact, lem-weil-pbc-exact-functor-complex-cohomology.

### Old step 3: New localized-resolution comparison node.

Fix a prime $\mathfrak q\subset A$, put $\mathfrak p=\varphi^{-1}(\mathfrak q)$ for the given map $\varphi:R\to A$, and set $P_{\mathfrak p}^\bullet=R_{\mathfrak p}\otimes_R P^\bullet$. The extension theorem [lem-pc-kflat-extension-of-scalars] makes this complex K-flat over $R_{\mathfrak p}$. Step 2 makes its augmentation to $N_{\mathfrak p}[0]$ a quasi-isomorphism. Here scalar extension equals termwise localization: $(r/t)\otimes u\mapsto ru/t$, with inverse $u/t\mapsto(1/t)\otimes u$, as the tensor and fraction relations verify. Consequently [lem-pc-source-kflat-module-tensor-model], with the two-resolution computation of Step 1 (now over $R_{\mathfrak p}$), computes $K^\bullet_{\mathfrak q}\otimes_{R_{\mathfrak p}}^{\mathbf L}N_{\mathfrak p}$ by $\operatorname{Tot}(K^\bullet_{\mathfrak q}\otimes_{R_{\mathfrak p}}P^\bullet_{\mathfrak p})$. The map $R_{\mathfrak p}\to A_{\mathfrak q}$ sends $r/t$ to $\varphi(r)/\varphi(t)$; it exists because $t\notin\mathfrak p$ implies $\varphi(t)\notin\mathfrak q$.

Original cited nodes: lem-pc-kflat-extension-of-scalars, lem-pc-source-kflat-module-tensor-model, lem-pc-source-module-kflat-resolution.

### Old step 4: New localized-resolution comparison node.

The ordinary tensor complexes in Steps 1 and 3 are related by an explicit $A_{\mathfrak q}$-linear chain isomorphism $$(C_N^\bullet)_{\mathfrak q}\longrightarrow\operatorname{Tot}(K^\bullet_{\mathfrak q}\otimes_{R_{\mathfrak p}}P^\bullet_{\mathfrak p}),\qquad (k\otimes u)/s\longmapsto(k/s)\otimes(u/1).$$ Its inverse on a homogeneous generator is $$(k/s)\otimes(u/t)\longmapsto(k\otimes u)/(s\varphi(t)),$$ where $s\notin\mathfrak q$ and $t\notin\mathfrak p$. The fraction relations of [def-weil-pbc-module-localization] and tensor balancing give well-defined maps: moving $r/t$ between the factors multiplies the numerator by $\varphi(r)$ or $r$ and introduces the same denominator $\varphi(t)$. The two composites fix every generator. Apply these formulas to finite sums of homogeneous generators; a common product of denominators puts any such sum over one denominator, so the maps also cover the direct sums in every total degree. Both maps commute separately with $d_K\otimes1$ and $(-1)^r1\otimes d_P$, with the same $r$ before and after localization. Thus they commute with the total differential, including for unbounded complexes.

Original cited nodes: def-weil-pbc-module-localization, def-pc-tensor-complex-sheaves.

### Old step 5: Parent step 2, applying cohomology to the derived comparison.

Apply cohomology to the chain isomorphism of Step 4, use Step 2 on its left side, and use the tensor models of Steps 1 and 3. This gives, for every $R$-module $N$, prime $\mathfrak q$ and integer $i$, the comparison $$H^i(K^\bullet\otimes_R^{\mathbf L}N)_{\mathfrak q}\cong H^i(K^\bullet_{\mathfrak q}\otimes_{R_{\mathfrak p}}^{\mathbf L}N_{\mathfrak p}).$$ The left side is localization of the actual $A$-module $H^i(C_N^\bullet)$, and the right side uses the specific structural map $R_{\mathfrak p}\to A_{\mathfrak q}$ of Step 3. This is a combination of the preceding computations, with no change from relative to absolute Tor amplitude.

Original cited nodes: .

### Old step 6: Parent step 3.

Assume (1), fix $\mathfrak q$, and let $L$ be any $R_{\mathfrak p}$-module. Use $N=L$ by restriction to $R$ in Step 5. Its localization satisfies $N_{\mathfrak p}\cong L$: send $l/t$ to $t^{-1}l$ and send $l$ back to $l/1$; these maps are inverse because each $t\notin\mathfrak p$ already acts invertibly. For $i\notin[a,b]$, assumption (1) makes the left side of Step 5 zero. Its right side, after this module isomorphism, is exactly $H^i(K^\bullet_{\mathfrak q}\otimes_{R_{\mathfrak p}}^{\mathbf L}L)$. It is zero. Since $\mathfrak q$ and $L$ were arbitrary, this proves (2), including the implication omitted in the source.

Original cited nodes: def-weil-pbc-module-localization.

### Old step 7: Parent step 4.

Assume (2), fix $N$ and $i\notin[a,b]$, and put $H=H^i(C_N^\bullet)$. Step 5 and (2), tested with $L=N_{\mathfrak p}$, give $H_{\mathfrak q}=0$ for every prime $\mathfrak q\subset A$. To conclude without a finiteness hypothesis, suppose $0\ne x\in H$. Its annihilator $I=\{a\in A:ax=0\}$ is a proper ideal. By [lem-weil-pbc-proper-ideal-contained-in-maximal] choose a maximal ideal $\mathfrak m\supseteq I$. It is prime: if $uv\in\mathfrak m$ and $u\notin\mathfrak m$, write $1=c+du$ with $c\in\mathfrak m$ and multiply by $v$ to get $v\in\mathfrak m$. As $H_{\mathfrak m}=0$, the fraction criterion of [def-weil-pbc-module-localization] gives $s\notin\mathfrak m$ with $sx=0$, contradicting $s\in I\subseteq\mathfrak m$. Hence $H=0$. All $N$ and all degrees outside the interval were arbitrary, so (1) holds. If $A$ is the zero ring, every $A$-module is zero already; the same argument is vacuous. The zero complex, $a=b$, and the identity ring map cause no exceptional step.

Original cited nodes: lem-weil-pbc-proper-ideal-contained-in-maximal, def-weil-pbc-module-localization.

For the first future proof, naturality is proved with the same two-resolution roof: tensor maps commute with f and h on homogeneous generators; comparison through a common refinement gives the resolution-independent square, including the multiplication endomorphisms. This makes explicit the natural A-action already used by the old proof. Existing helper statements to reuse are lem-pc-source-module-kflat-resolution, lem-pc-source-kflat-module-tensor-model, def-pc-module-kflat-complex, def-pc-tensor-complex-sheaves, lem-pc-mixed-tensor-restriction-comparison and lem-pc-derived-tensor-second-factor-functor. These are proof suggestions in this report, not proof dependencies on unsplit nodes.

## Mathlib search review

All new-node searches were run with the mandatory msearch.py and read before recording; searches.jsonl is the authoritative log, and each recorded result copies its log entry. Both phrasings for each comparison returned only ordinary localization/base-change, projective Tor, module flatness or categorical localization. I read Mathlib/RingTheory/Localization/BaseChange.lean, especially tensorProduct_isLocalizedModule at line 98 and IsLocalizedModule.rTensor at line 244: these are useful ordinary-module components but supply neither the signed unbounded complex comparison nor its derived restriction/K-flat resolution content in one line. Loogle's unknown IsKFlat identifier is recorded as a zero-result query, not as proof of absence; the other queries cover the concepts. No new node is a Mathlib leaf.

## Not duplicates

lem-trf-relative-tensor-test-model-restriction vs lem-trf-relative-tor-amplitude-localization: the existing item is a vanishing equivalence for all module tests; the new node gives a model/comparison and states no amplitude conclusion.

lem-trf-relative-tensor-test-model-restriction vs lem-trf-affine-relative-tor-amplitude-criterion: the existing statement compares sheaf-theoretic affine relative Tor amplitude, while the new statement is an explicit ring-complex comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-tor-vanishing-localized-algebra: the existing statement preserves one ordinary module Tor vanishing when an algebra is localized; it gives no unbounded complex or derived restriction comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-polynomial-tor-bound: the existing statement adds the polynomial-variable count to a Tor bound; the new node involves arbitrary ring maps and constructs an explicit derived comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-affine-sections-tor-bound-stalk: the existing statement transfers ordinary module Tor bounds from an affine chart to stalks, with no unbounded model comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-tor-vanishing-localized-base: the existing statement transfers one ordinary module Tor vanishing between tensor bases for already localized modules; it gives no explicit unbounded comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-localized-polynomial-tor-bound: the existing statement bounds Tor of a finite module over a localized Noetherian polynomial algebra; the new node has no such assumptions and no Tor-bound conclusion.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-tor-localization-denominators: the existing statement clears a denominator of one ordinary Tor class; the new node compares derived complexes with specified algebra actions.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-trf-relative-tor-amplitude-localization: the existing item is a vanishing equivalence for all module tests; the new node gives a model/comparison and states no amplitude conclusion.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-trf-affine-relative-tor-amplitude-criterion: the existing statement compares sheaf-theoretic affine relative Tor amplitude, while the new statement is an explicit ring-complex comparison.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-tor-vanishing-localized-algebra: the existing statement preserves one ordinary module Tor vanishing when an algebra is localized; it gives no unbounded complex or derived restriction comparison.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-polynomial-tor-bound: the existing statement adds the polynomial-variable count to a Tor bound; the new node involves arbitrary ring maps and constructs an explicit derived comparison.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-affine-sections-tor-bound-stalk: the existing statement transfers ordinary module Tor bounds from an affine chart to stalks, with no unbounded model comparison.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-tor-vanishing-localized-base: the existing statement transfers one ordinary module Tor vanishing between tensor bases for already localized modules; it gives no explicit unbounded comparison.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-localized-polynomial-tor-bound: the existing statement bounds Tor of a finite module over a localized Noetherian polynomial algebra; the new node has no such assumptions and no Tor-bound conclusion.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-pc-tor-localization-denominators: the existing statement clears a denominator of one ordinary Tor class; the new node compares derived complexes with specified algebra actions.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-source-kflat-module-tensor-model: the existing statement gives an objectwise K-flat tensor computation over a single ring; the new statement identifies the A-linear test model after restriction with the fixed D(R) tensor, naturally in maps of augmented resolutions and in K, including multiplication actions.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-derived-tensor-second-factor-functor: the existing functor has values in D(A) and a universal counit; it does not give the new restriction-to-the-prescribed-D(R)-tensor comparison.

lem-trf-relative-tensor-test-model-restriction vs lem-pc-mixed-tensor-restriction-comparison: the existing comparison is between ordinary cochain bifunctors; the new statement compares the resolved model to the fixed derived tensor and its action.

lem-trf-relative-tensor-localized-resolution-comparison vs lem-weil-pbc-localization-tensor-product: the existing result concerns two ordinary modules at one ring localization; the new result includes simultaneous R_p/A_q bases, a K-flat augmented resolution and signed unbounded total complexes in D(A_q).

lem-trf-relative-tensor-localized-resolution-comparison vs lem-weil-pbc-localization-tensor-over-base: the existing statement localizes only the first of two ordinary modules, with the tensor base still R; the new result changes the tensor base to R_p and compares unbounded total complexes while certifying the localized resolution.

Blueprint search: ancestor agrees with the retained ancestry. Whole-blueprint searches for tensor localization, localized tensor, K-flat resolution, test resolution, simultaneous, restriction comparison, test-resolution, simultaneous prime and 0B67 found no statement equal to either new node. Whole-DAG statement/title and tag searches, plus Lean source searches under both project roots, found the candidate helpers discussed above; their statements were opened before rejecting duplication.
