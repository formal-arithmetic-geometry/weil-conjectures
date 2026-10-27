# Stage-1 repair report: lem-sfb-prime-to-ell-derived-invariants-reduction

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-prime-to-ell-derived-invariants-reduction.json`: item, split; original statement and statement dependencies unchanged, now 2709 proof characters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-image-open-kernel-inflation.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-averaging-condensed-invariant-summand.json`: statement, unsplit; algebraic projector in Mathlib is only part of the assertion.
- `citations.json`: literal statement excerpts for every use in every parent step.

The sandbox initially contained only dispatcher markers, without the promised earlier node or report. The first required dry run exited with “no node files”. I copied the current repository node, including its prior proof, citations in the steps, search records, review metadata and Lean metadata; `returned-baseline.json` preserves that read baseline. No independent returned-head snapshot or earlier report was supplied. The current node's proof has precisely the eight lengths in the return (see preservation below), so this is the returned mathematical argument. No unchanged repush is being proposed.

## Attachments

None. Searches under `lean/WeilConjectures/` by blueprint tag and prime-to-ell/invariant concepts found no exact project declaration. `lean/Sheaf/Paper/PrimeToEllDerivedInvariantsReduction.lean` states the item but the main theorem and auxiliary obligations contain `sorry`; it cannot be attached as proved. The discrete-module fixed-lift theorem in `WeilConjectures/RepresentationTheory/DiscreteModule/Procyclic.lean` applies to discrete primary modules, not these ordinary internal norm-coefficient modules. No Lean was written or compiled.

## WANTED

WANTED: an exact external ordinary-condensed reference for the analytic scalar input, including the noncomplete norm field Omega, used by lem-sfb-finite-image-open-kernel-inflation through the existing lem-sfb-prime-to-ell-condensed-acyclicity.

WANTED: an external reference for normalized open-normal derived comparison and finite averaging on internal condensed coefficient modules, for lem-sfb-finite-image-open-kernel-inflation and lem-sfb-finite-averaging-condensed-invariant-summand. The blueprint paragraph is context, not a claim to provide these arguments. The inherited agent provenance and this reference obligation remain explicit; no SGA source is used.

## What was wrong and what changed

The maintainer's sole return is the human's batch5 re-split order: 6521 characters and eight steps left too much argument for one worker. Two independent, comparable tasks are now available, both with self-contained statements, status unsplit, no proof steps or proof dependencies, and actual leanfinder, loogle, grep and leansearch searches. The first task carries old steps 1–3 (2452 characters); the second carries old step 4 and the invariant-summand part of step 5, together with their coefficient normalization. They respectively handle the infinite pro-prime-to-ell kernel and the finite quotient, so neither restates the whole item or merely renames its conclusion. The parent uses their distinct conclusions to prove the original map is invertible, then keeps the old formal compatibility arguments. The complete original argument appears below without shortening. The assembly was not substituted for that argument in the record.

No statement error was found. No change to the chapter or unit route, statement, coefficient interpretation, noncomplete Omega, ordinary unbounded derived category, or canonical arrow is made. The current blueprint direct-images paragraph (3) gives the open-direct-image context; this remains the inherited analytic input to it. The ancestor search prints None, so both children use the inherited null ancestor and put this item before its inherited via chain; places are specific. Whole-blueprint searches for averaging, kernel inflation, derived invariants, finite averaging, finite image and invariant summand found no equivalent blueprint statement.

## Not duplicates

lem-sfb-finite-image-open-kernel-inflation vs lem-sfb-prime-to-ell-condensed-acyclicity: the existing node proves only the rank-one trivial scalar augmentation for a pro-prime-to-ell group; the new node includes finite-image kernel topology, the finite-rank augmentation and residual quotient-inflation isomorphism, without removing the finite quotient.

lem-sfb-finite-image-open-kernel-inflation vs lem-sfb-derived-invariants-normal-subgroup-comparison: the existing formal comparison does not prove its unit is invertible; the new node verifies that for the specific finite-dimensional norm-coefficient representation using scalar acyclicity and detection after forgetting actions.

lem-sfb-finite-image-open-kernel-inflation vs lem-sfb-profinite-algcl-derived-invariants-comparison: that comparison changes a union-of-finite-fields coefficient ring to all continuous functions and asserts an isomorphism after evaluation in D(Ab); the new node is internal and changes the acting group while retaining its coefficients.

lem-sfb-finite-image-open-kernel-inflation vs lem-sfb-prime-to-ell-cochain-finite-quotient-descent: that node compares explicit cochain complexes and explicitly does not identify them with derived invariants; the new node concerns actual derived invariants and a finite-image quotient.

lem-sfb-finite-averaging-condensed-invariant-summand vs lem-per-tame-invariants-arbitrary-base-change: the existing node is ordinary algebra over fixed rings. It has neither arbitrary internal condensed modules, the full generalized-element condition, sheaf epimorphism exactness nor the norm-topological identification for all continuous sections. Its algebraic projector is reused conceptually rather than duplicated as another algebraic assertion.

lem-sfb-finite-averaging-condensed-invariant-summand vs lem-sfb-condensed-product-action-inflation: the existing statement gives right adjoints and hence left exactness; it does not give finite averaging, preservation of epimorphisms, or scalar-extension topology of invariant summands.

lem-sfb-finite-averaging-condensed-invariant-summand vs lem-sfb-prime-to-ell-complete-scalar-integral: that node constructs integration on a possibly infinite profinite group over a complete field. The new node uses only a finite sum and has no completeness hypothesis on Omega.

Both new nodes vs lem-sfb-prime-to-ell-derived-invariants-reduction: the first stops at Q times L and the second works only on a finite group with arbitrary internal modules; the parent combines them using normalized composition. They are complementary arguments, not copies of the parent. There are no Stacks tags on these agent-formulated inputs and thus no new same-tag pair.

## Search evidence

Every new search entry is copied from an actual `msearch.py` log record in searches.jsonl, with identical tool and query, actual hit names/count and digest. A second semantic phrasing was run for each new task. I read the returned statements. Representation.isProj_averageMap and averageMap_invariant/id in Mathlib/RepresentationTheory/Invariants.lean (129–145) concern an ordinary representation over one ring and do not establish the new condensed statement in one line. Rep.coinvariantsShortComplex_shortExact concerns coinvariants, not exactness of these invariants. Rep.ofQuotient constructs an ordinary quotient representation only. The other search returned completion objects and solid/free condensed modules, which do not prove the inflation result. RingTheory/Invariant/Profinite.lean explicitly treats discrete ring actions and integrality. No result was recorded as a match merely for sharing words. All services answered successfully.

## Review by NE

I read the current source paragraph (3) and the chapter and unit records, then the complete baseline and the exact statements of every parent proof dependency. The source is unchanged for the item and both new nodes: this is an agent expansion under the analytic tame-inertia input, not a theorem claimed from the short blueprint paragraph. No nonexistent Stacks tag or forbidden source was substituted. I checked B–E of delivery-errors against these files.

Parent step 1 uses exactly the new open-kernel statement: its assumptions are the same finite-dimensional norm-topological representation and pro-prime-to-ell B as the item. It gives t_F in the internal derived category, not just an isomorphism of cohomology vector spaces. Parent step 2 uses exactly the new averaging statement's exact functor and theta_F; since B has image Q, V^B=V^Q. The normal-subgroup comparison permits G=K=Q and quotient 1, and its displayed c inf equation combined with the exact-functor clause of sk-def-sfb-derived-categories proves b_F invertible. Both source categories are Grothendieck abelian by that comparison, so the derived existence hypotheses are met.

Parent step 3 uses the comparison's successive-quotient composition clause, so the composite is the specified a_F, not an unspecified isomorphism; its normalized transpose clause gives exactly the original inclusion on H^0. Parent step 4 uses the same statement's naturality and coefficient clauses for the single quotient B to 1, requiring no common finite image for two representations. The averaging child's coefficient identity identifies the sources of that square under theta_F. Parent step 5 uses the comparison's K=1 identity normalization. The zero conclusions use only the isomorphisms already established. Each of these claims is available in a cited statement; citations.json includes separate literal quotes for the composition, transpose, naturality and coefficient clauses where needed.

For the kernel child's intended argument I checked that a finite subset of the Hausdorff matrix space is discrete, so continuity gives an open kernel. An open subgroup H of K is open in B; its B-core has finite index, so K/H is a quotient of a subgroup of a finite prime-to-ell B-quotient. A finite basis gives actual continuous inverse matrices over F, and finite direct sums of K-injectives are K-injective by the tuple-of-homotopies argument. This uses exactly the scalar augmentation of lem-sfb-prime-to-ell-condensed-acyclicity and the resolution-computation clause, not an assumed comparison with naive continuous cochains. The comparison's kernel clause identifies the underlying eta; lem-sfb-internal-action-site-presentation explicitly says forgetting creates kernels and cokernels and detects zero. Thus it detects the cohomology of the cone. I read its updated generated Grothendieck topology clause and did not assume the old precoverage satisfied bind.

For the averaging child's intended argument, each Q-valued continuous section is constant on a finite clopen partition. Permutation of the finite sum gives fixed generalized sections; the identity on fixed sections gives its image exactly. The product-action node gives the invariant right adjoint and left exactness. Epimorphisms are locally surjective on the underlying base sheaves because the action-site statement identifies cokernels with base sheafification of sectionwise cokernels; average a local lift to get an invariant lift. This is why the new exactness task is substantial and is not the algebraic projector in Mathlib alone. The invariant inclusion/projection on W are continuous; an image/kernel basis gives the product norm homeomorphism after either scalar extension. The finite sum commutes term by term with coefficient insertion. No compact-image descent to a finite subfield, integration over B, completion of Omega or solidification is used.

Small cases: B=1 yields K=Q=1; K=1 leaves quotient inflation as the identity. Q=1 gives average equal to the identity and an exact identity functor. V=0 gives the empty finite sum and zero derived objects. V^B=0 gives zero through theta and the finite exactness comparison. L=1 removes the residual action without changing any formula. The empty profinite set has its unique zero section. Nontrivial Q with zero fixed space is consistent with the splitting, and ell=2 causes no division issue since |Q| is odd (indeed every nonzero integer is invertible in E). These checks cover both F=E and the explicitly noncomplete F=Omega.

All non-elementary parent uses are cited. The old steps longer than two thousand characters are now distributed as independent tasks rather than hidden in a long new parent step. No new statement contains a proof sketch, and both new proof arrays and proof_deps are empty. No new node is an elementary duplicate of a comparison criterion; the formal exact-derived and composition consequences deliberately remain in the parent. Nothing remains unfinished in this stage-1 repair beyond the child proofs intentionally assigned as unsplit tasks and the inherited WANTED analytic reference.

## Preservation of the complete returned argument

The following eight texts are the returned proof verbatim. Steps 1–3 are assigned to lem-sfb-finite-image-open-kernel-inflation; step 4 and the invariant-summand part of step 5 to lem-sfb-finite-averaging-condensed-invariant-summand; the exact-derived beginning of step 5 and steps 6–8 remain parent assembly. Thus both new tasks retain their full intended arguments for later workers while carrying statement-only JSON. The finite-average coefficient equality in step 7 is also part of the second child's statement. No argument is discarded.

### Returned step 1 (733 characters)

Write $\rho:B\to\operatorname{GL}_E(V)$ for the action. Its kernel $K$ is open and normal: the finite set $\rho(B)$ is discrete as a subspace of the Hausdorff finite-dimensional matrix space, and $\rho$ is continuous. Thus $B/K=Q$. Every finite continuous quotient $K/H$ has order prime to $\ell$: $H$ is open in $B$, and its core $H_0=\bigcap_{b\in B}bHb^{-1}$ is a finite intersection because $[B:H]<\infty$. Then $B/H_0$ is a finite continuous quotient of $B$, and $K/H$ is a quotient of its subgroup $K/H_0$. Choose an $E$-basis of $V$, of size $d$. The corresponding maps $F\otimes_E V\cong F^d$ and their inverses are continuous matrices, so $V_F\cong C_F^d$ as $K$-modules with trivial action. If $d=0$ these are zero objects.

Uses: elementary

### Returned step 2 (675 characters)

Apply [lem-sfb-prime-to-ell-condensed-acyclicity] to $K$. It gives the canonical scalar augmentation $C_F[0]\to R\Gamma_K(C_F[0])$ as an isomorphism for both $F$. The same holds for $V_F$: take $d$ copies of a K-injective resolution of $C_F$; their finite direct sum is K-injective since a chain map from an acyclic complex to it is a tuple of $d$ null-homotopic maps, whose homotopies form a tuple. Termwise invariants preserve finite sums. Under the basis identification the augmentation is therefore the direct sum of $d$ scalar augmentations. This argument uses only finite sums, including the empty sum, and the resolution computation of [sk-def-sfb-derived-categories].

Uses: lem-sfb-prime-to-ell-condensed-acyclicity, sk-def-sfb-derived-categories

### Returned step 3 (1044 characters)

For $G=B$ use [lem-sfb-derived-invariants-normal-subgroup-comparison] with this $K$ and the given $L$, and write $T_F$ for its kernel invariants functor. Since $K$ acts trivially on $V_F$, $T_F(V_F)$ is $V_F$ with the residual $Q\times L$-action. The underlying map of $\eta_F:T_F(V_F)[0]\to RT_F(V_F[0])$ is exactly the augmentation in step 2, hence is an isomorphism. Use the generated Grothendieck action site of [lem-sfb-internal-action-site-presentation] over the small coherent profinite site; its base has finite limits and its group and coefficient ring are sheaves. Forgetting actions creates kernels and cokernels and detects zero by the final paragraph of that statement, so the cohomology of the cone vanishes before forgetting whenever it vanishes after forgetting. Consequently $\eta_F$ is an isomorphism in $D(\mathcal A_{Q\times L}(C_F))$. The normalized equation $c_F\operatorname{inf}_F=R\Gamma_{Q\times L}(\eta_F)$ now proves that $\operatorname{inf}_F:R\Gamma_{Q\times L}(V_F)\to R\Gamma_{B\times L}(V_F)$ is an isomorphism.

Uses: lem-sfb-derived-invariants-normal-subgroup-comparison, lem-sfb-internal-action-site-presentation

### Returned step 4 (1219 characters)

Put $m=|Q|$. For any internal $C_F$-module $M$ with $Q\times L$-action, the finite sum $e_M=m^{-1}\sum_{q\in Q}q$ defines an internal $L$-equivariant idempotent. A continuous $Q$-valued section is locally constant on a finite clopen partition; on each piece multiplication permutes the finite sum. Hence $\operatorname{im}e_M=M^Q$ for the full condensed notion of fixed sections. The scalar $m^{-1}$ is a continuous constant section of $C_F$, so is available also for $F=\Omega$. Invariants are left exact by [lem-sfb-condensed-product-action-inflation]. They preserve epimorphisms as well: an invariant section of a target has a local lift through an epimorphism of module sheaves, and averaging that lift gives an invariant lift of the same section. Here [lem-sfb-internal-action-site-presentation] uses the generated Grothendieck action topology and identifies the underlying cokernel with the sheafification on the base profinite site of the sectionwise cokernel. Thus the lifts are local on the base site; no composition property of the unsaturated action precoverage is needed. Thus $\Gamma_Q^L:\mathcal A_{Q\times L}(C_F)\to\mathcal A_L(C_F)$ is exact. This finite sum uses no integration over an infinite group.

Uses: lem-sfb-condensed-product-action-inflation, lem-sfb-internal-action-site-presentation

### Returned step 5 (856 characters)

Apply [lem-sfb-derived-invariants-normal-subgroup-comparison] with $G=K=Q$ and quotient $1$. Its comparison reads $R\Gamma_{Q\times L}(M)\cong R\Gamma_L(R\Gamma_Q^L(M))$. Exactness from step 4 and the exact-functor clause of [sk-def-sfb-derived-categories] identify $R\Gamma_Q^L(M[0])$ with $M^Q[0]$, through the canonical map. The normalized inflation equation therefore makes $b_F:R\Gamma_L(V_F^Q)\to R\Gamma_{Q\times L}(V_F)$ an isomorphism. On $V$, the finite average $e=m^{-1}\sum_q\rho(q)$ has image $V^B$; both its inclusion and its projection are continuous linear maps. Tensoring this splitting with $F$ identifies $F\otimes_E V^B$ with $\operatorname{im}(1\otimes e)$, with the subspace topology (choose a basis of the image and kernel). Applying continuous maps on every profinite test set proves $(V^B)_F=V_F^Q$, including residual $L$-actions.

Uses: lem-sfb-derived-invariants-normal-subgroup-comparison, sk-def-sfb-derived-categories

### Returned step 6 (614 characters)

The composite $t_F b_F$ has source $R\Gamma_L((V^B)_F)$ and target $R\Gamma_{B\times L}(V_F)$. The composition clause of [lem-sfb-derived-invariants-normal-subgroup-comparison] identifies it with the canonical inflation $a_F$ for $B\times L\to Q\times L\to L$ and the invariant inclusion. Thus $a_F$ is an isomorphism. Its degree-zero map is the original inclusion: the ordinary normalized transposes restrict codomain to invariants and their inverses compose with inclusion. Both source and target invariant submodules are the same $L$-fixed part of $V_F^B$, so this map is the identity after that identification.

Uses: lem-sfb-derived-invariants-normal-subgroup-comparison

### Returned step 7 (890 characters)

All maps used are canonical resolution maps, normalized inflation maps, or invariant inclusions. For an equivariant continuous $E$-linear map $f:V\to W$, $f\rho_V(b)=\rho_W(b)f$ implies $f(V^B)\subseteq W^B$ and equality of the two composites with invariant inclusions. The naturality clause of [lem-sfb-derived-invariants-normal-subgroup-comparison], applied directly to $a_F$ viewed as the single quotient $B\to1$, gives the requested naturality without choosing a common finite image or compatible bases. The coefficient clause of that node applied to $C_E\to C_\Omega$ and $v\mapsto1\otimes v$ gives $u_{B\times L}a_E=(\operatorname{Res}a_\Omega)u_L$. The invariant identifications of step 2 respect this map since $e_\Omega(1\otimes v)=1\otimes e_E(v)$, term by term in the same finite sum. Thus this is precisely the coefficient square in the statement, in ordinary condensed modules.

Uses: lem-sfb-derived-invariants-normal-subgroup-comparison

### Returned step 8 (473 characters)

If $B=1$, then $K=Q=1$, both kernel augmentations and the normalized comparisons in [lem-sfb-derived-invariants-normal-subgroup-comparison] are identities; invariant inclusion is also the identity. The composite in step 3 is therefore the identity. If $V=0$ the constructions are zero, and if $V^B=0$ step 2 gives zero derived invariants for $Q\times L$ and hence step 1 gives zero derived invariants for $B\times L$. No completeness assertion about $\Omega$ has been used.

Uses: lem-sfb-derived-invariants-normal-subgroup-comparison
