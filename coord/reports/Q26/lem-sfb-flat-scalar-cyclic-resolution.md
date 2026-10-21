# Q26 repair: lem-sfb-flat-scalar-cyclic-resolution

1. Files written (all in the assigned sandbox):
   - `dag/nodes/sec-six-functors-basics/lem-sfb-flat-scalar-cyclic-resolution.json`: existing statement retained verbatim; proof replaced by a three-step assembly of 1165 characters.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-flat-constant-module-scalar-mono.json`: statement, unsplit, no Mathlib match. Regularity after constant sheafification and flat module-sheaf tensor, for any commutative ring with a specified injective scalar, not just a flat algebra over a domain.
   - `dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-mono-cokernel-kflat.json`: statement, unsplit, no Mathlib match. The specified cokernel augmentation for any injective map between finite free module sheaves, including term-flatness and the K-flatness of the two-term and single-term complexes.
   - `citations.json`: one verbatim statement quote for each of the four parent citations.
   - `report.md`: this report, review and full argument transfer. `returned-proof.json` retains the exact six old proof steps; local repair scripts and the genuine `searches.jsonl` log are ancillary sandbox files.

2. Attachments: none. The exact blueprint tag and scalar-resolution names had no finished declaration in `lean/WeilConjectures/`. The recorded `lean/Sheaf/Algebra/Homology/FlatScalarCyclicResolution.lean` was read completely: `SheafOfModules.flat_scalar_cyclic_resolution` ends in `sorry`. Its definitions specify the actual scalar multiplication, cone, quotient and normalized augmentation. No Lean file was written and no compiler or Lake command was run.

3. WANTED: none. All sources needed for this re-split are available locally.

4. What required repair: this is the explicit human-directed re-split of an already reviewed node, not a fresh review that declines the assignment because it was already split. The assigned sandbox had only dispatcher brief markers and no retained node, report or searches; I copied the current shared item before editing. The existing statement is correct. Its six-step proof concentrated two independent mathematical arguments in one node. They now have separate, self-contained statements and remain unsplit for other workers. The item keeps its statement, statement dependencies, Lean metadata and import/review metadata. Only its stage-1 proof, proof dependencies, proof origin and split report are changed. No source or target statement was weakened, and no unit or chapter route was changed.

5. What remains unfinished: the two new nodes deliberately have `status: unsplit`, empty `proof` and `proof_deps`, and null `proof_origin`. Their future proofs are separate work items. The present stage-1 delivery is the completed decomposition, not a claim that those Lean proofs exist.

## Repair of the numbered return

The return requests work distribution, at least one genuinely smaller new statement-only node, and an assembly of at most 3000 characters. This delivery adds two such nodes and keeps a 1165-character assembly. They distribute the old argument as follows:

- Old Steps 1-2, including exact module sheafification, constant scalar identification, flat tensor preserving the injection, the tensor-unit maps and sectionwise kernels, belong to `lem-sfb-flat-constant-module-scalar-mono`.
- Old Steps 3-5, including construction of the quotient augmentation and its cochain equation, every cohomology degree, the tensor-unit proof of regular-module flatness and zero-flatness, boundedness above by zero, and the bounded-above flat K-flat criterion, belong to `lem-sfb-finite-free-mono-cokernel-kflat`.
- Old Step 6 uses the already existing node `lem-weil-pbc-ringed-projection-mate-exact`; its explicit one-K-flat-factor clause already states this argument and is still cited in parent Step 3.

Every argument is preserved below, verbatim for the old six steps. The generalizations in the two new statements do not move the entire item into a successor: the first has no quotient or K-flatness claim; the second assumes a monomorphism and has no domain, constant coefficient, flat scalar extension or derived tensor claim. They can be proved independently and neither depends on the parent or on the other. The parent connects them by proving scalar regularity in a domain, specializing the first to the underlying flat module of R, and specializing the second to the now-established R-linear monomorphism with both ranks one.

## Searches and source reading

Read the chapter `sec-six-functors-basics`, the unit `sk-lem-integral-models`, and the current blueprint `main-20261015` integral-models operations proof, especially paragraph (2) on tensoring local scalar models using flat resolutions. `tools/blueprint_refs.py ancestor` returns `det-lem-integral-models-operations`; both new nodes have that ancestor and `via: [lem-sfb-flat-scalar-cyclic-resolution]`. Whole-blueprint searches included scalar quotient, two-term, nonzero scalar, cokernel, flat module, regular element, monomorphism of, finite free, flat constant, and nonzero divisor. No blueprint node states either proposed lemma. Whole-DAG source-tag and statement/title searches were also read, not just the unit's nodes.

For the first new node I read Modules on Sites Tag 03EI (`lemma-sheafification-exact`, lines 874 ff.) and Tag 03ER (`definition-flat`, clause (3), lines 4243 ff.); I also read the constant-exactness comparison at Tag 093J (`lemma-constant-exact`, lines 8198 ff.). Exactness is for module sheafification over the constant *presheaf* ring and yields module sheaves over its associated ring sheaf. The flatness used subsequently is exactness of *sheaf tensor*, not an unsupported claim about sectionwise ordinary flatness. No enough-points argument is used.

For the second I read Cohomology on Sites Tag 06YQ (`lemma-bounded-flat-K-flat`, lines 3120 ff.), and Homology Tag 0115 (`definition-quasi-isomorphism-cochain`, lines 3160 ff.), together with the preceding cohomology formula. The finite-free term argument is the tensor-unit calculation from Modules on Sites, section `section-tensor-product` (Tag 03EK), applied componentwise to a finite direct sum; the full calculation appears below. For the parent's last step I read the construction immediately preceding Tag 06YU (`definition-derived-tor`, lines 3260-3312): fixing a K-flat representative of one factor yields the stated total-tensor representative for every unbounded other factor.

Every Mathlib search in a new node was actually run with the required `msearch.py Q26 lem-sfb-flat-scalar-cyclic-resolution ...` command, and is present with its identical tool/query in `searches.jsonl`. Each new node records two differently phrased semantic searches (LeanFinder and LeanSearch), Loogle, and grep, with follow-up greps directed at the candidate files/subdirectories. No service failed in these searches.

For the first, LeanFinder and LeanSearch found `Module.Flat.isSMulRegular_of_isRegular` and `Module.Flat.isSMulRegular_of_nonZeroDivisors`. I read `Mathlib/RingTheory/Flat/TorsionFree.lean:51` and `:79`. They concern ordinary ring modules, not an arbitrary module sheaf whose flatness is exact sheaf tensor. Loogle found presheaf mono criteria, also only a piece of the desired argument. Targeted grep in `Algebra/Category/ModuleCat/Sheaf` found no constant-flat scalar statement. Thus the sheafification and flat sheaf-tensor argument remains, and the node is unsplit rather than a Mathlib leaf.

For the second, Loogle found `CochainComplex.mappingCone.quasiIso_descShortComplex`; grep located it at `Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:137`, with `inr_descShortComplex` at line 56. I read the construction and its short-exact hypothesis. It supplies the normalized quasi-isomorphism once the short exact complex is supplied, but not flatness or K-flatness of these sheaf complexes. LeanSearch/LeanFinder found free-sheaf cokernel presentations and ordinary-module flatness results; I read the relevant presentation constructors in `Sheaf/Quasicoherent.lean`. The KFlat/kFlat search had no homological hit (the three regex hits in TuringMachine/Tape.lean were ListBlank.flatMap). These are useful future proof ingredients, not a one-line match of the whole new statement.

## Review by Q26

I checked the source statements and every new hypothesis against the actual application. In Step 1 the elementary domain calculation verifies precisely the injective-scalar hypothesis of `lem-sfb-flat-constant-module-scalar-mono`. Its statement explicitly permits any flat A_C-module M, so restriction of the given R-algebra to its underlying A_C-module is admissible. Its conclusion supplies injectivity on every object's sections. I opened `def-weil-sheaf-of-modules-category`: it explicitly states that kernels are sectionwise. Multiplication by a scalar from a commutative algebra is R-linear, and the zero kernel therefore makes it monic also in the R-module category; no exactness of a forgotten functor is assumed.

In Step 2 I read the entire new finite-free-monomorphism statement: it quantifies over any small site and any commutative ring sheaf, arbitrary finite ranks and any supplied monomorphism. Its ranks can be m=n=1, P=Q=R, and the R-linear injection is supplied by Step 1. Its cokernel is the sheaf cokernel, not an erroneously sectionwise-surjective quotient. Its specified epsilon has degree-zero component exactly q, so it matches the displayed complex and normalization in the existing Lean statement, including the +a differential. The conclusion explicitly includes both the K-flat resolution and Q[0] K-flatness. There is no unproved comparison hidden in the assembly.

In Step 3 I opened `lem-weil-pbc-ringed-projection-mate-exact` and copied its exact sentence “Derived tensor is computed by replacing one factor by a K-flat resolution.” This is a theorem clause, not an inference from its name or a definition. The identity of the same small ringed site supplies its ambient morphism, both factors are R-module complexes, and the resolution is the one just constructed. The clause permits unbounded M. The off-unit citation is retained as a generic tool in `split_report.tool_uses`; its projection-formula part is not used. All four citations have literal sentence/formula excerpts in `citations.json`.

I rechecked delivery-errors B1-B10: the new files have statements only and introduce all objects; finite free means explicitly isomorphic to finite sums of the regular sheaf; flatness, module sheaves, constants, complexes, quasi-isomorphisms and K-flatness cite their real definition nodes. TeX uses single backslashes in the rendered strings. Tags and labels were verified in `literature/stacks-project/tags/tags`. The leaf candidates were read at their actual Mathlib lines, and neither whole statement is a leaf. The live sorry theorem cannot be attached. The new nodes have no bogus lean attachment or source-only proof claim.

For C1-C8, the parent uses exactly the statements quoted in citations.json and its proof_deps is the union of uses. New-node arguments are deliberately future work, not undeclared facts used inline. There are no parent back-edges from either new node, and both inherit the unit and correct blueprint ancestry. The one off-unit result used in the parent is the existing generic derived-tensor computation.

For D1-D5, neither new node restates the whole item: arbitrary flat module regularity and arbitrary finite-free cokernel resolution are separate reusable tasks, with the latter requiring injectivity as input. The complete previous argument is retained below, rather than compressed into “standard” or “the same calculation.” The item now assembles the two results in three distinct steps; all are below 2000 characters and their total is below 3000.

For E1-E7, I checked the constant and algebra coefficient categories separately, the R-linearity after the first application, quotient sheaf versus sectionwise quotient, degree -1 versus degree 0, the +u sign, regular-module flatness over R versus the original flatness over A_C, and the unbounded tensor factor. Small cases: the point site with A=Z and R=Z; a a unit (the cokernel is zero and the two-term complex is acyclic); R=0 and a nonzero (zero modules, valid); the empty site; m=0 or n=0 in the new cokernel node (if n=0, monicity forces P=0); a general commutative ring with a unit regular scalar; and A=Z, M=(Z/2)_C, a=2, which fails the flatness hypothesis rather than contradicting the result. On a point site a non-injective u has H^{-1}=ker(u) nonzero, showing why the monomorphism hypothesis in the second node cannot be dropped. No additional geometric, Noetherian, enough-points, or finite-coefficient hypothesis slipped into a new statement. There is no source dispute and no SGA source.

## Arguments transferred to the statement-only nodes

These are plans in the report, not proof fields in the new nodes. The exact old steps follow afterwards so that nothing is lost.

For `lem-sfb-flat-constant-module-scalar-mono`, start with the assumed injective A-module map a:A→A. Exact constant-module presheaf sheafification (the statement of `lem-weil-pbc-site-r-module-presheaf-sheafification-exact`) makes a:A_C→A_C monic. The underlying constant ring sheaf and the constant regular module are the associated objects by `def-weil-pbc-constant-sheaf`. Tensor with flat M; exactness is exactly the functor in `def-pc-flat-sheaf-modules`. The tensor-unit isomorphism sends b⊗m to bm and has inverse m↦1⊗m; these sectionwise maps are restriction-compatible and sheafify by `def-pur-sheaf-tensor-product`. Under it the tensor of a is m↦am. Thus it is monic. Finally, sectionwise kernels from `def-weil-sheaf-of-modules-category` give the advertised injection on each U, without passing to points. Compared with the old argument, only the initial domain calculation is replaced by the explicit regularity hypothesis, and the argument works for a module M without an algebra structure.

For `lem-sfb-finite-free-mono-cokernel-kflat`, form the actual two-term complex C_u and the sheaf cokernel q. The components of epsilon satisfy the cochain equation because qu=0. Compute H^{-1}=ker(u)=0, H^0=coker(u)=T and H^i=0 elsewhere. Its cohomology map is the identity cokernel comparison in degree zero and an isomorphism between zero sheaves in other degrees, so epsilon is a quasi-isomorphism by `def-pc-quasi-iso-modules`, with cohomology as in `def-pc-acyclic-complex-modules`. The normalized map from the cone has inr followed by epsilon equal to q[0], and its differential in degrees -1,0 is +u. For any module sheaf N, tensor with R^{⊕k} is N^{⊕k}: locally the inverse maps are (x_i)↦Σ_i x_i⊗e_i and x⊗(r_i)↦(r_i x); the tensor relations show they are inverse, and they commute with all restrictions, hence sheafify. Finite direct sums are exact (kernels and cokernels componentwise in an abelian category), so P,Q are flat. The k=0 case is the zero functor, also exact. This includes the old rank-one maps n⊗r↦rn and n↦n⊗1 and proves flatness of every zero term as well. All three complexes C_u,P[0],Q[0] vanish in degrees >0; apply the exact statement of `lem-pc-bounded-above-flat-kflat-site` with b=0 to each. Their terms are now known flat, so they are K-flat, and epsilon is the asserted K-flat resolution by `def-pc-kflat-complex`. The existing bounded-flat node's source says 06YS, but its statement is the criterion and the correct read source is 06YQ; no other node was edited to repair that pre-existing citation typo.

## Old proof, retained verbatim

### Old Step 1

Fix $a\ne0$. Since $A$ is an integral domain, $ax=ay$ implies $a(x-y)=0$ and hence $x=y$. Multiplication by $a$ is therefore a monomorphism of constant $A$-module presheaves. By [lem-weil-pbc-site-r-module-presheaf-sheafification-exact], evaluation computes presheaf kernels and module sheafification is exact. Sheafify this monomorphism over the constant ring presheaf $A$: by [def-weil-pbc-constant-sheaf] its source and target are $A_{\mathcal C}$, and its map is multiplication by the constant scalar $a$. Thus $a:A_{\mathcal C}\to A_{\mathcal C}$ is a monomorphism. This uses exact sheafification, without any assumption that the site has enough points.

Uses: lem-weil-pbc-site-r-module-presheaf-sheafification-exact, def-weil-pbc-constant-sheaf.

### Old Step 2

By [def-pc-flat-sheaf-modules], the given flatness of $R$ means precisely that $-\otimes_{A_{\mathcal C}}R$ is exact, so it preserves the kernel sequence $0\to A_{\mathcal C}\xrightarrow{a}A_{\mathcal C}$ from Step 1. The sheaf tensor product of [def-pur-sheaf-tensor-product] identifies $A_{\mathcal C}\otimes_{A_{\mathcal C}}R$ with $R$: sectionwise the map is $b\otimes r\mapsto br$, with inverse $r\mapsto1\otimes r$, and these maps respect restrictions and hence sheafify. Under this identification $a\otimes1$ sends $r$ to $ar$. Thus $a:R\to R$ is monic. Kernels of module sheaves are sectionwise by [def-weil-sheaf-of-modules-category], so this is injectivity on sections as well.

Uses: def-pc-flat-sheaf-modules, def-pur-sheaf-tensor-product, def-weil-sheaf-of-modules-category.

### Old Step 3

Let $C^{-1}=R$, $C^0=R$, $d^{-1}=a$, and all other terms and differentials be zero. Let $q:R\to R/aR$ be the sheaf cokernel of $a$. Cokernels are sheafifications of sectionwise cokernels by [def-weil-sheaf-of-modules-category], so this is the quotient sheaf meant by $R/aR$. The augmentation $\epsilon:C\to(R/aR)[0]$ has $\epsilon^0=q$ and zero components elsewhere; $qa=0$ gives its cochain-map equation. By [def-pc-acyclic-complex-modules], $H^{-1}(C)=\ker(a)=0$ by Step 2, $H^0(C)=\operatorname{coker}(a)=R/aR$, and $H^i(C)=0$ for $i\ne-1,0$. The map $H^0(\epsilon)$ is precisely the cokernel identification, and all other cohomology maps are isomorphisms between zero sheaves. Hence $\epsilon$ is a quasi-isomorphism by [def-pc-quasi-iso-modules].

Uses: def-weil-sheaf-of-modules-category, def-pc-acyclic-complex-modules, def-pc-quasi-iso-modules.

### Old Step 4

Over the coefficient sheaf $R$ itself, both nonzero terms of $C$ are flat, independently of the original flatness over $A_{\mathcal C}$. Indeed, [def-pur-sheaf-tensor-product] gives $M\otimes_RR\cong M$ by $m\otimes r\mapsto rm$ with inverse $m\mapsto m\otimes1$, sectionwise and then after sheafification; consequently tensoring with $R$ is exact. Tensoring with the zero sheaf is the zero functor, also exact. By [def-pc-flat-sheaf-modules], this proves flatness of every term of $C$ and of $R[0]$ as $R$-module sheaves.

Uses: def-pur-sheaf-tensor-product, def-pc-flat-sheaf-modules.

### Old Step 5

The complexes $C$ and $R[0]$ both vanish in degrees strictly greater than zero, and every term is flat over $R$ by Step 4. Apply [lem-pc-bounded-above-flat-kflat-site] to the ringed site $(\mathcal C,R)$, with upper bound $b=0$, separately to each complex. Both are K-flat over $R$. Combining the K-flatness of $C$ with the actual augmentation quasi-isomorphism from Step 3 gives a K-flat resolution of $(R/aR)[0]$, exactly as defined by [def-pc-kflat-complex].

Uses: lem-pc-bounded-above-flat-kflat-site, def-pc-kflat-complex.

### Old Step 6

The statement [lem-weil-pbc-ringed-projection-mate-exact] says that derived tensor is computed by replacing one factor by a K-flat resolution (take the identity morphism of the small ringed site $(\mathcal C,R)$ for its ambient ringed-topos data). Use the resolution $\epsilon$ of Step 5 for the quotient factor. Thus for any $R$-module complex $M^\bullet$, $M^\bullet\otimes_R^{\mathbf L}(R/aR)$ is represented by $\operatorname{Tot}(M^\bullet\otimes_R C)$. This is precisely computation by the displayed two-term complex, and proves the final assertion.

Uses: lem-weil-pbc-ringed-projection-mate-exact.

## Not duplicates

lem-sfb-flat-constant-module-scalar-mono vs lem-sf-intrinsic-realization-origin-comparison: finite-coefficient intrinsic realization versus original sheaves on a scheme; no scalar regularity theorem for an arbitrary small site.

lem-sfb-flat-constant-module-scalar-mono vs def-pc-flat-sheaf-modules: defines exact tensor flatness; it does not state regular-scalar preservation after constant sheafification.

lem-sfb-flat-constant-module-scalar-mono vs lem-sfb-open-closed-flatness: tests flatness by an open/closed decomposition of schemes with finite coefficients; no arbitrary-ring regular-scalar conclusion.

lem-sfb-flat-constant-module-scalar-mono vs lem-sfb-constant-to-continuous-scalar-flat: proves one specific constant-to-continuous map is flat on profinite sets over a topological PID; our result takes arbitrary flat module sheaves and proves scalar monicity.

lem-sfb-flat-constant-module-scalar-mono vs lem-c2-internal-section-module-flatness: compares internal and section-module flatness predicates; no regular-scalar action is asserted.

lem-sfb-flat-constant-module-scalar-mono vs lem-weil-pbc-flat-restriction-exact-left-adjoint: constructs an exact scalar-extension left adjoint for a supplied flat ring-sheaf map; our statement concerns scalar monicity on a supplied flat module over a constant ring.

lem-sfb-flat-constant-module-scalar-mono vs lem-weil-pbc-module-presheaf-sheafification-exact: exact sheafification on a scheme ringed space; no conclusion about regular constant scalars on arbitrary flat module sheaves.

lem-sfb-flat-constant-module-scalar-mono vs lem-weil-pbc-sheaf-tensor-closed: constructs exact strong-monoidal sheafification and closed tensor; our result applies exactness to a specified regular scalar and flat module and proves sectionwise injectivity.

lem-sfb-flat-constant-module-scalar-mono vs lem-exc-constant-field-module-flat: flatness for all module sheaves over a constant field; our ring may have zero divisors and our conclusion is regular-scalar injectivity.

lem-sfb-flat-constant-module-scalar-mono vs lem-sf-proetale-residue-module-tensor-homology: fixed-degree vanishing transfer from a residue coefficient to annihilated modules; no scalar monicity conclusion.

lem-sfb-flat-constant-module-scalar-mono vs lem-pur-etale-constant-module-flat: equivalence of flatness predicates under the etale constant module equivalence; no regular-scalar injectivity conclusion.

lem-sfb-flat-constant-module-scalar-mono vs lem-pur-constant-two-term-resolution: only the Z_l/ell^N constant quotient and its tensor augmentation; our scalar theorem is for any commutative ring with an injective scalar and any flat module sheaf, with no quotient conclusion.

lem-sfb-flat-constant-module-scalar-mono vs lem-weil-pbc-site-r-module-presheaf-sheafification-exact: general exactness of constant-ring module sheafification; this is an ingredient, not its consequence for regular scalars on arbitrary flat module sheaves.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sf-integral-line-tensor-comparison-representative: completed integral coefficients, line bundles and finite-reduction comparison; our statement constructs the cokernel resolution for any finite-free monomorphism on any small ringed site.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-trf-finite-filtered-flat-resolution: existence of split-flat filtered resolutions and equivalences of filtered localizations; no specified two-term cokernel augmentation is asserted.

lem-sfb-finite-free-mono-cokernel-kflat vs def-trf-split-flat-filtered-sheaf-models: defines finite filtered split-flat models and their tensor filtration; it does not prove a cokernel augmentation is a quasi-isomorphism.

lem-sfb-finite-free-mono-cokernel-kflat vs def-pc-acyclic-complex-modules: defines cohomology and acyclicity; it does not construct the normalized augmentation or prove finite-free K-flatness.

lem-sfb-finite-free-mono-cokernel-kflat vs def-pc-quasi-iso-modules: defines quasi-isomorphisms; our statement proves one for a specified cokernel augmentation and gives K-flatness.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-pc-bounded-above-flat-tensor-acyclic-degree: a fixed-degree acyclicity result under another node's bounded-flat hypotheses; it does not identify the augmented cokernel resolution.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sfb-constant-field-tor-bounds: Tor-amplitude bounds over constant fields on scheme pro-etale sites; our statement is a finite-free resolution over arbitrary commutative ring sheaves.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sfb-ringed-site-point-kflat-resolution: existence of a K-flat resolution with K-flat stalk at a supplied point; our resolution is a specified two-term complex without a point assumption.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sfb-flat-scalar-cyclic-resolution: the parent proves scalar monicity from a domain and flat extension and then derived-tensor computation; this new node assumes monicity of an arbitrary finite-free map and treats only its normalized resolution.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-weil-pbc-site-tensor-local-model-comparison: identifies cohomology under supplied local finite-free scalar models; no construction of the normalized cokernel augmentation.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-weil-pbc-independent-bounded-flat-kflat: gives K-flatness for any supplied bounded-above flat complex; does not prove the specified cokernel augmentation is a quasi-isomorphism or finite-free terms are flat.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-weil-pbc-split-perfect-tensor-kinjective: tensor of a K-injective and a split-perfect complex is K-injective; our assertion is about a cokernel augmentation and K-flatness.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-weil-pbc-completed-adic-koszul-kflat: K-flatness of a specified completed adic Koszul complex; no arbitrary finite-free monomorphism or normalized cokernel quasi-isomorphism.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-pur-etale-single-functor-monoidal-compatibility: coherence of etale flat-single tensor pairings and inverse-image comparison; our statement is the construction of a two-term cokernel resolution.

lem-sfb-finite-free-mono-cokernel-kflat vs def-weil-derived-category-cohomology-functor: defines ordinary-module derived cohomology; it does not prove sheaf cokernel resolutions or K-flatness.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-pur-constant-two-term-resolution: only a power-of-ell map over the constant Z_l sheaf, with an extra tensor-augmentation clause; this new node allows every injective rectangular matrix over any ring sheaf and no constant coefficient assumption.

lem-sfb-flat-constant-module-scalar-mono vs lem-trf-flat-module-torsionfree-domain: ordinary modules over an ordinary domain, not flat module sheaves over a constant arbitrary ring; the sheafification and sectionwise kernel argument remains.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sfb-finite-constant-model-two-term-free-resolution: existence of a scalar-derived resolution over a DVR or field on a scheme's pro-etale site, not the specified augmentation and K-flatness for an arbitrary supplied finite-free monomorphism on an arbitrary ringed site.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-sfb-scalar-model-finite-flat-resolution: constructs some finite flat resolution of a finitely presented scalar model over a DVR; it does not apply to an arbitrary supplied rectangular finite-free map over a general ring sheaf, and that existence theorem may use the present parent.

lem-sfb-flat-constant-module-scalar-mono vs lem-pod-completed-integral-scalar-regular: uniformizer powers on a specified completed integral sheaf; our result is arbitrary regular scalars on arbitrary flat constant-coefficient module sheaves.

lem-sfb-finite-free-mono-cokernel-kflat vs lem-pc-bounded-above-flat-kflat-site: the latter is the general K-flatness criterion used in the new node's eventual proof; it does not itself state finite-free flatness or the normalized cokernel quasi-isomorphism.
