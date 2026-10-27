# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-separable-closed-point-formal-presentation.json: repaired parent split; statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-coefficient-field-generator-presentation.json: statement-only lemma, status unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-separable-evaluation-local-base-change.json: statement-only lemma, status unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every node cited by each parent step.

## Attachments

None. I searched the project WeilConjectures source for the exact blueprint tag and the closed-point, coefficient-field and power-series concepts. No exact finished project declaration was found. The parent declaration in Sheaf/RingTheory/SeparableClosedPointFormalPresentation.lean ends in sorry (line 180), so it is not an attachment. No Lean was changed or compiled.

## WANTED

None; the required Stacks sources are present locally.

## What was wrong and what changed

This repairs the human's re-split return, not a statement correction. The read-only current node has the returned seven-step proof with lengths 1188, 1942, 241, 448, 1936, 347, 497. The sandbox initially contained only brief markers, no node files, report or search log, so I copied the current returned node without discarding any sandbox work. No repository git command was run.

The new coefficient-field-generator lemma takes the complete Noetherian local ring, its fixed coefficient section and an arbitrary generating tuple as input; its proof obligation is the universal-property and complete-source surjectivity argument previously inline in step 2. The new separable-evaluation lemma takes the finite-type algebra and the embedding into K; its proof obligation is the evaluation-prime, localized flatness, Noetherianity and reduced zero-dimensional fibre calculation previously inline in step 5. These are two comparable independent arguments (1942 and 1936 original characters), not a renamed copy of the whole parent. Neither asserts the completed differential comparison or completion base-change theorem. Both nodes have self-contained statements, sources, three kinds of logged Mathlib search, empty proofs and empty proof_deps. Their full proof obligations are preserved verbatim below rather than being installed as proofs on unsplit nodes.

The remaining proof keeps its separate elementary dummy-variable padding. It uses the existing completed-Jacobian lemma twice, and the existing completion base-change lemma once. Step 1 is an assembly of the existing Noetherianity, localization and completion statements; no new lemma is manufactured for that assembly. No old argument has been dropped. The parent statement, definitions, source, imported fields and Lean records are unchanged. Blueprint searches for coefficient field, coefficient-field, power series, complete local, change fields, separable closed, 0C52, 0C50 and 0C4Y found no imported node stating either new lemma; the ancestor command confirms lem-trf-local-term-locality and the existing via chain, which is extended by the parent on each new node.

## Mathlib searches

Every query in the new nodes is copied from this sandbox's actual msearch.py log. I read the returned hits and made a second semantic search for each argument. The presentation searches found completeness of the power-series ring, the empty-variable constants surjection, Henselian lifting, polynomial presentations and Weierstrass division. Reading MvPowerSeries/Basic.lean:368 and PowerSeries/WeierstrassPreparation.lean:835 confirms that these do not present an arbitrary complete local algebra through a prescribed coefficient field. The field-change searches found Algebra.isUnramifiedAt_iff_map_eq and FormallyUnramified.iff_map_maximalIdeal_eq. I read Unramified/LocalRing.lean:117 and :134: those are criteria using unramifiedness and separability of residue extensions, not the evaluation-fibre calculation or its explicit residue map. FiniteType.baseChange supplies only one ingredient. Hence neither new lemma is a one-line Mathlib specialization. The parent's existing searches and their original results are retained unchanged.

## Review by Q22

I read the item and both new statements against varieties.tex, Tag 0C52 (lemma-complete-local-ring-structure-as-algebra), Tags 0C4Y (lemma-change-fields-flat), 0C50 (lemma-change-fields-algebraic-unramified) and 0C54 (lemma-base-change-complete-local-ring); I also read more-algebra.tex, Tag 0C34 (lemma-lift-residue-field), and curves.tex, Tag 0C4D (lemma-nodal), especially the polynomial Jacobian passage. The two extracted statements isolate the arguments of 0C52 and 0C4Y/0C50 with the same hypotheses as the old argument. For the field-change lemma I explicitly retain finite separability of F/k, the k-linearity of the embedding and the evaluation prime. Finiteness gives dimension zero of the fibre directly; I do not import 0C50's dimension-equality hypothesis without proving it. For the presentation lemma I require actual adic completeness including separatedness and a section inducing the identity on the residue field; an arbitrary Cohen coefficient ring would not meet that requirement.

Step 1: I opened all five cited statements. finite-type-algebra-noetherian applies over the Noetherian field k; flat-local-ring-maps applied to the identity gives precisely the localization and its Noetherian local property. The quotient S/p is already a field, so its localization is unchanged. adic-completion-noetherian gives the Noetherian completion, local-completion-local-ring gives the maximal ideal and canonical residue-field identification, and adic-completion-mod-ideal gives completeness because m is finitely generated. Nothing is inferred merely from the definition of completion.

Step 2: the coefficient-section statement supplies a k-algebra splitting because the complete local algebra has separable residue F/k. The new generator-presentation statement supplies the actual F-algebra map through that section, not through an unrelated Cohen ring, and also supplies continuity, surjectivity and finite kernel generators in (t). Images of a generating tuple for m generate its extended ideal in the completion. These are exactly the new lemma's inputs.

Step 3: dummy variables mapped to zero, with those variables added to the relation tuple, give the same quotient; this is elementary and is kept in the parent. In particular the field and single-generator cases are not excluded by the n>=2 convention.

Step 4: I opened completed-jacobian-differentials; its statement is for every fixed section and continuous presentation, and its canonical cokernel map sends e_i to the continuous differential of the variable image. This supplies the every-presentation clause, rather than a calculation for only the presentation just constructed.

Step 5: I read the entire new local-base-change statement. Its outputs include finite type over K for the later Jacobian application, Noetherian local B, faithful flatness of the explicitly induced map, the extended maximal-ideal equality and the evaluation residue isomorphism. Its statement says everything used here; no assertion is taken from its future proof.

Step 6: I opened field-extension-completion-presentation. It takes the very same S,p,F/k and k-embedding, and any chosen F-algebra presentation. Its conclusion is the complete local K-algebra isomorphism preserving all variable images; its statement requires no unproved dimension equality. This is exactly what the parent takes from it.

Step 7: the completed-Jacobian statement applies with base K, algebra S tensor_k K (finite type by step 5), local ring B and residue extension K/K. Step 6 supplies the structural coefficient section and presentation. Coefficientwise partial differentiation commutes with the embedding, since it multiplies each coefficient by the same natural exponent and lowers the same monomial exponent. This elementary observation explains precisely why the Jacobian matrix is the transported matrix.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 with the statements open. No unsplit node contains proof steps or a proof sketch in its statement. All notions are introduced and cited or defined inline; all text uses ordinary single-escaped TeX. No source or node is used for a theorem its statement does not contain. The split uses no SGA route. The duplicate comparisons below distinguish the shared tags and closely related Cohen and regular-coordinate statements. Both nodes are strictly smaller independent sourced arguments, as specifically required by this re-split return; the parent still assembles section choice, padding, the two differential comparisons and completion base change. No new non-elementary parent step exceeds 2000 characters.

Small cases: for R=F the zero-generator case has Phi=id_F and zero kernel. For R=F[[u,v]]/(uv), y=(u,v) gives kernel (uv), so regularity is not tacitly assumed. Repeated or zero generators are allowed, e.g. y=(u,0) in F[[u]] has kernel (T_2). When S=k and F=k, the second lemma gives B=K and zero maximal ideal. When S=R[x], p=(x^2+1), F=C and K=C, the chosen evaluation picks one factor of C tensor_R C, so localizing at the chosen prime is essential. Without separability, k=F_p(a), F=k[x]/(x^p-a), K=F gives F tensor_k K=K[epsilon]/(epsilon^p); the maximal-ideal conclusion fails. This checks that the hypotheses doing the reduced-fibre work have not been weakened.

## Original arguments retained and work distribution

The following is the original proof, verbatim, with ownership of each argument made explicit. It is documentation for future stage-1 workers; the new nodes remain statement-only.

### Original step 1: Parent step 1, using the existing five structural lemmas.

The field $k$ is Noetherian, so the finitely generated $k$-algebra $S$ is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Applying [lem-weil-pbc-flat-local-ring-maps] to the (flat) identity map $S\to S$ and the prime $\mathfrak p$ shows that $A=S_{\mathfrak p}$ is a Noetherian local ring, with maximal ideal $\mathfrak m=\mathfrak pA$ and residue field $A/\mathfrak m=S/\mathfrak p=F$ ($\mathfrak p$ being maximal; localization is exact). Since $\mathfrak m$ is an ideal of the Noetherian ring $A$, its completion $\widehat A$ is Noetherian by [lem-weil-pbc-adic-completion-noetherian]. The completion-local-ring lemma [lem-weil-pbc-local-completion-local-ring] applied to $(A,\mathfrak m)$ says that $\widehat A$ is local, its maximal ideal is $\mathfrak m\widehat A$, and $A/\mathfrak m=F\to\widehat A/\mathfrak m\widehat A$ is an isomorphism; and [lem-weil-pbc-adic-completion-mod-ideal] (with $I=\mathfrak m$, finitely generated) says that $\widehat A$ is $\mathfrak m\widehat A$-adically complete. Thus the first local and residue assertions of the item hold, and $\widehat A$ is a complete local $k$-algebra (through $k\to S\to A\to\widehat A$) with residue field $F$.

### Original step 2: lem-trf-coefficient-field-generator-presentation (new statement-only work item).

By step 1, $\widehat A$ is a complete local $k$-algebra whose residue field $F$ is finite separable over $k$, so the residue-field section lemma [lem-trf-separable-residue-coefficient-section] supplies a $k$-algebra map $\sigma:F\to\widehat A$ with $F\xrightarrow{\sigma}\widehat A\to\widehat A/\mathfrak m\widehat A=F$ the identity. Choose generators $y_1,\ldots,y_n$ of the maximal ideal $\mathfrak m\widehat A$ (images of generators of the finitely generated ideal $\mathfrak m$). By the universal property of power series over a complete ring [lem-weil-pbc-power-series-universal-property-complete] (with $\Lambda=F$, $T=\widehat A$, $\mathfrak a=\mathfrak m\widehat A$, $\alpha=\sigma$, $t_i=y_i$) there is a ring map $\Phi:F[[t_1,\ldots,t_n]]\to\widehat A$ equal to $\sigma$ on constants and with $\Phi(t_i)=y_i$; it is a map of $F$-algebras for the $F$-structure through $\sigma$, and it is continuous since $\Phi((t_1,\ldots,t_n)^r)\subseteq(\mathfrak m\widehat A)^r$. By [lem-weil-pbc-power-series-field-cohen-regular-complete] (case $\Lambda=F$), $R_0=F[[t_1,\ldots,t_n]]$ is a Noetherian local ring, complete for $I=(t_1,\ldots,t_n)$. Then $I\widehat A=(y_1,\ldots,y_n)=\mathfrak m\widehat A$, $\widehat A$ is $\mathfrak m\widehat A$-adically complete, hence Hausdorff (step 1), and $R_0\to\widehat A/\mathfrak m\widehat A=F$ is surjective because it restricts to $\mathrm{id}_F$ on constants; so $\Phi$ is surjective by [lem-weil-pbc-complete-source-surjective-mod-ideal]. Its kernel is finitely generated, say by $f_1,\ldots,f_s$, because $R_0$ is Noetherian. Finally the composite $R_0\xrightarrow{\Phi}\widehat A\to F$ sends a constant $c$ to $c$ and each $t_i$ to $\bar y_i=0$, so it is the constant-term map, whose kernel is $(t_1,\ldots,t_n)$; hence $\ker\Phi\subseteq(t_1,\ldots,t_n)$. (This is the argument of Tag 0C52; the Cohen structure theorem with its unrelated coefficient ring is not needed once $\sigma$ is fixed.)

### Original step 3: Parent step 3, elementary dummy-variable padding.

If the presentation in step 2 has $n<2$, adjoin $2-n$ dummy variables and add them to the kernel generators. The quotient, section, continuity, and containment of the kernel in the variable ideal are unchanged, so we may and do take $n\ge2$.

### Original step 4: Parent step 4, using the existing completed-Jacobian lemma.

For an arbitrary presentation chosen in the statement, the completed-Jacobian lemma [lem-trf-completed-jacobian-differentials] applies with the given finite-separable extension $F/k$, section $\sigma$, and generators $f_j$. Its explicitly defined map sends $e_i$ to the continuous differential $\widehat d(t_i)$ and identifies the Jacobian cokernel with $\Omega_{A/k}\otimes_A\widehat A$; hence the differential clause holds for every presentation.

### Original step 5: lem-trf-separable-evaluation-local-base-change (new statement-only work item).

Let $K/k$ be an extension field containing the specified $k$-embedded copy $\iota:F\hookrightarrow K$, and define $\mathfrak q$ and $B$ as in the statement. The evaluation map $S\otimes_kK\to K$ is surjective ($1\otimes\lambda\mapsto\lambda$), so $\mathfrak q$ is a maximal ideal with residue field $K$, and $\mathfrak q\cap S=\ker(S\to F\xrightarrow{\iota}K)=\mathfrak p$ since $\iota$ is injective. The field-extension base-change lemma [lem-weil-pbc-field-extension-base-change-faithfully-flat] makes $S\to S\otimes_kK$ faithfully flat. A presentation $S\cong k[x_1,\ldots,x_m]/\mathfrak a$ gives $S\otimes_kK\cong K[x_1,\ldots,x_m]/\mathfrak aK[x]$, so $S\otimes_kK$ is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Localizing at $\mathfrak q$ over $\mathfrak p$, [lem-weil-pbc-flat-local-ring-maps] gives a flat local map $A\to B$ of Noetherian local rings, and the local-flat faithful-flat lemma [lem-pc-local-flat-faithful-flat-reflects-surjective] upgrades it to faithfully flat. For the fibre: by exactness of $-\otimes_kK$ and of localization, $B/\mathfrak mB=\big((S/\mathfrak p)\otimes_kK\big)_{\bar{\mathfrak q}}=(F\otimes_kK)_{\bar{\mathfrak q}}$, where $\bar{\mathfrak q}$ is the kernel of $F\otimes_kK\to K$, $a\otimes\lambda\mapsto\iota(a)\lambda$. Since $F/k$ is finite separable, $F\otimes_kK$ is reduced by [lem-weil-pbc-finite-separable-tensor-field-reduced] (with $L=k$, $K'=F$, $E=K$). It is a finite-dimensional $K$-algebra, so every prime of it is maximal (a domain finite over a field is a field), hence $(F\otimes_kK)_{\bar{\mathfrak q}}$ has a unique prime ideal, which is therefore its nilradical, which is $0$ by reducedness (localization of a reduced ring is reduced). So $B/\mathfrak mB$ is a field, hence equal to the residue field $B/\mathfrak qB=K$ of $\mathfrak q$, i.e. $\mathfrak mB=\mathfrak qB=\mathfrak m_B$. Thus all local-flatness, maximal-ideal, and residue-field clauses hold.

### Original step 6: Parent step 6, using the existing completion base-change lemma.

Apply the completion-presentation base-change lemma [lem-trf-field-extension-completion-presentation] to the chosen presentation, using the $k$-embedding $F\hookrightarrow K$. The inverse-limit computation identifies $\widehat B$ with $K[[t_1,\ldots,t_n]]/(f_1,\ldots,f_s)$ as complete local $K$-algebras and preserves the images of all variables.

### Original step 7: Parent step 7, using the existing completed-Jacobian lemma over K.

Finally apply [lem-trf-completed-jacobian-differentials] over the base field $K$ to the finite-type $K$-algebra $S\otimes_kK$, the maximal ideal $\mathfrak q$, and the local ring $B$. Its residue field is $K$, the identity extension $K/K$ is finite separable, and the canonical section $K\to\widehat B$ is the structural map. The transported presentation from step 6 therefore gives the same Jacobian cokernel for $\Omega_{B/K}\otimes_B\widehat B$, with the variable images identified as asserted.

The first new lemma's additional inverse-image identity is exactly the old constant-term argument: rho pi Phi is constantCoeff, so Phi^{-1}(n)=I. The second new lemma's displayed evaluation formula is the localization of epsilon, hence records the map used by the old residue-field identification. Its finite-dimensionality and reducedness conclusions expose the precise intermediate claims of the old fibre argument for the future worker. They are conclusions, not an embedded proof sketch.

## Not duplicates

lem-trf-coefficient-field-generator-presentation vs def-trf-formal-local-presentation: the existing node defines presentation data and proves no existence or evaluation-localization theorem.

lem-trf-coefficient-field-generator-presentation vs lem-per-prime-field-complete-coordinate-model: the existing node concerns Cohen coordinate completion of an equicharacteristic regular local ring, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-per-principal-jacobian-algebraization: the existing node concerns Principal-ideal algebraization of a torsion conormal presentation, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-sfb-separable-node-quadratic-completion: the existing node concerns Quadratic completion over the separable residue field of a geometric node, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-completed-conormal-determinant-comparison: the existing node concerns Completed algebraic and continuous formal conormal determinants with generic normalization, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-completed-jacobian-differentials: the existing statement identifies completed differential modules for a supplied presentation; neither new lemma makes a differential assertion.

lem-trf-coefficient-field-generator-presentation vs lem-trf-completion-local-complete-intersection: the existing node concerns Complete-intersection neighbourhoods detected by the completed local ring, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-flat-projective-reduction-completion-splitting: the existing node concerns Flat quotient with projective reduction gives split sequence of completions, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-nodal-point-local-criterion: the existing node concerns Pointwise criterion for a nodal singularity by the first Fitting ideal, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-rational-node-quadratic-completion: the existing node concerns Quadratic completed equation at a rational geometric node, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-trf-regular-complete-coefficient-coordinates: the existing statement requires regularity and gives an isomorphism; the new lemma allows singular complete local rings and asserts a surjection with its kernel.

lem-trf-coefficient-field-generator-presentation vs lem-trf-relative-cohen-flat-presentation: the existing theorem assumes a flat local map of Q-algebras with regular closed fibre and chooses compatible coefficient sections; the new lemma works in arbitrary characteristic with a supplied section and any prescribed generating tuple, without a flat map or regularity hypothesis.

lem-trf-coefficient-field-generator-presentation vs lem-trf-separable-closed-point-formal-presentation: the parent combines section existence, completed differentials, completion field change and local structure; the new node isolates only the presentation with a supplied section and any generator tuple.

lem-trf-coefficient-field-generator-presentation vs lem-trf-separable-residue-coefficient-section: the existing statement produces a coefficient section, whereas the new presentation starts with one and constructs the power-series surjection.

lem-trf-coefficient-field-generator-presentation vs lem-trf-stable-modification-stability-field-descent: the existing node concerns Semistability and geometric stability are invariant under field extension, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-cohen-structure-power-series-surjection: the existing Cohen construction permits an unrelated coefficient ring; the new presentation fixes a supplied residue-field section and every prescribed maximal-ideal generating tuple.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-complete-source-surjective-mod-ideal: the existing lemma is a criterion for a given ring map; the new lemma constructs the fixed-coefficient power-series map and proves its kernel assertions.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-finite-after-completion: the existing node concerns Completion of a local ring with finite-dimensional special fibre is finite over the completion of the base, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-finite-module-complete-over-complete-noetherian: the existing node concerns A finite module over a Noetherian ring complete along an ideal is complete, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-finite-over-complete-ring: the existing node concerns A Hausdorff module over a complete ring that is finite modulo the ideal is finite, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-g-ring-quotient: the existing node concerns A quotient of a G-ring is a G-ring, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-local-completion-quotient: the existing node concerns Completion of a quotient of a Noetherian local ring, whereas the new lemma constructs a power-series surjection through a fixed coefficient-field section for any generating tuple, with its kernel in the variable ideal.

lem-trf-coefficient-field-generator-presentation vs lem-weil-pbc-power-series-onto-completion: the existing map has coefficients in the original ring R; the new map has coefficients in the prescribed residue field F and a fixed section.

lem-trf-separable-evaluation-local-base-change vs lem-sc-etale-base-change-geometric: the existing node concerns Pointwise etaleness is preserved and reflected by field extension, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-sc-etale-faithfully-flat-local: the existing node concerns Etaleness at a point descends along a faithfully flat field extension, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-sc-etale-local-ring-faithfully-flat-descent: the existing node concerns Etaleness at a prime descends for a faithfully flat field base change, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-sc-etale-local-ring-stalk-faithfully-flat: the existing statement supplies only faithful flatness; the new field-change lemma also computes the evaluation fibre, its explicit residue map and maximal ideal.

lem-trf-separable-evaluation-local-base-change vs lem-sc-hom-etale-locus-translation: the existing node concerns Etale locus of a group homomorphism is translation invariant, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-sc-lfp-field-extension-pointwise-descent: the existing node concerns Pointwise local finite presentation descends along a field extension, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-sfb-separable-node-quadratic-completion: the existing node concerns Quadratic completion over the separable residue field of a geometric node, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-trf-field-extension-completion-presentation: the existing statement compares completed presentations; it does not assert the uncompleted localized fibre, its residue formula, and faithful flatness, or construct the supplied-coefficient presentation.

lem-trf-separable-evaluation-local-base-change vs lem-trf-nodal-point-local-criterion: the existing node concerns Pointwise criterion for a nodal singularity by the first Fitting ideal, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-trf-rational-node-quadratic-completion: the existing node concerns Quadratic completed equation at a rational geometric node, whereas the new lemma computes the local fibre at the specified separable evaluation prime and its explicit residue map, with local faithful flatness.

lem-trf-separable-evaluation-local-base-change vs lem-trf-separable-closed-point-formal-presentation: the parent combines section existence, completed differentials, completion field change and local structure; the new node isolates only the uncompleted evaluation-localization calculation.

## What remains

The parent is split. The two extracted lemmas are deliberately unsplit so other workers can prove their independent arguments. The first required deliver.py --no-push exited successfully with OK (not pushed), commit d3402d2b0cd, preflight passed. The final report is checked again before pushing.
