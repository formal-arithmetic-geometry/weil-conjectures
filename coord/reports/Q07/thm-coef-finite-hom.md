# Q07 repair: thm-coef-finite-hom

## Files written

- dag/nodes/sec-six-functors/thm-coef-finite-hom.json: statement unchanged; five-step assembly, 1948 characters.
- dag/nodes/sec-six-functors/lem-coef-finite-hom-domain-calculus.json: statement, unsplit; no Mathlib match after logged searches.
- dag/nodes/sec-six-functors/lem-coef-etale-lisse-hom-reduction.json: statement, unsplit; no Mathlib match after logged searches.
- dag/nodes/sec-six-functors/lem-coef-locally-closed-hom-generator.json: statement, unsplit; no Mathlib match after logged searches.
- dag/nodes/sec-six-functors/lem-coef-evaluation-transpose-coherence.json: statement, unsplit; no Mathlib match after logged searches.
- dag/nodes/sec-six-functors/lem-coef-finite-hom-site-descent.json: statement, unsplit; no Mathlib match after logged searches.
- citations.json: a verbatim statement quote for every citation in each assembly step.
- report.md: review, extraction map and complete original arguments.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and finite Hom/coefficient notions. The project's corresponding theorem is WeilConjectures.finiteCoefficient_derivedHom_change in lean/Sheaf/Paper/FiniteCoefficientHomChange.lean:230; its proof is still sorry (line 274), so it is not an attachment. No Lean file was edited or compiled.

## WANTED

None for this repair. The master blueprint full proof and the main-20261015 restatement are available and were read. The original proof is agent-written, so this repair retains proof_origin.by=agent; it does not present the extracted statements as established external theorems. No SGA source was used.

## What was wrong and what changed

The returned proof was 14542 characters, blocking independent work. The sandbox initially contained only dispatcher marker files, no delivered node, report or search log. I copied the current read-only repository item, which has the exact 14 returned steps and unchanged statement, and preserved that argument below. The initial dry run exited with the expected missing report/Review diagnostic. This is a substantive re-split, not an unchanged re-push. The item statement, original metadata and existing dependency records are retained where not owned by the split.

## What remains

Five new unsplit statements require independent future workers. As instructed, they contain no proof steps or proof dependencies. Their complete inherited arguments, literature places and old cited statements are preserved below as starting material, not hidden inside their statements. No stage 2 or 3 work was attempted.

## Not duplicates

lem-coef-finite-hom-domain-calculus vs lem-coef-etale-tensor-model-comparison: that node gives the canonical binary scalar tensor normalization, not finite-Tor constructible domain preservation, pullback domains and the Hom endpoint calculation.

lem-coef-finite-hom-domain-calculus vs lem-sf-ringed-derived-closed-symmetric-monoidal: that node supplies ambient closed tensor calculus, not the finite-coefficient constructible flat models or scalar-domain checks.

lem-coef-etale-lisse-hom-reduction vs lem-coef-etale-locally-closed-shriek: that node supplies exceptional comparison and preservation, but not the explicit Tor bounds for Q and the lisse finite-free Hom comparison u.

lem-coef-etale-lisse-hom-reduction vs lem-sf-hom-finite-projective: that node gives projective dual tensor and biduality, not the etale quotient coefficient comparison with exceptional domains and bounds.

lem-coef-etale-lisse-hom-reduction vs lem-sf-ringed-finite-free-hom-base-change: that node assumes the TARGET ring is finite free over the source; here B=A/(varpi^m) is generally nonflat and the FIRST HOM INPUT is lisse finite projective.

lem-coef-etale-lisse-hom-reduction vs lem-sf-hom-comparison-finite-free: that node concerns a change of SITE at one coefficient, not a nonflat change of coefficient ring and exceptional Tor bounds.

lem-coef-locally-closed-hom-generator vs lem-coef-internal-adjunction-pairing-change: that node assumes N,Q are ctf and supplies an equality without assuming or concluding invertibility of u or c; the new generator lemma proves all those factors invertible under lisse input hypotheses.

lem-coef-locally-closed-hom-generator vs lem-sf-etale-generic-evaluation-coherence: that node is a geometric base-change identity, with closed-then-open factorization and no invertibility; this is a coefficient quotient and an invertibility theorem for open-then-closed generators.

lem-coef-evaluation-transpose-coherence vs lem-coef-monoidal-square-hom-transport: that node transports already given comparison identities through a square and explicitly takes the identities as inputs; this lemma establishes those identities for the evaluation transpose of one/composed strong monoidal functors.

lem-coef-evaluation-transpose-coherence vs lem-coef-closed-self-enrichment-base-change: that infinity-categorical adjunction theorem concerns R[LX,B] and enrichment on a family; here an ordinary strong monoidal F need not be an adjoint or preserve internal Hom.

lem-coef-finite-hom-site-descent vs lem-weil-finite-duality-site-comparison: that node gives beta at one coefficient, not the scalar/site square with its B action and successive-quotient coherence.

lem-coef-finite-hom-site-descent vs lem-coef-monoidal-square-hom-transport: that node is generic and explicitly assumes monoidal square data and beta invertibility, and asserts no sheaf-theoretic descent; the new node supplies those inputs on actual sites.

lem-coef-finite-hom-site-descent vs lem-sfb-etale-proetale-cube-flat-model: that node normalizes six geometric/scalar cube faces on a K-flat model, not constructible finite-Tor descent, beta isomorphisms and the resulting Hom square.

## Review by Q07

I read coord/delivery-errors.md B–E in full and checked the new JSON statements against the source and against the actual statements of the old cited nodes, rather than treating their names as evidence. I read the master thm-coef-finite-hom four-paragraph proof and the current main-20261015 restatement; the current restatement has no proof. The fixed chapter and the biduality unit retain their localization/stratification route. I changed no target statement and no route.

Step 1 uses the domain-calculus statement: it explicitly supplies Noetherianity, same-interval reduction, coherent tensor comparison, the ambient adjunction, the definition of v and both ctf endpoints. The proof to be written there is exactly old steps 1–2: bounded flat constructible models use the Noetherian constructible variant of lem-sf-flat-model; K-flat criteria and change-of-rings apply without flatness of B; finite module values remain finite after tensor. Etale inverse image preserves the chosen partition and constant trivializations. For the adjunction the old K-flat/K-injective resolutions, Hom-total isomorphism and global-sections identification are retained. cor-weil-finite-constructible-hom needs a nonnegative dimension bound, supplied by lem-kun-dimension-finite-type, with the empty case zero.

Step 2 cites lem-coef-etale-hom-thick-locus for the ACTUAL evaluation-transpose arrow, including its shift and connecting-map signs, and det-sf-flat-model-generation for exactly its etale clause (3); clause (2) puts these same generators in ctf. I opened both statements: neither a pro-etale-only claim nor mere full faithfulness is substituted. The new lisse-reduction statement takes precisely a finite-projective locally constant degree-zero L, not an arbitrary constructible K. It contains site-perfectness, exceptional and Q domains and Tor bounds, and the normalized local comparison. Its argument is old steps 4–6, preserved verbatim below. I checked thm-pur-open-complement-unconditional gives BOTH constructibility and the all-sheaf 2d bound for the quasi-compact complement in the separably closed finite-type ambient X; prop-exc-closed-tor then gives [a,b+2d+1]. S is finite type and separated, so cor-weil-finite-constructible-hom applies on S as well. The bounded-free Hom model and exact restriction are statements of the cited ringed-site lemmas. Stalk conservativity is applied to cohomology sheaves of the cone, not asserted as a derived theorem directly. I combined the exceptional preparation with lisse Hom reduction rather than creating a duplicate node for the exceptional-preservation clause already in lem-coef-etale-locally-closed-shriek.

Step 3 uses the new locally closed generator statement, which displays the entire typed composite and asserts both its invertibility and its equality with the specified v. Its argument is old steps 7–8. I checked lem-coef-finite-direct-image requires Q ctf and s separated finite type, not arbitrary derived inputs; the lisse reduction supplies Q. The ordinary c is defined by the ordinary counit; q and b have exactly the exceptional counit normalization in lem-coef-etale-locally-closed-shriek. prop-asd-internal-adjunction applies to the compactifiable immersion between Noetherian schemes. The open tensor and closed proper projection give the canonical compact-support projection, and lem-coef-internal-adjunction-pairing-change states the required equality of the ACTUAL maps; it is not merely an endpoint isomorphism. The new lemma is restricted to generator K=Rs_!L and contains neither thick generation nor the final arbitrary-pair theorem. Thick closure and generation therefore finish the etale isomorphism assertion with no hidden lemma.

Step 4 uses the generic transpose-coherence statement, with the strong monoidal functors and coherent associators already supplied by step 1. It proves the formal equations; it makes no assertion of invertibility or constructibility. Its retained arguments are old steps 10–12, including both-variable naturality, actual transposes of arbitrary morphisms, iterated evaluation for composition, and the scalar associator for quotient cocycles and the identity quotient. I wrote the general composite equation with H(h_K^{-1},h_M), so contravariance is typed correctly. Mathlib's exponential-comparison results require Cartesian monoidal categories and cannot specialize to derived tensor categories in one line; its individual curry laws remain tools for a later split. This new lemma is not a clause restated for the original geometric K,M.

Step 5 uses the new site-descent statement: it explicitly gives ctf witnesses, preservation and reflection of their Tor intervals, the B-linear monoidal scalar square, invertible beta comparisons at both coefficients and their evaluation-normalized Hom square. It assumes no v is invertible, so the etale theorem is genuinely required in the assembly. Its argument is old steps 13–14. I checked exactness of site inverse image and flat pullback in the actual statements; the scalar factor retains its B action. lem-sf-proetale-constructible-origin supplies etale witnesses, lem-sf-comparison-tor-amplitude(ii) reflects their interval, and lem-weil-finite-duality-site-comparison gives the evaluation beta, not an arbitrary isomorphism. lem-coef-monoidal-square-hom-transport applies only after the monoidal h and coherent successive quotient squares are supplied by flat-model reassociation. Its statement then gives the square and transports the equations. Thus no ambient pro-etale exceptional adjoint is silently used.

For all five new nodes I searched the whole DAG by concepts and candidate names, the blueprint with blueprint_refs.py search and ancestor, and the upstream Lean text. The Not duplicates section records the closest genuine candidates, opened above. The new statements are independently meaningful, with their objects and hypotheses introduced in full, and have empty proof/proof_deps and status unsplit. The new nodes divide roughly 3.2k, 3.2k, 2.3k, 2.2k and 2.3k characters of old work, rather than moving the theorem into one node. The full old argument text is retained next so that a subsequent worker does not have to reconstruct it from a shorter summary. Every new statement is a derived-category assertion when it identifies complexes. No Stacks tag was invented: the extraction follows the available blueprint/previous agent argument, and original cited nodes carry the literature tags for their own inputs.

Edge cases checked against each extracted statement: X or S empty (bounds zero and zero complexes), L rank zero, K/M zero, identity n=m, residue-field quotient m=1, nonflat A=O/(varpi^2) to B=O/(varpi), and a full coefficient chain 1<=r<=m<=n. None uses underived tensor for a nonflat arbitrary input: P is K-flat, and only L is locally free. E includes identity functors and composition without invertibility assumptions. F retains both input h identifications and B-linearity; scalar associativity is the pure-tensor reassociation, so the repeated quotient square has the same normalization.

I checked each assembly citation against its statement and wrote the verbatim full quote in citations.json. Assembly proof length is below 3000 characters and every step below 2000. The longer old steps are now explicitly owned by five unsplit nodes, not hidden inline. No compiler or build was run. All Mathlib queries were executed with msearch.py and the saved outputs read; unavailable LeanSearch replies are recorded as unavailable. No search is claimed that is absent from searches.jsonl.

## Argument preservation and assignment

- lem-coef-finite-hom-domain-calculus: old steps 1, 2.
- lem-coef-etale-lisse-hom-reduction: old steps 4, 5, 6.
- lem-coef-locally-closed-hom-generator: old steps 7, 8.
- lem-coef-evaluation-transpose-coherence: old steps 10, 11, 12.
- lem-coef-finite-hom-site-descent: old steps 13, 14.
- Old steps 3 and 9: retained thick-locus/generation assembly, citing the same existing nodes.

### Returned step 1 (verbatim)

Every finite-type $k$-scheme used here is Noetherian by [lem-weil-pbc-finite-type-over-noetherian], since $\operatorname{Spec}k$ is Noetherian (the only ideals of the field are zero and the whole ring). First work on the small etale site. Put $F_{A,B}(T)=T\otimes_A^L B$. By [lem-pur-derived-change-of-rings] this is an exact functor on the ambient derived categories, even when $B$ is not flat over $A$. For $T\in D^b_{ctf}(X,A)$, choose a bounded flat constructible model $P$ by the etale constructible variant of [lem-sf-flat-model]. The bounded flat complex is K-flat by [lem-kun-kflat-criteria], and [lem-pur-kflat-change-of-rings] shows that $P\otimes_A B$ is a K-flat complex of flat $B$-sheaves representing $F_{A,B}T$. Each of its finitely many terms is constructible: on a partition trivializing $P^i$ with finite module value $V$, its tensor is constant with value $V\otimes_A B$, which is finite since both rings and $V$ are finite. Thus [lem-sf-flat-model], now over $B$, gives $T_B\in D^b_{ctf}(X,B)$ with the same Tor interval. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] to the identity of the underlying topos with ring map $A\to B$ to obtain the canonical tensor comparison. On K-flat models it reassociates pure tensors, so it preserves tensor associativity. For later use, the same theorem for a morphism of small etale topoi with constant coefficients takes bounded flat models to bounded flat models in the same degrees. Inverse image is exact by [def-kun-projection-formula-map], and preserves constructibility: pull back a finite locally closed partition and its finite locally constant trivializations. Thus etale pullback preserves bounded constructibility and the Tor interval. Its compatibility with coefficient change is the termwise reassociation of these same tensor models.

Cited nodes: lem-pur-derived-change-of-rings, lem-sf-flat-model, lem-kun-kflat-criteria, lem-pur-kflat-change-of-rings, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-kun-projection-formula-map

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 1: domains and coefficient tensor; expanded agent argument (original document unavailable on this machine)"}

### Returned step 2 (verbatim)

The tensor–Hom adjunction used throughout is obtained as follows. Choose flat K-flat representatives for $T,K$ and a K-injective representative $I$ for $M$. By [lem-pur-hom-kflat-into-kinjective], $\mathcal Hom^\bullet(K,I)$ is K-injective. The total tensor of the two K-flat representatives is K-flat: tensoring it with an acyclic complex is the iterated tensor, first acyclic by K-flatness of $K$ and then by K-flatness of $T$. The functorial complex isomorphism [lem-sc-derived-hom-tensor-total] identifies $\mathcal Hom^\bullet(T,\mathcal Hom^\bullet(K,I))$ with $\mathcal Hom^\bullet(\operatorname{Tot}(T\otimes K),I)$. Taking zeroth global cohomology and applying [lem-pur-rhom-global-sections] gives the natural bijection $\operatorname{Hom}(T,H_A(K,M))=\operatorname{Hom}(T\otimes_A^L K,M)$, with the usual evaluation and transpose. For $H=H_A(K,M)$ define $v_{K,M}^{A,B}$ as the transpose of $F_{A,B}H\otimes_B^L K_B\cong F_{A,B}(H\otimes_A^L K)\xrightarrow{F_{A,B}(\mathrm{ev}_A)}M_B$, using the tensor comparison established in step 1. Choose a nonnegative integer $d_X$ bounding $\dim X$ by [lem-kun-dimension-finite-type], taking $d_X=0$ when $X$ is empty. Apply [cor-weil-finite-constructible-hom] over $A$ and over $B$, and step 1, to see that both the source and the target lie in $D^b_{ctf}(X,B)$. This also defines the same comparison for all ambient pairs, without a finiteness assertion on their internal Hom.

Cited nodes: lem-kun-dimension-finite-type, cor-weil-finite-constructible-hom, lem-pc-kflat-resolution, prop-pur-kinjective-resolutions-exist, lem-pur-hom-kflat-into-kinjective, lem-sc-derived-hom-tensor-total, lem-pur-rhom-global-sections

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 1: evaluation-defined map; expanded agent argument (original document unavailable on this machine)"}

### Returned step 3 (verbatim)

Fix $M$ and let $\mathcal C_M$ be the full subcategory of $D^b_{ctf}(X,A)$ where the evaluation-defined $v_{K,M}^{A,B}$ is invertible. By [lem-coef-etale-hom-thick-locus] the ambient isomorphism locus is thick in the etale derived category, hence $\mathcal C_M$ is thick in $D^b_{ctf}(X,A)$, for the actual comparison of step 2, including its shift and connecting-map normalization. Since $X$ is Noetherian, clause (3) of [det-sf-flat-model-generation] on the etale site generates $D^b_{ctf}(X,A)$ by $Rg_*j_!L$ with $L$ locally constant of finite projective stalks. Its clause (2) also puts the generators in $D^b_{ctf}$; the notation there is exactly $s_!=g_*j_!$, with closed pushforward exact. Thus it suffices to check these generators. This is the same flat-model/finite-stratification localization reduction as before, now supplied by an existing statement covering the chosen site.

Cited nodes: lem-coef-etale-hom-thick-locus, det-sf-flat-model-generation

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 2: localization reduction; expanded agent argument (original document unavailable on this machine); repair 2026-10-17: hidden arguments extracted into cited statement-only nodes"}

### Returned step 4 (verbatim)

The generator sheaf $L$ is site-perfect, not merely stalkwise perfect. Indeed lisseness supplies an actual etale covering on which $L$ is constant with finite $A$-module value $V$. Its flat stalks say that $V[0]$ has Tor interval $[0,0]$. The finite local ring $A$ is Noetherian (its set of ideals is finite), so [lem-weil-bounded-finite-tor-perfect] applied to $V[0]$ gives a finite projective module in degree zero, free because $A$ is local. Pulling this model back as a constant sheaf on that covering is the required site-perfect model. In particular $L$ is bounded constructible of Tor interval $[0,0]$. The etale finite-free calculation in step 6 will therefore apply to $L$.

Cited nodes: lem-weil-bounded-finite-tor-perfect

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 2: site-perfect stratum; expanded agent argument (original document unavailable on this machine)"}

### Returned step 5 (verbatim)

Set $N=Rs_A^!M$. To check its domain, factor $s=g\circ j$ with $g:\overline S\hookrightarrow X$ closed and $j:S\hookrightarrow\overline S$ open, so $Rs_A^!=j^*Rg_A^!$. Choose a nonnegative integer $d\geq\dim X$, possible by [lem-kun-dimension-finite-type], taking $d=0$ if $X$ is empty. The complement of $g$ is quasi-compact since $X$ is Noetherian. The field $k=\overline{\mathbf F}_q$ is separably closed, $A=A_{E,n}$ is a finite ring annihilated by a power of $\ell\neq p$, and the ambient scheme is the finite-type scheme $X$ of dimension at most $d$. Thus the general quasi-compact-open clause of the current [thm-pur-open-complement-unconditional] supplies both vanishing above $2d$ for all sheaves and constructibility of all higher direct images of constructible sheaves. No affine-chart specialization or nonemptiness of a chart is used. Thus [prop-exc-closed-tor] applies with $c=2d$: if $M$ has Tor interval $[a,b]$, $Rg_A^!M$ is bounded constructible with Tor interval $[a,b+2d+1]$. Its open pullback remains finite-Tor constructible by the etale pullback argument of step 1. Consequently $N\in D^b_{ctf}(S,A)$. This preservation is not a conclusion of the coefficient-comparison lemma.

Cited nodes: lem-kun-dimension-finite-type, thm-pur-open-complement-unconditional, prop-exc-closed-tor

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 3: closed exceptional preservation; expanded agent argument (original document unavailable on this machine)"}

### Returned step 6 (verbatim)

Put $Q=H_A(L,N)$. The stratum $S$ is a separated finite-type $k$-scheme. Choose a nonnegative dimension bound $d_S$ by [lem-kun-dimension-finite-type], with $d_S=0$ for the empty stratum. Apply [cor-weil-finite-constructible-hom] on $S$, with the same finite coefficient ring $A$, to the two finite-Tor constructible arguments just obtained; it gives $Q\in D^b_{ctf}(S,A)$. Here is the required etale coefficient comparison directly. Internal Hom restricts to every etale covering object by [lem-weil-pbc-ringed-internal-hom-exact-restriction]. On the cover of step 4 write $L=A^{r}[0]$ and choose a bounded flat model $P$ for $N$ using [lem-sf-flat-model]. The ringed-site Hom model [lem-weil-pbc-ringed-site-bounded-free-rhom-model] identifies $H_A(L,N)$ with $P^{\oplus r}$, and the $B$-coefficient Hom with $(P\otimes_A B)^{\oplus r}$. The evaluation-defined comparison is the identity between these models, including for $r=0$. Its cone therefore restricts to zero on a cover; equivalently its cohomology has zero geometric stalks, so [lemma-weil-pbc-geometric-stalk-conservative] makes it an isomorphism globally. We have the isomorphism $Q_B\xrightarrow{v_{L,N}^{A,B}}H_B(L_B,N_B)$, preserving evaluation. Only this local finite-free calculation, not the theorem being proved for arbitrary $K$, is used here.

Cited nodes: cor-weil-finite-constructible-hom, lem-kun-dimension-finite-type, lem-weil-pbc-ringed-internal-hom-exact-restriction, lem-weil-pbc-ringed-site-bounded-free-rhom-model, lem-sf-flat-model, lemma-weil-pbc-geometric-stalk-conservative

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 3: inner internal Hom; expanded agent argument (original document unavailable on this machine)"}

### Returned step 7 (verbatim)

For $s=gj$ and $N=Rs_A^!M$ from step 5, apply [lem-coef-etale-locally-closed-shriek]. It identifies the right adjoint of $Rs_!=g_*j_!$ with $j^*Rg^!$, and gives natural isomorphisms $b_{s,M}:N_B\xrightarrow{\sim}Rs_B^!M_B$ and $q_{s,L}:F_XRs_{!,A}L\xrightarrow{\sim}Rs_{!,B}L_B$, satisfying the displayed exceptional-counit identity in that lemma. This is an etale assertion proved by the closed-support route, so the choice of site agrees with steps 1–6. With $Q=H_A(L,N)$ from step 6, canonical internal adjunction [prop-asd-internal-adjunction] applies to the compactifiable locally closed immersion between the Noetherian schemes in step 1. Combine its isomorphisms on either side with
$$F_XRs_{*,A}Q\xrightarrow{c_{s,Q}}Rs_{*,B}Q_B\xrightarrow{Rs_*v_{L,N}}Rs_{*,B}H_B(L_B,N_B)\xrightarrow{Rs_*H_B(1,b_{s,M})}Rs_{*,B}H_B(L_B,Rs_B^!M_B).$$
The first arrow is [lem-coef-finite-direct-image], applicable because $Q$ is finite-Tor bounded constructible by step 6 and $s$ is separated of finite type. The second is the finite-free calculation of step 6 and the third uses the just-cited $b$. Thus all arrows, and $q_{s,L}$ identifying the final first argument with $F_XRs_{!,A}L$, are invertible. Step 8 identifies their composite with the specified comparison.

Cited nodes: lem-coef-etale-locally-closed-shriek, prop-asd-internal-adjunction, lem-coef-finite-direct-image

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 3 and paragraph 4 opening: generator comparison; expanded agent argument (original document unavailable on this machine); repair 2026-10-17: hidden arguments extracted into cited statement-only nodes"}

### Returned step 8 (verbatim)

The canonical etale open projection isomorphism and its coefficient/counit normalization are [lem-coef-etale-open-tensor]. Compose it with [lem-amb-proper-coproducts-projection] for the closed factor $g$ to obtain the compact-support projection in the internal-adjunction pairing; $g$ is proper of finite type between the Noetherian schemes already checked. Apply [lem-coef-internal-adjunction-pairing-change] to $L,M,N,Q$ of steps 4–6. Its ordinary direct-image comparison is exactly the counit-defined $c_{s,Q}$ used in step 7, its open/closed compact-support comparison is that of step 7, and its exceptional-counit hypothesis is precisely the identity in [lem-coef-etale-locally-closed-shriek]. Its local comparison $u$ is the evaluation-defined $v_{L,N}$ computed in step 6. The pairing identity in the cited lemma therefore identifies the entire step-7 composite, after $H_B(q_{s,L},1)$, with $v_{Rs_!L,M}^{A,B}$. All factors are invertible by step 7; hence this particular evaluation transpose is invertible on every generator.

Cited nodes: lem-coef-etale-open-tensor, lem-amb-proper-coproducts-projection, lem-coef-internal-adjunction-pairing-change, lem-coef-etale-locally-closed-shriek

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: identify the specified transpose; expanded agent argument (original document unavailable on this machine); repair 2026-10-17: hidden arguments extracted into cited statement-only nodes"}

### Returned step 9 (verbatim)

Step 8 puts every flat-lisse locally closed generator of the etale construction in step 3 in $\mathcal C_M$. Its triangle and summand closure, applied first through the dimension induction for each flat constructible sheaf and then through the finite stupid-truncation triangles of a flat constructible model, gives $\mathcal C_M=D^b_{ctf}(X,A)$. Since $M$ was any finite-Tor constructible complex, the specified comparison is an isomorphism for every pair in the statement.

Cited nodes: 

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: exactness in first argument; expanded agent argument (original document unavailable on this machine)"}

### Returned step 10 (verbatim)

The evaluation identity is, by construction, $\mathrm{ev}_B\circ(v_{K,M}^{A,B}\otimes1)=F_{A,B}(\mathrm{ev}_A)$ after the tensor comparison. For a morphism $u:T\otimes_A^L K\to M$ with transpose $u^\sharp:T\to H_A(K,M)$, uncurrying $v_{K,M}^{A,B}\circ F_{A,B}(u^\sharp)$ gives $F_{A,B}(u)$, by this identity and naturality. Uniqueness in tensor–Hom adjunction proves preservation of transposes. For $f:K'\to K$, compare $v_{K',M}F_{A,B}(H_A(f,1))$ and $H_B(f_B,1)v_{K,M}$. Their transposes, with source $F_{A,B}H_A(K,M)\otimes_B^L K'_B$, are both $F_{A,B}(\mathrm{ev}_{K,M}\circ(1\otimes f))$. For $g:M\to M'$, compare $v_{K,M'}F_{A,B}(H_A(1,g))$ and $H_B(1,g_B)v_{K,M}$. Their transposes are both $F_{A,B}(g\circ\mathrm{ev}_{K,M})$. Uniqueness of transpose gives both naturality equations.

Cited nodes: 

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: evaluation and tensor–Hom adjunction; expanded agent argument (original document unavailable on this machine)"}

### Returned step 11 (verbatim)

Write $\mu_A:H_A(M,N)\otimes_A^L H_A(K,M)\to H_A(K,N)$ for internal-Hom composition, characterized by evaluating first at $K$ and then at $M$. To compare $v_{K,N}F_{A,B}(\mu_A)$ with $\mu_B(v_{M,N}\otimes v_{K,M})$, tensor both maps with $K_B$ and evaluate at $N_B$. By the evaluation identity of step 10, both composites are $F_{A,B}$ of the successive evaluations $H_A(M,N)\otimes H_A(K,M)\otimes K\to H_A(M,N)\otimes M\to N$. Tensor associativity and uniqueness of transpose give the composition identity.

Cited nodes: 

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: composition identity; expanded agent argument (original document unavailable on this machine)"}

### Returned step 12 (verbatim)

Let $C=A_{E,r}$ with $1\leq r\leq m$. Compare the direct coefficient map $v^{A,C}_{K,M}$ with $v^{B,C}_{K_B,M_B}\circ F_{B,C}(v^{A,B}_{K,M})$. After tensoring with $K_C$ and evaluating, the first map yields $F_{A,C}(\mathrm{ev}_A)$; the second yields $F_{B,C}F_{A,B}(\mathrm{ev}_A)$ by applying step 10 twice. These agree under the associative identification $(T\otimes_A^L B)\otimes_B^L C\cong T\otimes_A^L C$. The K-flat tensor identifications in step 1 give precisely these identifications: both send a pure tensor $(t\otimes b)\otimes c$ to $t\otimes bc$. Uniqueness of transpose proves the displayed quotient cocycle. For $m=n$, both $v^{A,A}_{K,M}$ and the identity of $H_A(K,M)$ have transpose $\mathrm{ev}_A$, since $F_{A,A}$ and its tensor comparison are the identity under the unit scalar-extension identifications. Uniqueness of transpose gives $v^{A,A}_{K,M}=1$.

Cited nodes: 

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: successive coefficient changes; expanded agent argument (original document unavailable on this machine)"}

### Returned step 13 (verbatim)

For passage to the pro-etale site, $\nu_X^*$ is an exact module inverse image by [prop-weil-pbc-site-comparison-finite-level] and comes from the geometric morphism of [def-weil-pbc-site-comparison-morphism]. The ringed-topos tensor-pullback theorem [lem-weil-pbc-ringed-topoi-derived-tensor-pullback] supplies its natural derived tensor comparison. Flat sheaves remain flat by [lem-exc-constant-inverse-image-flat]. Thus the flat models in [lem-sf-flat-model] are pulled back to flat models. Termwise, inverse image identifies the constant $B$ sheaf with the constant $B$ sheaf and takes $P^i\otimes_A B$ to $(\nu_X^*P^i)\otimes_A B$ by the tensor comparison; the $B$ action in both expressions is on that same factor. Consequently $\nu_X^*(T\otimes_A^L B)\cong(\nu_X^*T)\otimes_A^L B$ as $B$-complexes, not merely after forgetting the $B$ action. On the tensor total complexes all these maps rebracket the same pure tensors, so their identifications agree with tensor associativity. This checks the coefficient and tensor identifications required for site transport.

Cited nodes: def-weil-pbc-site-comparison-morphism, prop-weil-pbc-site-comparison-finite-level, lem-exc-constant-inverse-image-flat, lem-sf-flat-model, lem-weil-pbc-ringed-topoi-derived-tensor-pullback

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: coefficient tensor and site passage; expanded agent argument (original document unavailable on this machine)"}

### Returned step 14 (verbatim)

By [lem-sf-proetale-constructible-origin], every bounded constructible pro-etale pair is $\nu_X^*K',\nu_X^*M'$ for bounded constructible etale complexes. Clause (ii) of [lem-sf-comparison-tor-amplitude] makes $K',M'$ finite-Tor when the pro-etale pair is. Apply [lem-weil-finite-duality-site-comparison] to these pairs over $A$ and $B$; step 1 verifies the $B$-domains. Its canonical evaluation comparisons $\beta_A,\beta_B$ are invertible. Apply [lem-coef-monoidal-square-hom-transport] with $U_A=U_B=\nu_X^*$, $F=F_{\mathrm{et},A,B}$, $G=F_{\mathrm{proet},A,B}$, and the monoidal scalar/site comparison of step 13. Under its identifications the formula is
$$v_{\mathrm{proet}}=\beta_B\circ\nu_X^*(v_{\mathrm{et}})\circ F_{\mathrm{proet}}(\beta_A^{-1}).$$
Hence $v_{\mathrm{proet}}$ is invertible by step 9. The transport lemma also carries evaluation, tensor–Hom transposes, naturality and internal-Hom composition from steps 10–11. For $A\to B\to C$, step 13's tensor reassociations supply its coherent-square hypothesis; its composition clause transports step 12's identity and quotient cocycle. Thus all the required compatibilities hold on the second site with the canonical site-comparison maps.

Cited nodes: lem-sf-proetale-constructible-origin, lem-sf-comparison-tor-amplitude, lem-weil-finite-duality-site-comparison, lem-coef-monoidal-square-hom-transport

Source: {"document": "literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/thm-coef-finite-hom.md", "place": "original paragraph 4: pro-etale internal Hom and all compatibilities; expanded agent argument (original document unavailable on this machine); repair 2026-10-17: hidden arguments extracted into cited statement-only nodes"}


## Dry-run repair

The first complete server preflight rejected the generic coherence node because its only bracketed citations contained two ids in one bracket, which the citation scanner did not recognize. I separated those into one bracket per id and refreshed its verbatim quote; the mathematical statement is unchanged.
