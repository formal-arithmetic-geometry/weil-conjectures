# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-finite-coefficient-input-models.json`: the statement is byte-for-byte unchanged. Eight proof steps are replaced by three assembly steps (1809 characters in their texts).
- `dag/nodes/sec-smooth-purity/lem-sp-bounded-flat-coefficient-site-square.json`: statement, unsplit; no Mathlib match. Homological work on a supplied bounded flat complex, without constructibility or Noetherianity.
- `dag/nodes/sec-smooth-purity/lem-sp-constructible-coefficient-site-square.json`: statement, unsplit; no Mathlib match. Finiteness work on a supplied bounded termwise constructible complex, without flatness.
- `citations.json`: verbatim statement quotations for every parent proof citation.

## Attachments

None. I searched the project for the blueprint tag and its notions. The project's `Sheaf/Paper/FiniteCoefficientInputModels.lean` theorem `AlgebraicGeometry.finiteCoefficientInputModels` ends in `sorry`; its definitions alone do not prove the item. The upstream `hasTorAmplitudeIn_iff_exists_flatConstructibleModel` is the existing input theorem, not an attachment for the whole item. The coefficient constructibility declarations in `WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/ExtendScalars/Constructible.lean` assume schemes separated and finite type over a field and do not state the entire item or either new result in the required generality.

## WANTED

None. The source texts used below are present locally.

## Return repaired

The return asks for a workload re-split, not a shorter retelling. There were no node files, report or search log in the supplied Q18 sandbox, only dispatcher brief markers. I therefore copied the live item, which has precisely the eight-step returned proof (and its maintainer fix adding the constant-module citation in old Step 5). No git command was run in the read clone. The current reviewed statement, all maintainer metadata, citations, source and earlier Mathlib search records on the item were retained.

Two comparable independent proof tasks now replace the long argument: old Steps 2, 3, 4 and 8 (2763 characters) go to the bounded-flat square, while old Steps 5, 6 and 7 (2831 characters) go to the constructibility square. Old Step 1 remains in the parent. Every old argument is reproduced verbatim below, attributed to its new statement-only node. New workers need only their own node and the specified source places; the report also preserves the complete prior reasoning and the citations it used. Neither new node has proof steps, proof dependencies, a proof sketch inside its statement, or a Lean module. Their differing input hypotheses isolate the two arguments: flatness for the first, constructibility for the second. Neither asserts existence of the input model. Neither states the whole parent.

The repair keeps the blueprint route: Charts in det-sp-reduction-exceptional, via lem-sp-et-proet-coefficient-compatibility. The inherited unit is sk-thm-sf-compatibility; its coefficient clause uses sk-lem-sp-reduction and the finite-flat-model route. I read both unit records and the chapter record. There is no change to a chapter, unit, target, coefficient category, or the lecture-notes purity route.

## Review by Q18

I read the parent statement, all eight old proof steps and each of their 15 cited node statements, not their dependency lists alone. I read the current blueprint coefficient-reduction statement and its unit, the source theorem in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/FlatModel.lean` lines 160-209, and the forward sheaf and bounded-complex arguments in `sk-thm-pe-constructible-comparison-equivalence.proof.md`. For the homological work package I read Stacks sites-cohomology.tex labels lemma-bounded-flat-K-flat (06YQ), lemma-pullback-K-flat (0G7E), lemma-derived-base-change (06YY), lemma-pullback-tensor-product (07A4), lemma-tor-amplitude (08G1), and sites-modules.tex lemma-tensor-product-pullback (03EL). For the constructibility work package I read etale-cohomology.tex lemma-tensor-constructible (0GKB) and lemma-constructible-abelian (03RZ), as well as the blueprint forward comparison proof. I also read more-etale.tex remark-Rf-lower-shriek-change-of-rings (0GL6): this is the surrounding coefficient-compatibility motivation and is not a source claiming the model theorem by itself.

Parent Step 1 uses exactly lem-sf-etale-flat-constructible: its statement requires a finite commutative coefficient ring, a Noetherian scheme, bounded constructibility and the explicit ordered Tor interval, all given in the parent. It supplies flat constructible terms, strict support and a derived isomorphism, exactly what this step takes.

Parent Step 2 uses exactly lem-sp-bounded-flat-coefficient-site-square. Its statement supplies the four K-flat models, flat terms, strict interval, three derived identifications, the B-linear chain comparison, its canonical derived image, and the universal Tor interval. Substituting Q(P) = L under Step 1's isomorphism is merely functoriality. Its hypotheses do not need constructibility or Noetherianity, and the parent certainly has its finite rings and bounded flat complex. The fourth comparison model N_B(P tensor B) is included explicitly; it cannot be mistaken for restriction of coefficients to A. All derived identifications are isomorphisms in the derived category, not just isomorphisms of cohomology groups.

Parent Step 3 uses exactly lem-sp-constructible-coefficient-site-square. Its statement is about an underived bounded complex with constructible terms, so P is an admissible input without any new condition. It gives constructible cohomology of C, C_B, N_A C and N_B C_B, with the same interval and the actual global finite-stratification predicate. Step 2 then identifies these objects with the objects named in the parent. The new finiteness lemma does not assert that an arbitrary C_B is a derived scalar extension: the parent uses the K-flat result of Step 2 for that identification. This distinction is why the two new nodes are independent work packages, rather than weakened restatements of a clause.

I checked the old arguments assigned to the new nodes for C1 and C4. The ringed K-flat pullback statement has no flatness hypothesis on its structural ring map, and it supplies flat terms as well as K-flatness. The derived pullback statement supplies the required computing comparison on a K-flat complex with flat terms. The module tensor statement is natural in both factors; the constant-module inverse-image statement is natural in all A-linear maps, hence in multiplication by b on B, and thus preserves the B-action needed for the chain comparison. The derived tensor source specifies its representative construction. The Tor flat-model equivalence tests every module sheaf on the target site; it imposes neither enough points nor constructibility. These are exactly the statements the retained homological argument needs.

For the retained finiteness argument I checked that the lisse scalar-extension statement applies only to a nonempty stratum with a geometric point; empty strata have the zero sheaf and are treated directly. The finite module value M tensor_A B is finite over finite B since a finite generating family of M gives a finite generating family over B. The kernel/cokernel clauses of thm-constructible-serre apply to the complex terms and then the kernel, not to an assumed constructible image. The finite affine cover gives quasi-compactness, and locally Noetherian quasi-separatedness is precisely lem-weil-pbc-locally-noetherian-quasi-separated. Finite rings are Noetherian. These verify the qcqs and coefficient hypotheses of sk-thm-pe-constructible-comparison. Its affine-local constructibility convention alone is insufficient for our global convention, so the new statement expressly retains the stratum-restriction argument using lem-weil-pbc-comparison-pullback and the constant-module isomorphism; the same finite partitions and covers work. Exact comparison gives the actual cohomology isomorphism, not an unsupported cohomology identification.

I tested both new statements with the zero complex, zero coefficient ring, empty scheme, a=b, A=B with the identity map, and the nonflat quotient Z/4 -> Z/2. For P=A[0] the homological result gives B[0] of Tor amplitude [0,0] over B; it never claims that B is flat over A. For the second lemma one may take the nonflat sheaf (Z/2)[0] over Z/4: its underived scalar extension is constructible even though underived tensor does not in general compute derived tensor. For the empty scheme a single empty stratum meets the positive-strata convention for pro-etale constructibility. Arbitrary acyclic, unbounded test complexes remain in the K-flat assertion. No source error or statement dispute was found. The earlier correction 06YS -> 06YQ remains in the retained text; the shared cited node was not edited.

I searched the whole DAG and all blueprint chapters with blueprint_refs.py for flat coefficient, bounded flat, constructible scalar, constructible comparison, coefficient site and termwise constructible, and searched DAG statements/titles and source tags for the nearby results discussed below. Every new node has a filled blueprint.from.place, the required ancestor and via chain, and same_as=[]. I ran two phrasings of LeanFinder for each new node, LeanSearch (unavailable because of rate limiting), fully qualified Loogle queries and Mathlib grep; the raw results are retained in search-results and exactly transcribed in the node search records. The earlier unqualified Loogle patterns were invalid, explicitly recorded as such, and replaced. The valid Loogle hits are general cochain functors or sheaf evaluation, not these site/constructibility assertions. Mathlib grep found no K-flat/Tor-amplitude implementation and no constructible-module-sheaf theorem. Pro-etale topology and finite-type generators are definitions or different finiteness notions. No match was promoted without a theorem. No Lean was written or compiled.

The parent's longest step is below 2000 characters and the complete assembly is below 3000. The new nodes have no proof steps to hide additional lemmas in; their future workers will split the distinct retained arguments below. B (self-contained statements, definitions, source tags, actual searches), C (cited statements, all non-elementary inputs, no cycles), D (two genuinely separate tasks and no transfer of the whole theorem), and E (hypotheses, coefficient action, actual objects and small cases) were checked against the open statements and sources.

## Not finished

The two new nodes are deliberately unsplit, as the return requires. They are ready for separate workers. The parent is a short assembly of their stated conclusions, not a claim that their Lean proofs are complete.

## Retained argument: lem-sp-bounded-flat-coefficient-site-square

This section preserves old Steps 2, 3, 4 and 8 verbatim. The new statement uses Q(P) instead of a separately supplied isomorphic L, and works without Noetherianity, constructibility or ell-power torsion. These assumptions were never used in these four steps.

### Old Step 2

The bound $P^q=0$ for $q>b$ makes $P$ a bounded-above complex of flat module sheaves. Thus [lem-pc-bounded-above-flat-kflat-site] makes it K-flat on the ringed small etale site $(X_{\rm et},A_X)$. This is K-flatness against arbitrary acyclic complexes, not just bounded acyclic test complexes.

Source: literature/stacks-project/sites-cohomology.tex; Tag 06YQ, label lemma-bounded-flat-K-flat (the cited node has the older incorrect tag 06YS in its source field, but its statement is precisely this lemma)

### Old Step 3

Apply [lem-weil-pbc-ringed-pullback-preserves-kflat] to the identity topos with ring map $A_X\to B_X$, and to the site comparison with its constant-ring identification from [lem-sf-comparison-pullback-exact]. Starting with $P$, these applications give K-flatness and flat terms for $P\otimes_A B$ and $N_XP$; applying the identity-topos change of rings on the pro-etale site to $N_XP$ gives them for $(N_XP)\otimes_A B$. All these functors send zero modules to zero modules, so the degree interval stays $[a,b]$. The computing comparison of [lem-weil-pbc-ringed-topoi-derived-pullback], applied to the two coefficient morphisms, identifies the first and third complexes with $L_B$ and $(N_XL)_B$. Exactness in [lem-sf-comparison-pullback-exact] identifies termwise $N_XP$ with $N_XL$: it sends the isomorphism represented by $P$ to its derived isomorphism. No coefficient ring map in the K-flat pullback statement is assumed flat.

Source: literature/stacks-project/sites-cohomology.tex; Tags 0G7E (lemma-pullback-K-flat) and 06YY (lemma-derived-base-change), applied to the identity-topos coefficient morphisms and the comparison morphism

### Old Step 4

For every degree $q$, apply [lem-weil-pbc-ringed-topoi-module-pullback-tensor] to $P^q$ and the etale $A_X$-module $B_X$. The constant-module isomorphism of [lem-sfb-geometric-inverse-image-constant-module], with $R=A$ and $M=B$, identifies $N_XB_X$ with the pro-etale $B_X$, including its $A$-action. Hence the canonical comparison gives $N_X(P^q\otimes_A B)\simeq N_XP^q\otimes_A B$. It is $B_X$-linear: scalar multiplication by a section of $B_X$ acts on the second tensor factor on both sides. Naturality in $P^q$ makes the isomorphisms commute with the differentials, giving the asserted isomorphism of complexes. Its image in the derived category is the canonical derived tensor comparison of [lem-weil-pbc-ringed-topoi-derived-tensor-pullback]: that node defines the comparison on K-flat representatives by these same termwise tensor maps. In particular the fourth complex also represents $(N_XL)_B$.

Source: literature/stacks-project/sites-modules.tex; Tag 03EL, label lemma-tensor-product-pullback; sites-cohomology.tex Tag 07A4, label lemma-pullback-tensor-product, its comparison on K-flat representatives

### Old Step 8

Finally apply the implication from a flat model to Tor amplitude in [lem-sp-ringed-site-tor-flat-model], on $(X_{\rm et},B_X)$, $(X_{\rm proet},A_X)$, and $(X_{\rm proet},B_X)$ respectively. Step 3 has supplied, for $L_B$, $N_XL$ and $(N_XL)_B$, flat representatives zero outside $[a,b]$. The cited equivalence therefore gives Tor amplitude in precisely this interval for all three objects, against every module sheaf on the appropriate site. Together with Steps 1-7 this proves every claim. In particular $B$ itself is never used as a K-flat or flat $A$-module: only $P$ and its pullbacks are used to compute the derived extensions.

Source: literature/stacks-project/sites-cohomology.tex; Tag 08G1, label lemma-tor-amplitude, implication (2) to (1)

## Retained argument: lem-sp-constructible-coefficient-site-square

This section preserves old Steps 5, 6 and 7 verbatim. The new statement names the supplied arbitrary underived input C instead of P. The old argument only used termwise constructibility and strict bounds here; representation as a derived scalar extension belongs to the separate homological node. The kernel/cokernel argument is also applied over A to C itself before exact site comparison. This is the same displayed two-kernel/cokernel calculation, with A in place of B.

### Old Step 5

Fix a degree $q$ and a finite constructible stratification witnessing constructibility of $P^q$ in [def-weil-pbc-etale-constructible-sheaf]. On a stratum $i:S\to X$ the tensor comparison [lem-weil-pbc-ringed-topoi-module-pullback-tensor] identifies $i^*(P^q\otimes_A B)$ with $i^*P^q\otimes_A i^*B_X$, and the constant-module isomorphism of [lem-sfb-geometric-inverse-image-constant-module] (with $R=A$, $M=B$, $f=i$) identifies $i^*B_X$ with $B_S$, compatibly with the $B$-action by its naturality in the $A$-linear maps $b\cdot-:B\to B$; so $i^*(P^q\otimes_A B)\simeq i^*P^q\otimes_A B_S$. The scalar-extension clause of [lem-pod-lisse-tensor-and-scalar-extension] makes this a finite locally constant $B_S$-module: on a trivializing etale cover it has value $M\otimes_A B$ for a finite $A$-module $M$. Concretely, if $r$ elements generate $M$, their tensors with $1$ generate $M\otimes_A B$ over the finite ring $B$, so its underlying set is finite. Empty strata give the zero sheaf and need no choice of a geometric point; on every nonempty stratum a geometric point exists, as in the lisse lemma. Thus the same finite partition witnesses constructibility over $B$ for each term of $P\otimes_A B$.

Source: literature/stacks-project/etale-cohomology.tex; Tag 0GKB, label lemma-tensor-constructible, same-stratification argument; the local scalar-extension input is the existing lisse lemma

### Old Step 6

Put $Q=P\otimes_A B$. By Step 5 its terms are constructible $B_X$-modules. Apply [thm-constructible-serre] over the finite ring $B$: $Z^q=\ker(Q^q\to Q^{q+1})$ is constructible, and $H^q(Q)=\operatorname{coker}(Q^{q-1}\to Z^q)$ is constructible. These are maps between constructible sheaves, so the kernel and cokernel clauses apply directly. Since $Q$ is zero outside $[a,b]$, so is its cohomology. Step 3 therefore proves bounded constructibility of $L_B$.

Source: literature/stacks-project/etale-cohomology.tex; Tag 03RZ, label lemma-constructible-abelian, kernel and cokernel clauses

### Old Step 7

The given finite affine cover makes $X$ quasi-compact. It is locally Noetherian, so [lem-weil-pbc-locally-noetherian-quasi-separated] makes it quasi-separated. Each finite coefficient ring is Noetherian, since it has only finitely many ideals. Consequently the forward constructible-sheaf comparison in [sk-thm-pe-constructible-comparison] applies to both $A$ and $B$. Exactness of $N_X$ in [lem-sf-comparison-pullback-exact] gives $H^q(N_XL)\simeq N_XH^q(L)$, so $N_XL$ is bounded constructible. Apply the same statements over $B$ to the bounded constructible etale complex $L_B$ obtained in Step 6. This gives bounded constructibility of $N_XL_B$, hence of $(N_XL)_B$ by Step 4. To check the global finite-stratification convention explicitly, take the finite stratification of each etale cohomology sheaf. For each stratum $i:S\to X$, [lem-weil-pbc-comparison-pullback] identifies $i^*N_XF$ with $N_Si^*F$. A trivializing etale covering is also a pro-etale covering, and [lem-sfb-geometric-inverse-image-constant-module] identifies its constant values with the same finite modules. Thus that same finite partition witnesses the pro-etale constructibility required here.

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-constructible-comparison/sk-thm-pe-constructible-comparison-equivalence.proof.md; forward directions of (1) and (2); locally Noetherian quasi-separatedness is the separately cited scheme lemma

## Not duplicates

The following statements were opened in full. These are workload packages requested by the return: they gather independent several-step arguments with materially different hypotheses from the parent. Neither is a renamed existence theorem or the whole input-model statement.

lem-sp-bounded-flat-coefficient-site-square vs lem-sfb-site-inverse-image-multimap-universal: The existing node concerns Universality of inverse-image units for natural maps with finitely many inputs; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-sfb-site-inverse-image-bilinear-adjunction: The existing node concerns Bilinear adjunction for the inverse image of a morphism of sites; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-weil-pbc-ringed-slice-normalized-comparisons: The existing node concerns Existence of normalized slice tensor, Hom and Koszul comparisons; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs def-coef-semilinear-geometry-derived: The existing node concerns Derived geometric system operations and normalization; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs def-sf-point-evaluation-tensor-coherence: The existing node concerns Signed tensor coherence for point sections; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs def-sf-point-evaluation-scalar-data: The existing node concerns Balanced scalar comparison for point sections; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-coef-signed-single-dual-restriction: The existing node concerns Normalized slice comparison for a single coefficient dual; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-sf-open-operation-models: The existing node concerns Open operation comparisons with fixed tensor models and right square; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-weil-ramified-finite-pullback-comparison: The existing node concerns Normalized finite pullback comparison along coefficient quotient base change; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs lem-weil-finite-pullback-transition-generators: The existing node concerns Composite finite pullback transitions reduce both tensor coefficients; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs def-sf-point-evaluation-tensor-data: The existing node concerns Normalized tensor presentation for point sections; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-bounded-flat-coefficient-site-square vs def-sf-point-evaluation-derived-compatibility: The existing node concerns Representative-normalized derived point comparisons; the new assertion instead starts with an arbitrary bounded flat etale complex and certifies all four coefficient/site vertices, their strict interval, universal Tor bounds and the canonical derived scalar/site comparison. It does not replace or reassert that existing result.

lem-sp-constructible-coefficient-site-square vs lem-trf-constructible-etale-finite-affine-syzygy: The existing node concerns Finite affine-free syzygies of constructible etale modules; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-sfb-discrete-noetherian-constructible-serre: The existing node concerns Constructible sheaves over a discrete Noetherian ring form a weak Serre subcategory; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-sfb-finite-flat-constructible-total-tensor: The existing node concerns Bounded flat constructible total tensor on the etale site; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-constructible-module-finite-presentation: The existing node concerns A constructible sheaf of modules on a qcqs scheme is a cokernel of a map between finite sums of extensions by zero of Lambda from affine etale objects; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs thm-constructible-serre: The existing node concerns Constructible sheaves form a weak Serre subcategory; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-module-sheaf-colimit-constructible-data: The existing node concerns Filtered constructible maps with factorization and relations; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-v2-constructible-prime-field-filtration: The existing node concerns Finite coefficients admit prime-field extension trees; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-constructible-stratification-intersection: The existing node concerns Common refinement of two stratifications with constructible strata; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-constructible-coefficient-serre: The existing node concerns Exact closure of intrinsic constructible sheaves in the site coefficient universe; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-constant-subsheaf-generic: The existing node concerns Generic constancy of a subsheaf of a constant finite sheaf; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-weil-proetale-constructible-exact-closure: The existing node concerns Exactness closure of globally constructible pro-etale module sheaves; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-constructible-coefficient-site-square vs lem-kun-03sa: The existing node concerns Constructible generation; the new assertion instead treats termwise finite scalar extension and comparison of an arbitrary bounded constructible etale complex, including same-stratification local module values and all four cohomology objects. It assumes no flatness and makes no derived-scalar computation claim.

lem-sp-bounded-flat-coefficient-site-square vs lem-sp-finite-coefficient-input-models: The parent asserts existence of a constructible flat replacement and bounded constructibility; this node takes a supplied flat complex and asserts only the homological square, with no constructibility or Noetherian hypothesis.

lem-sp-bounded-flat-coefficient-site-square vs lem-sfb-etale-proetale-cube-flat-model: The cube theorem starts with an already K-flat flat-term model and normalizes six faces involving a scheme morphism. This assertion starts with a bounded flat model, proves K-flatness, retains its strict interval and universal Tor bounds, and treats the scalar/site square. Face normalization is a reusable input, not the whole bound-certification argument.

lem-sp-bounded-flat-coefficient-site-square vs lem-weil-pbc-ringed-pullback-preserves-kflat: The existing theorem treats one ringed pullback of an already K-flat input; it does not assert derived representative identifications, a normalized square of two coefficient morphisms and comparison, or a strict Tor interval.

lem-sp-bounded-flat-coefficient-site-square vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: The existing theorem gives derived monoidality for one ringed morphism on two derived objects. The new statement certifies strict support, flatness, K-flatness and universal target Tor bounds of concrete input-model vertices, with the scalar/site comparison on them.

lem-sp-bounded-flat-coefficient-site-square vs lem-sfb-kflat-scalar-comparison-normalization: The existing mate normalization assumes a K-flat input and treats no strict support interval or universal Tor tests. The new result supplies the bounded-flat certificate and target Tor bounds; its comparison normalization can use this existing node.

lem-sp-bounded-flat-coefficient-site-square vs lem-sp-ringed-site-tor-flat-model: The existing equivalence treats a single object on one ringed site. This new result retains the same model simultaneously across coefficient and site change with its canonical comparison.

lem-sp-bounded-flat-coefficient-site-square vs lem-sp-open-scalar-site-coherence: The existing statement concerns open extension, its scalar/site coherence square and composition. The new node concerns input complexes alone, with no open immersion or extension by zero.

lem-sp-constructible-coefficient-site-square vs lem-sp-finite-coefficient-input-models: The parent starts with a bounded finite-Tor derived object and asserts existence and K-flatness of representing complexes. The new node assumes a bounded termwise constructible complex, allows nonflat terms, and only asserts underived finiteness on the four vertices.

lem-sp-constructible-coefficient-site-square vs lem-pur-finite-reduction-etale-constructibility: The existing result assumes a finite-Tor derived object and proves etale derived scalar constructibility. This node permits nonflat terms and concerns underived scalar complexes, explicit same-stratification values and the two pro-etale comparison vertices.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-bounded-constructible-exact-scalar-extension: The existing theorem assumes exact scalar extension on a pro-etale ring-object category. The new theorem uses no flatness or exactness of scalar extension; it works termwise on etale complexes and compares to the pro-etale site.

lem-sp-constructible-coefficient-site-square vs sk-thm-pe-constructible-comparison: The existing equivalence uses an affine-local pro-etale constructibility convention and performs no coefficient change. The new statement includes the same global finite stratifications, explicit finite scalar values and underived scalar complexes; its cohomological comparison uses the existing forward theorem.

lem-sp-constructible-coefficient-site-square vs lem-pe-finite-coefficient-model-comparison: The existing statement compares discrete condensed and ordinary pro-etale coefficient models. This statement compares etale and pro-etale sites and two finite rings on a supplied underived complex.

lem-sp-constructible-coefficient-site-square vs lem-sfb-finite-flat-constructible-total-tensor: The existing theorem tensors two flat constructible A-complexes over a fixed ring and computes a derived tensor. Here the coefficient B may be nonflat over A, C may have nonflat terms, and the conclusion has a different target-ring action and pro-etale comparison vertices.


## Additional same-tag comparisons from server dry run

I opened each statement listed by the server duplicate gate. These local/order-dependent tag hits add no mathematical duplicate. The following lines continue the Not duplicates comparison.

lem-sp-bounded-flat-coefficient-site-square vs lem-per-galois-descent-monodromy-tensor: The existing theorem computes monodromy and tensor of descended modules along a connected finite Galois cover; it asserts no bounded complex, K-flatness, universal Tor interval, or coefficient/site square.

lem-sp-bounded-flat-coefficient-site-square vs lem-per-local-system-tensor-monodromy: The existing theorem identifies tensors and monodromy of unbounded-rank local systems at a geometric stalk. The new theorem concerns bounded flat complexes and their coefficient/site vertices, without a connectedness or local-system hypothesis.

lem-sp-bounded-flat-coefficient-site-square vs lem-per-proetale-scalar-slice-comparison: The existing theorem normalizes scalar extension across literal restriction to a pro-etale object U. The new theorem compares the etale and pro-etale sites and supplies strict bounds and universal Tor certificates, with no choice of a localized object.

lem-sp-bounded-flat-coefficient-site-square vs lem-pd-ringed-tensor-adjunction-mate: The existing theorem identifies an ordinary oplax tensor map with an adjunction mate. It gives no bounded-flat/K-flat complex certificate or same-interval Tor tests on coefficient/site vertices.

lem-sp-bounded-flat-coefficient-site-square vs lem-pd-section-ordinary-oplax-normalization: The existing statement identifies ordinary internal/section module tensor maps for condensed coefficients. The new statement concerns ordinary finite constant rings, bounded complexes and their Tor bounds on two sites.

lem-sp-bounded-flat-coefficient-site-square vs lem-pod-etale-stalk-tensor-scalar: The existing theorem identifies geometric stalks of ordinary tensor and scalar sheaves. It does not treat bounded complexes, K-flatness, change of site, derived representative isomorphisms or a Tor interval.

lem-sp-bounded-flat-coefficient-site-square vs lem-pod-lisse-tensor-and-scalar-extension: The existing theorem preserves lisse sheaves under scalar extension and computes their stalks. The new node does not assume lisse or constructible terms and proves the homological square for bounded flat complexes.

lem-sp-bounded-flat-coefficient-site-square vs def-weil-pbc-actual-finite-coefficient-transport: This definition fixes actual valuation-ring inclusions and completed adic coefficient transport; the new theorem takes arbitrary finite rings on ordinary sites and proves bounded-flat and Tor assertions.

lem-sp-bounded-flat-coefficient-site-square vs def-weil-pbc-canonical-ringed-tensor-comparison: This definition records ordinary pure-tensor normalization data. The new statement proves simultaneous K-flat models and same-interval universal Tor bounds, and identifies their derived scalar/site map.

lem-sp-bounded-flat-coefficient-site-square vs def-weil-pbc-normalized-scalar-restriction: This definition specifies a comparison for completed coefficient sheaves along a scheme morphism. The new theorem proves bounded-flat certificates at finite constant coefficients across etale/pro-etale comparison, with no completed rings.

lem-sp-constructible-coefficient-site-square vs lem-weil-pbc-constructible-subobjects-noetherian: The existing node asserts constructibility of every subsheaf on a Noetherian etale scheme. The new node concerns underived scalar extension with finite local module values and the global stratifications and cohomology of four coefficient/site vertices, rather than subobjects.
