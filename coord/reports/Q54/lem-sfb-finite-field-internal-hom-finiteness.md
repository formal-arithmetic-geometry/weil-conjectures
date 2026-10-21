# Stage-1 repair: finite-field internal-Hom finiteness

Item: lem-sfb-finite-field-internal-hom-finiteness. Group Q54. Date 2026-10-21.

## Worker report

The returned 13185-character proof is replaced by five short assembly steps using four new statement-only nodes. The statement, statement dependencies, Lean record and imported metadata are unchanged against the current repository. This is the requested deliberate re-split of an already reviewed node.

The retained attempt had completed the mathematical refinement but delivered its four new nodes as `split` with proof steps. The first dry run of this retry reproduced exactly the four status-gate failures. The current route note explicitly says to deliver these nodes statement-only with status `unsplit`: I cleared their proof arrays and proof dependencies, set proof_origin to null, removed their split_report fields, and retained their statements, source records, blueprint references and logged Mathlib searches. Their extracted arguments are preserved below as report notes for the next stage-1 workers. This resolves the earlier gate failure without changing any launcher or checker.

I also corrected C4 in the assembly: the ringed open/closed statement does not explicitly state exactness of open inverse image. Step 4 now cites the exact abelian inverse-image theorem and explains why constant-coefficient module kernels and cokernels are the underlying abelian ones. No new lemma is needed for that two-line lift of exactness.

## Files written

All five node files are under dag/nodes/sec-six-functors-basics/ in the Q54 sandbox.

- lem-sfb-finite-field-internal-hom-finiteness.json: existing statement; split, with the unchanged conclusion and a short assembly proof.
- lem-sfb-finite-field-proetale-direct-image.json: new statement-only unsplit lemma; finite-field ordinary derived direct-image finiteness on the pro-etale site; Mathlib: no match.
- lem-sfb-finite-field-closed-support.json: new statement-only unsplit lemma; bounded constructibility of the ambient closed exceptional inverse image; Mathlib: no match.
- lem-sfb-finite-field-stratified-generation.json: new statement-only unsplit lemma; finite construction from g_* j_! L using shifts and triangle extensions; Mathlib: no match.
- lem-sfb-finite-field-lisse-internal-hom.json: new statement-only unsplit lemma; local-system Hom cohomology formula and preservation of the second input's interval; Mathlib: no match.
- citations.json: one verbatim quotation for each node cited by each item step.
- report.md: this report and substantive self-review, including the retained extracted arguments.

Four new nodes; zero Mathlib leaves. No unit realization changes: this item is not the unit's statement node. The prior report is preserved as retained-report-Q54-proof-bearing.md. The earlier N5/Q27 reports, repair scripts, extracted Bhatt--Scholze text and searches.jsonl remain sandbox working records. No Lean, repository, launcher or checker file is written; no compiler, Lake, build or local project checker is run. The required delivery wrapper is the only git-producing operation.

## Attachments

None. The exact tag search in lean/WeilConjectures returns no declaration of the item. Concept searches locate adic and Weil-sheaf local-system Hom interfaces, with different coefficient/ground-field assumptions. The actual item declaration AlgebraicGeometry.ProEtale.finiteField_constantModel_internalHom at lean/Sheaf/Paper/FiniteFieldInternalHomFiniteness.lean:156 has a literal sorry. It is not a finished proof or an attachment. None of the four new pro-etale finite-field statements is supplied by those upstream interfaces.

## WANTED

None. Bhatt--Scholze and the Stacks source files used by the retained packet are available locally. No prohibited SGA source is used.

## What was wrong and what remains

The old proof contained large inline arguments, especially its coefficient comparison, direct-image transfer, support-triangle argument, bounded stratified generation, and local-system computation. Existing coefficient-equivalence/comparison and open/closed Hom nodes replace the already recorded comparisons. The four remaining non-elementary tools become new nodes. None restates the item: they have, respectively, a morphism/direct-image conclusion, a closed right-adjoint conclusion, a finite-generation conclusion, and a degree-zero locally constant first input with a cohomology formula. The item still assembles them on strata and proves the finite induction.

There is no statement dispute and no unresolved mathematical objection. The four new lemmas deliberately remain unsplit for future stage-1 work. Their proposed arguments are retained as report notes rather than asserted as completed node proofs. The current item keeps precisely its prior statement, including arbitrary positive-characteristic k, p different from ell, and ambient internal Hom without a finite-Tor hypothesis.

## Not duplicates


Before creating the four nodes I searched all dag/nodes by id, statement keywords and literature places (6.7.2, 6.7.11, 6.3.3, 6.7.13, 08JB, 08JJ), and the whole imported blueprint using tools/blueprint_refs.py search. Queries included finite field internal, direct image finiteness, ordinary direct image, closed exceptional, closed support constructible, flat constructible, finite filtration, locally constant Hom, locally constant finite-dimensional, and discrete condensed. The broad queries supplied candidate nodes that I read; the narrow queries returned no equivalent blueprint statement. All new ids were absent before creation. The item has the existing ancestor lem-sfb-dc-hom-preserves, at its finite-coefficient finiteness sentence after the mod-varpi display; each new node records that exact place, via this item, and same_as is empty.

lem-sfb-finite-field-proetale-direct-image vs thm-dg-finite-type-constructibility: the existing result is ordinary etale finiteness; the new result is on the pro-etale site and proves the transfer through etale origin and bounded-below qcqs comparison.
lem-sfb-finite-field-proetale-direct-image vs sk-thm-pe-direct-image-comparison: the existing statement is a comparison isomorphism for discrete coefficients and bounded-below classical input, with no finiteness conclusion; the new lemma supplies bounded constructibility using that comparison.
lem-sfb-finite-field-proetale-direct-image vs lem-per-proper-finite-coefficient-bounded-preservation: the existing result is etale and proper; the new result applies to nonproper finite-type maps with invertible finite-field coefficients on pro-etale sites.
lem-sfb-finite-field-proetale-direct-image vs det-prop-scalar-six-direct-image: the existing result is a coefficient-change comparison on finite-Tor objects; the new lemma is ordinary direct-image finiteness without a coefficient change or finite-Tor input hypothesis.
lem-sfb-finite-field-closed-support vs lem-exc-proetale-closed-support: the existing statement constructs the ambient right adjoint with no constructibility assertion; the new lemma proves preservation of bounded constructibility.
lem-sfb-finite-field-closed-support vs lem-exc-proetale-support-triangle: the existing statement supplies only the ambient triangle, explicitly without constructibility of the exceptional inverse image; the new lemma proves its bounded constructibility via the open complement.
lem-sfb-finite-field-closed-support vs lem-sfb-rational-closed-support-constructible: the existing result concerns rational coefficient categories; the new lemma concerns ordinary finite constant field coefficients.
lem-sfb-finite-field-closed-support vs sk-prop-sf-rf-shriek-preservation: the existing functor is the right adjoint on a localizing subcategory and has a finite-Tor conclusion; the new lemma is for the ambient uncompleted closed right adjoint, proved independently by its support triangle. The former also has a dependency path back to this item and is not cited.
lem-sfb-finite-field-stratified-generation vs det-sf-flat-model-generation: clauses (1)-(2) of the existing statement concern flat sheaves; clause (3) allows direct summands and assumes finite Tor amplitude. The new lemma gives an explicit finite construction of every cohomologically bounded constructible finite-field complex without such an input hypothesis or direct summands, by field flatness, sheaf filtration, then truncation.
lem-sfb-finite-field-stratified-generation vs lem-fin-constructible-devissage: the existing result filters a single etale sheaf; the new lemma concerns bounded complexes on the pro-etale site and includes the finite truncation tower.
lem-sfb-finite-field-lisse-internal-hom vs lem-sfb-ringed-site-perfect-duality: the existing statement gives a perfect dual and evaluation isomorphism on any ringed site but no interval or constructibility assertion for arbitrary constructible N; the new lemma computes the cohomology and its finite models explicitly.
lem-sfb-finite-field-lisse-internal-hom vs lem-sfb-lisse-split-hom-flat-constructible: the existing result is underived sheaf Hom on an etale site with flat constructible second input; the new statement is ambient derived Hom on the pro-etale site with a bounded complex as second input.
lem-sfb-finite-field-lisse-internal-hom vs lem-sf-hom-finite-projective: the existing result has the fixed geometric finite-field datum and ctf coefficient conventions; the new result works on any Noetherian scheme with an ordinary finite constant field and proves a uniform cohomological interval.
lem-sfb-finite-field-lisse-internal-hom vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement gives restriction, shift and triangle identities with no boundedness or finite-generation conclusion; the new lemma uses it for a finite local system and proves bounded constructibility.
lem-sfb-finite-field-lisse-internal-hom vs lem-sfb-finite-field-internal-hom-finiteness: the new result treats a degree-zero locally constant first input and supplies a cohomology formula and unchanged interval. The item has an arbitrary bounded constructible first input; its proof still needs the support, direct-image and finite-filtration arguments.

## Mathlib searches

I read all sixteen retained searches.jsonl records and the actual hits stored with them before reusing them. Each of the four unchanged new statements has leanfinder, loogle, grep and leansearch records from 2026-10-21, with exactly the command's query text and results. The leanfinder and leansearch queries use different phrasings; no service was unavailable. I did not rerun unchanged search questions or invent a search record.

The direct-image hits give etale sites, constructible subsets and underived pushforward; they do not assert derived pro-etale bounded-constructible finiteness. Closed-support hits give geometric closed immersions, ideal local cohomology or ordinary adjunctions, without this constructibility assertion. Generation hits give bounded representatives and condensed locally constant objects, without finite stratified generation. Local-system Hom hits give vector-space dualTensorHomEquiv, sheafHom and condensed closed structures, without the ringed-site derived formula and constructibility conclusion. None states a whole new lemma or specializes to it in one line. The original item's recorded searches are also retained.

## Review by Q54

I read the chapter and restricted-functor unit, the current ancestor and the item's source interpretation. I compared the retained item to the current read-only repository: before this retry only proof, proof_deps and split_report differed; its statement and all maintainer-owned fields agree. I read Bhatt--Scholze Lemmas 5.4.3, 6.3.3, 6.3.9, 6.7.2, 6.7.11 and 6.7.13, together with Theorem 6.7.1, in the retained extracted text. At R=A, m=0 completion does not change finite constant coefficients. The arbitrary-field direct-image theorem is the existing etale finiteness input, followed by the bounded-below qcqs comparison; there is no inference from absolute Galois cohomological dimension. The source route is preserved.

For step 1 I opened lem-sf-module-object-ordinary-coefficient-equivalence: its statement gives the pulled-back coefficient isomorphism, exact derived equivalence and identification of finite constant models. I opened lem-sfb-module-object-ringed-site-derived-comparison: it states the actual ambient internal-Hom comparison for all derived objects. Over a field finite presentation equals finite dimension by a finite basis. These citations supply the comparison rather than merely defining the two categories.

For step 2 I opened the finite-type-over-Noetherian, Noetherian-open-subscheme, immersion-base-change-lft and locally-Noetherian-quasi-separated nodes. Their statements provide exactly Noetherianity, quasi-compactness of open strata, local finite type of immersions and quasi-separatedness. Closed immersions are quasi-compact because inverse images of affine opens are closed affine subschemes; composing finite generating sets on affine charts checks finite type. Hence the stratum, closure and open complements satisfy the qcqs/finite-type assumptions needed later. No scheme factorization is inferred from set-theoretic containment.

For step 3 I read the entire new generation statement: it gives an actual finite construction with the open-then-closed convention and finite local systems. It does not require a finite-Tor input or direct summands. That is the non-elementary tool the step applies, not a restatement of Hom finiteness.

For step 4 I opened the open/closed internal-Hom formula node: it states the two ambient adjunction identities with exact closed direct image and total derived open direct image. Applying them first to g and then j yields the displayed g_* Rj_* formula. Under the exact coefficient equivalence in step 1 the right adjoints are identified by their defining Hom bijections. I checked that all complements are quasi-compact by step 2. The new closed-support lemma supplies bounded constructibility before restriction. The exact site-pullback statement explicitly preserves kernels, cokernels and short exact sequences of abelian sheaves; the module action on those objects is induced, so constant-coefficient restriction is exact too. The exact-functor cohomology node explicitly gives H^r F(K)=F H^r(K). The constant-model pullback node supplies the base-changed strata, covers and same finite models for an admissible finite ell-primary ring on qcqs schemes. The new local-system Hom lemma now applies to that bounded second input. Finally the new direct-image lemma applies to finite-type j and g. Thus every substantive step is a cited statement; the earlier exactness citation gap is repaired.

For step 5 I opened the ringed-Hom exact-restriction node: it expressly has the contravariant triangle and opposite-shift clauses. The bounded-constructible triangulated-subcategory statement supplies zero, shift, isomorphism and extension closure with the same intrinsic constructibility convention. Induct over the specified finite construction: the base is zero and the generators computed in step 4; shifts reverse their sign under Hom; an extension gives a triangle whose endpoint Hom objects are already constructible. This proves both bounds and constructibility, and step 1 returns them to the original category.

For each new node I checked B1--B9: all objects and coefficient/site conventions are introduced, notions cite their defining nodes, source places and blueprint provenance are explicit, searches are logged, and status is unsplit with no proof content. The direct-image statement agrees with the finite-field case of 6.7.2 via 5.4.3 and the existing etale theorem, on finite-type schemes over any field with ell invertible. The closed-support statement is the closed case of 6.7.11 and uses its ambient right adjoint, whose existing node explicitly does not assume constructibility. The generation statement makes the finite filtration/truncation argument underlying 6.3.3 and 6.3.9 precise; the existing flat-model-generation node gives the sheaf part, whereas the new node supplies the bounded-complex finite tower. The local-system statement is the local finite-free calculation used in 6.7.13: it concerns internal sheaf Hom, not global sections, and includes a natural cohomology formula. None simply restates either conclusion of the full item.

I tested empty schemes, zero inputs/local ranks, identity and empty immersions, a one-degree complex shifted by r, and varying local ranks on disconnected schemes. The generation tower uses H^r(P)[-r], and needs only finitely many cohomology degrees. The local-system Hom keeps the second input's interval regardless of rank. On Spec k with unbounded absolute ell-cohomological dimension this is an internal sheaf calculation and makes no bounded-global-sections claim. The p=ell case is excluded exactly where direct-image finiteness needs it. A sheaf on closed support need not be locally free on X; the generation node only uses local freeness on strata.

I refreshed whole-DAG/blueprint duplicate searches and read the retained candidates before keeping the four nodes. Their statements did not change, so the recorded Mathlib queries remain applicable. I checked that each citation quote is verbatim in the current cited statement, proof_deps is exactly the union of uses, and the new nodes have no proof dependencies or path back to this item. The item proof is below 3000 characters and each step below 2000. The signed repair follows the current statement-only route note, resolving the older packet's incorrect proof-bearing interpretation.

## Extracted argument notes for later workers

These are the retained proposed arguments from the prior packet, provided for continuity. The four new JSON nodes are statement-only and are not claimed split by this delivery. The new workers must audit these notes against their sources and dependencies when splitting their own nodes.

### lem-sfb-finite-field-closed-support

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.7.11, closed-immersion support-triangle proof, specialized to R=A and m=0.

1. The scheme $T$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. Its open complement $h:W\hookrightarrow T$ is Noetherian and quasi-compact by [lem-weil-pbc-noetherian-open-subscheme-noetherian]; applying that assertion inside affine opens makes $h$ quasi-compact as a morphism. By [lem-weil-pbc-qc-open-immersion-finite-type] it is finite type. Thus $W$ is finite type over $k$: on affine charts combine the finite algebra generators of the two maps.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-noetherian-open-subscheme-noetherian, lem-weil-pbc-qc-open-immersion-finite-type.

2. Ordinary pullback by $v=h$ or $v=g$ preserves $\mathcal B_A$. Indeed [prop-weil-pbc-proetale-constant-exact] and [lem-weil-pbc-exact-functor-complex-cohomology] give $H^r(v^*M)=v^*H^r(M)$, preserving its vanishing interval. [lem-sfb-pullback-constant-model-constructible] pulls back the finite stratification and its finite constant local models (finite-dimensional modules over the field $A$). All bases are Noetherian and hence qcqs by [lem-weil-pbc-locally-noetherian-quasi-separated]. Apply [lem-sfb-finite-field-proetale-direct-image] to $h$ to get $Rh_*h^*M\in\mathcal B_A(T)$.

Uses: prop-weil-pbc-proetale-constant-exact, lem-weil-pbc-exact-functor-complex-cohomology, lem-sfb-pullback-constant-model-constructible, lem-weil-pbc-locally-noetherian-quasi-separated, lem-sfb-finite-field-proetale-direct-image.

3. For $M\in\mathcal B_A(T)$, [lem-exc-proetale-support-triangle] gives $g_*Rg^!M\to M\to Rh_*h^*M\to g_*Rg^!M[1]$. Its last two unshifted terms are in $\mathcal B_A(T)$, so the triangle closure of [lem-weil-proetale-dbc-triangulated] puts the first there. Finally [lem-weil-pbc-proetale-ringed-open-closed] gives exact $g_*$ and $g^*g_*\cong\mathrm{id}$. The pullback calculation of step 2 gives $Rg^!M\cong g^*g_*Rg^!M\in\mathcal B_A(Z)$.

Uses: lem-exc-proetale-support-triangle, lem-weil-proetale-dbc-triangulated, lem-weil-pbc-proetale-ringed-open-closed.

### lem-sfb-finite-field-lisse-internal-hom

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.7.13, local-system case of the finite-coefficient computation, using the ringed-site perfect-dual formula.

1. The object $L[0]$ is perfect: on a trivializing cover it is $A^d[0]$. [lem-sfb-ringed-site-perfect-duality] identifies $R\mathcal Hom(L,N)$ with $L^\vee\otimes^{\mathbf L}N$; the derived dual is the ordinary degree-zero dual since on that cover Hom from $A^d$ is the exact functor of taking $d$ copies. Slice restriction of derived Hom is allowed by [lem-weil-pbc-ringed-internal-hom-exact-restriction], so these are comparisons of the ambient Hom, not restrictions along a closed stratum. The ordinary dual is locally $(A^d)^\vee$.

Uses: lem-sfb-ringed-site-perfect-duality, lem-weil-pbc-ringed-internal-hom-exact-restriction.

2. The sheaf $L^\vee$ is flat by [lem-exc-constant-field-module-flat]. Hence its degree-zero complex is K-flat: tensor sends an acyclic complex to an acyclic complex, by exactness. Apply [lem-exc-constant-field-sheaf-tensor-cohomology] to any representative of $N$ to obtain $H^rR\mathcal Hom(L,N)\cong L^\vee\otimes H^r(N)$. This also proves the uniform vanishing outside $[a,b]$, regardless of the ranks of $L$.

Uses: lem-exc-constant-field-module-flat, lem-exc-constant-field-sheaf-tensor-cohomology.

3. For each $r$, take the finite stratification witnessing constructibility of $H^r(N)$. On a stratum $i:S_c\to S$, [lem-exc-proetale-pullback-locally-constant] pulls the local models of $L$ back to $S_c$. Locally there $L^\vee$ is the constant dual vector space; this identification is the evaluation map and is checked on the pulled-back basis. Refine its cover with one trivializing $H^r(N)|_{S_c}$. Ordinary tensor commutes with inverse image by its defining bilinear universal property, so $(L^\vee\otimes H^rN)|_{S_c}$ has the constant value $V^\vee\otimes_A W$ on this common cover. It is finite-dimensional. The same finite stratification proves the required constructibility. Ranks zero and zero cohomology give the zero sheaf.

Uses: lem-exc-proetale-pullback-locally-constant.

### lem-sfb-finite-field-proetale-direct-image

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.7.2, finite-field specialization, with Lemma 5.4.3 and Theorem 6.7.1; expanded using the existing arbitrary-field étale finiteness node.

1. The field $k$ is Noetherian (its only ideals are $0,k$). Thus $T,V$ are Noetherian by [lem-weil-pbc-finite-type-over-noetherian] and quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. Their quasi-compactness and [lem-weil-pbc-qcqs-morphism-permanence] make $f$ qcqs. The image of $\ell$ is a nonzero field element of $k$, hence invertible.

Uses: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-weil-pbc-qcqs-morphism-permanence.

2. For $C\in\mathcal B_A(T)$, [lem-weil-pbc-finite-ring-constructible-derived-origin] gives a bounded constructible étale complex $C_0$ and $C\cong\nu_T^*C_0$. Since $\ell A=0$ and $\ell$ is invertible in $k$, [thm-dg-finite-type-constructibility] gives $Rf_{\mathrm{ét},*}C_0\in D^b_c(V_{\mathrm{ét}},A)$.

Uses: lem-weil-pbc-finite-ring-constructible-derived-origin, thm-dg-finite-type-constructibility.

3. Apply [sk-thm-pe-direct-image-comparison] to the qcqs map $f$ and bounded-below $C_0$ to obtain $Rf_{\mathrm{proét},*}C\cong\nu_V^*Rf_{\mathrm{ét},*}C_0$. The constructible equivalence and interval preservation of [lem-weil-pbc-finite-ring-constructible-derived-origin] put the right side in $\mathcal B_A(V)$. This uses no bound for the absolute Galois cohomology of $k$.

Uses: sk-thm-pe-direct-image-comparison, lem-weil-pbc-finite-ring-constructible-derived-origin.

### lem-sfb-finite-field-stratified-generation

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemmas 6.3.3 and 6.3.9, finite stratified dévissage in the proof of Lemma 6.7.13; degree-zero sheaf filtrations followed by the finite truncation tower.

1. By [lem-exc-constant-field-module-flat] every $A_X$-module sheaf is flat. Apply clauses (1)–(2) of [det-sf-flat-model-generation] to each constructible sheaf $F$: $X$ is Noetherian and $A$ is finite. They give a finite sheaf filtration with subquotients $g_*j_!L$ in exactly the stated open-then-closed convention. Finite projective $A$-modules are finite-dimensional vector spaces. Each short exact extension, placed in degree zero, is a distinguished triangle by [lem-weil-pbc-complex-ses-triangle]. Thus each $F[0]$ has the asserted finite construction.

Uses: lem-exc-constant-field-module-flat, det-sf-flat-model-generation, lem-weil-pbc-complex-ses-triangle.

2. Choose $u\le v$ with $H^r(P)=0$ outside $[u,v]$. In [lem-pc-derived-lower-truncation-step-triangle] put $n=-r$ to obtain $H^r(P)[-r]\to\tau_{\ge r}P\to\tau_{\ge r+1}P\to H^r(P)[-r+1]$. Start at $\tau_{\ge v+1}P\cong0$ and run $r=v,v-1,\ldots,u$. At each step the first object was constructed from the sheaf filtration in step 1 and the third in the preceding step, so the middle is a permitted extension. The final object $\tau_{\ge u}P$ is isomorphic to $P$. There are finitely many degrees and each sheaf filtration is finite, proving finiteness of the construction. For zero $P$ or empty $X$ the empty construction suffices.

Uses: lem-pc-derived-lower-truncation-step-triangle.

## Validation

Initial dry run of this retry reproduced four new-node status errors (split instead of unsplit); nothing was pushed. All four are repaired as described above. After repair, the prescribed final dry run exited 0: `OK (not pushed) deliver/Q54/lem-sfb-finite-field-internal-hom-finiteness at 74eeced001b: preflight passed`. It included the server DAG and split checks. The initial invocation had already exited before this final invocation began. Direct delivery follows under the explicit direct-delivery brief; no separate reader is requested by that brief.
