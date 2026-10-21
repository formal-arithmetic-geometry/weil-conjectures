## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-hom-dual-constructible-models.json: item, unchanged statement; five assembly steps, 1814 characters of proof text.
- dag/nodes/sec-six-functors-basics/lem-sfb-admissible-scalar-realization-exact.json: statement, unsplit; Mathlib searches found component results only.
- dag/nodes/sec-six-functors-basics/lem-sfb-scalar-perfect-dual-realization.json: statement, unsplit; Mathlib searches found component results only.
- citations.json: one verbatim statement quotation per step/dependency pair.
- searches.jsonl: actual msearch.py queries and results, retained verbatim.

Attachments: none. The project theorem AlgebraicGeometry.ProEtale.InternalHomDualModels.internalHomDual_constructible_models, lean/Sheaf/Paper/InternalHomDualConstructibleModels.lean:321, ends with sorry. Its ten-step docstring agrees with the returned proof. The existing scalarDual data and ancillary additive instances cover no complete new theorem. Searches of lean/WeilConjectures/ by the item tag and scalar-exact/dual-realization concepts found no completed declaration of this item or either new statement. No Lean was written or compiled.

WANTED: none. All source documents used are present.

The sandbox initially contained only dispatcher brief markers, with no node files, report, citations or search log. Accordingly I copied the current live item, retaining all its metadata and statement. There was no existing split/report to dry-run first. The live item is deliberately reopened by the human; its previously reviewed status and stage-2 declaration do not supersede this re-split. Delivery packaging rebases split-owned fields onto the current server tree.

## Repair of the return

The single returned point is fully addressed: this is a spread of work, not a shortened proof with unchanged dependencies. There are TWO new independently startable statement-only nodes, each with a self-contained theorem, source, blueprint place and real searches. Neither has proof steps or proof dependencies, and neither restates bounded constructibility or either cohomology formula of the item.

The old argument is partitioned as follows:
- New admissible-scalar-realization-exact: old steps 1, 3 and 4. This is the coefficient-dependent argument: Noetherian scalar rings, finite discrete comparison, field splitting, and completed-integral flatness, including exactness on slices. The old text assigned to it has approximately 2500 characters.
- New scalar-perfect-dual-realization: the non-restriction parts of old steps 5, 6 and 7. This is the ringed-site linear-algebra argument: realized finite-free retracts, exactness of internal Hom from those terms, bounded Hom invariance against the K-injective augmentation, and the natural scalar/sheaf dual isomorphism with its signed differential. The old text assigned to it has approximately 2600 characters. The global-to-slice RHom restriction remains in parent Step 3.
- Parent assembly Step 2 retains old step 2 (finite-projective scalar duals and finite-presentation cohomology); Step 4 retains old step 8 (both formulas on every original chart); Step 5 retains old steps 9--10 (finite refinement, common interval, empty case and descent), using existing nodes for the hard refinement/descent arguments.

All ten old proof steps are reproduced verbatim below as a handoff map. The new nodes' conclusions explicitly carry the comparisons and exactness facts which those arguments establish; their future workers receive the assigned proof arguments here, while the nodes themselves remain statement-only as requested. The parent statement is byte-for-byte unchanged. No target, unit or chapter statement is changed. No SGA source is used.

## Sources and searches

I read the current blueprint internal-Hom proof at literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-internal-hom.proof.md, paragraphs 2--3, together with the unit/chapter records and SETUP's three-level route. Its perfect dual and perfect-factor membership are exactly the places served here.

For the new coefficient node I read sites-modules.tex, Tag 093J, lemma-constant-exact, and Tag 093M, lemma-completion-flat (including their proofs), and the statements of the existing finite-discrete, DVR, completed-coefficient-identification and completed-flatness nodes. The field case is the existing split-sequence argument: choose a basis of the quotient, lift its vectors and extend linearly. Realization is additive, so it preserves the resulting direct-sum decomposition, regardless of whether the coefficient field sheaf is discrete. Finite rings and fields satisfy the ideal-finiteness definition directly. The DVR theorem gives principal ideals for O_E; Z_l is its base case. Completion-flatness applies because these integral rings are Noetherian and because the coefficient object is the actual inverse limit of constant finite quotients. Exact constant realization followed by flat extension proves exactness. Exact slice restriction then gives the stated slice conclusion.

For the new scalar-dual node I read sites-cohomology.tex, Tag 08JH, lemma-Rhom-strictly-perfect, and Tag 08JJ, lemma-dual-perfect-complex, especially the final strictly-perfect/retract calculation, and the explicit signed-Hom definition. The statement is the scalar-realization refinement of that calculation. Finite-projective splittings survive under constant sheafification and tensoring. Finite-free internal Hom is exact; the natural idempotent splits each exact sequence into image and complementary image sequences, proving exactness of the retract Hom. The existing bounded-exact-term-Hom lemma therefore applies to the K-injective augmentation. The map beta_V has its free inverse by coordinates, and naturality identifies the idempotent on both sides, giving its retract inverse. Its degreewise naturality commutes with -(-1)^q precomposition by d_F, giving precisely the written chain isomorphism. This does not assume global projectivity of module sheaves or scalar flatness.

Before naming nodes I searched the whole DAG by scalar exactness, scalar/dual realization and Tags 093J, 093M, 08JH, 08JJ, and read the matching statements. I ran blueprint_refs.py ancestor on the item and searches 'scalar exact', 'dual perfect', 'constant scalar', 'scalar dual', 'completion flat', 'admissible scalar realization', and 'perfect dual realization'. The only broad phrase hit, sk-def-sfb-derived-categories, is a derived-category definition and states neither theorem. The nearest ancestor is det-thm-sf-ctf-stability-internal-hom, with the item in via. No equivalent blueprint statement was found. The detailed same-tag distinctions follow below.

All new-node Mathlib entries are copied from actual msearch.py calls. Each node has LeanSearch, LeanFinder, Loogle and source grep searches, and a second semantic phrasing. One early Loogle query returned an unknown identifier; I retained that result and also ran the valid ModuleCat.preservesFiniteLimits_extendScalars_of_flat query. The valid result assumes ordinary module flatness; it does not construct the pro-etale coefficient sheaf or prove the six cases. I read Mathlib/Algebra/Category/ModuleCat/Descent.lean:42 and Mathlib/LinearAlgebra/Dual/BaseChange.lean (the baseChange formula and finite-free IsBaseChange construction). Ordinary module dual base change and Module.dual_projective have neither a sheafification comparison nor a derived internal-sheaf Hom assertion. Thus neither complete new node is an exact match or a one-line specialization. There are zero Mathlib leaves. No unavailable service was recorded as a negative search.

## Review by Q94

I checked the returned point by tracing every old argument to the two new obligations or an explicit assembly step, rather than just deleting text. The two extracted workloads are comparable and mathematically independent: coefficient exactness requires no dual calculation, and scalar-dual realization requires no Noetherianity or flatness. The proof text is below 3000 characters; every step is below 2000. The unchanged statement still includes all six coefficient cases, both original-cover formulas, finite presentation, global bounds and both Dbc memberships.

Step 1 uses precisely lem-sfb-admissible-scalar-realization-exact: its statement provides Noetherianity, exact realization on all scalar modules and slices, and the completed coefficient identification. The scheme and coefficient hypotheses of that theorem are satisfied by the item. No exactness of arbitrary inverse limits is inferred.

Step 2 uses lem-sf-finite-projective-dual for finite projectivity of Hom_R(F^{-q},R), lem-pc-noetherian-finite-kernels-cokernels for the finite cycles and the cokernel G^{q-1} to Z^q(G), and lem-sc-noetherian-finite-module-finite-presentation for the final promotion. I opened all three statements; the latter requires only finite modules over a Noetherian ring, exactly Step 1's conclusion. Both source and target of the second cokernel application are finite. Boundedness of the scalar dual is immediate from its degree -q formula. We do not claim its cohomology is projective.

Step 3 uses the arbitrary-complex restriction clause of lem-weil-pbc-ringed-internal-hom-exact-restriction, which really states RHom(L,M)|_U = RHom(L|_U,M|_U), and the new scalar-perfect-dual-realization with R, the slice site, B|_U and F_i. Its hypotheses are exactly the given bounded finite-projective scalar model. The new statement explicitly specifies beta and the sign, so no comparison is borrowed from the proof of a definition node. The local model C_U is the restriction of the item’s coefficient realization.

Step 4 uses clause (c) of lem-sp-exact-functor-preserves-homology and exactness of j_U^* from lem-pur-site-restriction-module-adjunction-exact. Those statements were read in full. Apply (c) to the degree-(q-1,q,q+1) three-term piece, first under C_U and then under restriction. The result gives both formulas on every ORIGINAL U_i, not only on a finite refinement. Step 2 supplies finite presentation for each module in both formulas.

Step 5 uses lem-weil-pbc-finite-type-over-noetherian to obtain Noetherian S from the field, and lem-weil-pbc-locally-noetherian-quasi-separated for quasi-separatedness. The finite affine refinement theorem assumes exactly this Noetherian/quasi-separated situation and a finite affine open cover; it returns a finite pro-etale covering with maps through the old charts. I read its complete statement. The localization theorem lem-sfb-coefficient-sections-localization identifies the slice with V_proet and its coefficient ring with Lambda_V for ANY condensed ring, preserving scalar sections along maps. Exact slice restriction carries the finite-free-summand models and the signed dual models to these charts. The minimum/maximum give a common bound, and lem-sfb-local-model-cohomology-descent explicitly gives global bounds, cohomology formulas, constructibility on the single stratum and Dbc membership, assuming exact scalar realization and finite presentation. All those hypotheses have been supplied. I opened each cited statement and placed its verbatim text in citations.json.

I corrected one citation-level coefficient mismatch while preserving the statement and argument: sk-prop-sfb-cartesian-coefficients explicitly fixes the older finite-subextension-valued Qbar coefficient, whereas this item's live statement and Lean use the continuous-function condensed ring. The arbitrary-condensed localization theorem supplies the needed coefficient/slice identification without that mismatch. It is an off-unit generic tool and is declared in split_report.tool_uses for the maintainer to judge; the other retained generic refinement/descent/restriction uses keep their earlier justifications. No existing node was edited except the assigned item.

Small cases: for the coefficient theorem a zero finite ring gives the zero module functor, still exact, and an empty scheme gives zero sheaves. No characteristic or regularity restriction was added. Field sequences split even in infinite dimension; only finite biproduct preservation is used after obtaining the section. For the scalar-dual theorem F=0 and a rank-zero summand give zero comparisons; a module in a single arbitrary positive or negative degree gives the reversed degree and the stated -(-1)^q sign. The direct summand need not be free. No flatness of B is used in the dual theorem. For the parent, A=F_l[epsilon]/(epsilon^2) with multiplication-by-epsilon differentials illustrates why finite presentation rather than projectivity of cohomology is required. The empty scheme is handled separately, and nonempty finite covering families allow min/max; different chart supports are allowed and zero chart complexes can be padded. These checks exclude hidden uniform-bound, discrete-coefficient and regularity assumptions.

Against delivery-errors B--E: new statements introduce their objects and cite notions, carry no proof or proof dependencies, and use single-escaped TeX; searches are real and nonmatches distinguished from component matches. Same-tag candidates were opened and distinguished, including the more general ringed-site duality nodes. Every non-elementary assembly fact is a cited statement, quotes are verbatim, and definitions are not substituted for missing theorems. There is no dependency from either new statement to the item or to its constructibility conclusion. The sources are the permitted blueprint/Stacks route. No new node is elementary, a constructibility clause of the parent, or the whole parent relabelled. Outstanding work consists exactly of the two unsplit proof obligations and their existing prerequisites; delivery checks are run by the required server tool.

## Not duplicates

lem-sfb-admissible-scalar-realization-exact vs def-sfb-quotient-kernel-completeness: existing node defines a derived completeness predicate; new theorem proves scalar Noetherianity and exactness, with no completeness predicate.

lem-sfb-admissible-scalar-realization-exact vs def-weil-pbc-completed-constant-realization-data: existing node defines interfaces requiring exactness on finite completion modules as data; new theorem proves the actual exactness and scalar Noetherianity, including nonintegral cases, with no such data assumption.

lem-sfb-admissible-scalar-realization-exact vs def-weil-pbc-derived-normalization-arrows: existing node defines normalization arrows for discrete constant realization and coefficient restriction; it does not prove exact extension to continuous/completed coefficients.

lem-sfb-admissible-scalar-realization-exact vs lem-cbc-finite-extension-reduction-cone-bound: existing theorem is the uniformizer cone and cohomology interval for finite reductions of an integral derived object; new theorem gives scalar Noetherianity and exact ordinary coefficient realization without a derived input.

lem-sfb-admissible-scalar-realization-exact vs lem-pod-completed-integral-scalar-regular: existing theorem gives injectivity of uniformizer multiplication on completed coefficient sections; new theorem gives all-module exact realization and includes finite and field coefficients.

lem-sfb-admissible-scalar-realization-exact vs lem-pod-point-principal-reduction-coefficients: existing theorem gives a specific short exact uniformizer sequence at a field point; new theorem gives exact realization of EVERY scalar short exact sequence on any scheme for all six coefficients.

lem-sfb-admissible-scalar-realization-exact vs lem-pod-point-reduction-coefficient-ring: existing theorem describes a DVR quotient map and its principal kernel in scalar coordinates; new theorem concerns coefficient sheaf realization exactness and Noetherianity for all admissible types.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-adic-perfect-model-complete-reduction: existing statement gives derived completeness and residue reduction for a scalar perfect complex over a specified completion; new theorem gives scalar Noetherianity and all-module exact realization for the actual six coefficient sheaves, with no derived completeness claim.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-constant-realization-derived-scalar-extension: existing theorem compares DISCRETE constant realization with algebraic derived scalar extension; new theorem asserts underived exactness for actual continuous/completed coefficient sheaves, not a derived base-change comparison.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-constant-realization-reflects-isomorphism: existing theorem is conservativity and homology for discrete constant realization on nonempty objects, not exactness of extension to all six pulled-back coefficient sheaves.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-constant-realization-reflects-isomorphism-general: existing theorem is conservativity/perfectness reflection under a nondegenerate topology; new theorem asserts exact ordinary realization with specified continuous/completed coefficients and scalar Noetherianity, with no nondegeneracy assumption.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-constant-to-continuous-scalar-flat: existing theorem gives flatness on the POINT for a topological PID, with no claim that its scheme pullback has the required scalar realization or that all six scalar rings are Noetherian; new theorem supplies those scheme/slice cases including finite rings not PIDs. It is reusable as a component, not a theorem of the whole new statement.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-finite-constant-model-two-term-free-resolution: existing theorem constructs finite free resolutions of finitely presented integral/rational scalar local models; new theorem is exactness on arbitrary scalar modules for all six coefficient types, including singular finite rings.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-integral-quotient-direct-image-comparison: existing theorem is a quotient-scalar/direct-image mate isomorphism; new theorem concerns coefficient realization exactness before any pushforward or derived reduction.

lem-sfb-admissible-scalar-realization-exact vs lem-sfb-local-integral-perfect-model-cohomology: existing theorem is an integral perfect-model cohomology formula for a locally closed immersion; new theorem concerns all scalar modules and all six coefficients, their exact realization and scalar Noetherianity, with no cohomology or constructibility conclusion.

lem-sfb-admissible-scalar-realization-exact vs lem-sp-constant-inverse-image-section: existing theorem describes transport of sections and quotient-kernel membership; new theorem gives exactness and scalar Noetherianity, not a section-transport identity.

lem-sfb-admissible-scalar-realization-exact vs lem-sp-constant-pullback-scalar: existing theorem describes transport of multiplication by a scalar under a supplied inverse-image datum; new theorem proves exact realization in the actual admissible coefficients.

lem-sfb-admissible-scalar-realization-exact vs lem-trf-point-reduction-unit-normalization: existing theorem normalizes point finite-reduction comparison units for integral and quotient coefficients; new theorem proves exact ordinary realization for all scalar modules in six coefficient cases on arbitrary schemes, with no point sections or reduction-unit comparison.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-finite-free-completed-scalar-comparison: existing theorem compares derived integral scalar extension with a completed tower for derived-complete objects under a finite extension of coefficient fields; new theorem gives ordinary scalar realization exactness for arbitrary modules and all coefficient types.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-completed-constant-algebra-flat-quotients: existing theorem transports flatness/quotients between presentations of a specified completion, assuming Noetherianity; new theorem supplies the admissible scalar rings and exact realization in all coefficient cases without a supplied completion presentation.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-completed-constant-module-model: existing theorem assumes a completion scalar map and concludes exactness only on finite completion modules plus adic lissity; new theorem gives exactness on ALL scalar modules for all six admissible coefficients and scalar Noetherianity.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-completed-constant-sheaf-reduction: existing theorem proves flatness and reduction for a specified inverse-limit ring sheaf, assuming a Noetherian scalar ring; new theorem identifies the actual admissible coefficient realizations, proves Noetherianity, and covers finite and continuous field coefficients too. It is the integral component used in the assigned old argument.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-constant-completion-equivalence: existing theorem assumes a Noetherian scalar ring and studies a specified completion and derived-complete subcategories; new theorem establishes Noetherianity and ordinary exact realization for finite, integral and field admissible coefficients without a derived-completeness condition.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-constant-module-section-properties: existing theorem concerns sections of DISCRETE constant modules and assumes a Noetherian ring; new theorem concerns extension to the actual continuous/completed coefficient sheaf and establishes scalar Noetherianity.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: existing theorem gives a strict finite-projective tower comparison and cone over an adic coefficient datum; new theorem concerns degree-zero ordinary scalar realization on all modules, including field and finite-ring cases.

lem-sfb-admissible-scalar-realization-exact vs lem-weil-pbc-locally-constant-finite-values-finite-type: existing theorem proves finite type from etale locally constant finite scalar modules, not exactness of pro-etale continuous coefficient realization on all modules.

lem-sfb-scalar-perfect-dual-realization vs lem-fix-site-perfect-scalar-hom: existing theorem compares derived Hom across a map of ring SHEAVES for a site-perfect first variable; it has no ordinary scalar module to constant-sheaf comparison or signed scalar-dual chain identification. That comparison cannot be obtained by a one-line substitution.

lem-sfb-scalar-perfect-dual-realization vs lem-pur-completed-line-complete: existing statement proves derived completeness of a completed coefficient line; the new theorem computes scalar-realized internal duals on general ringed sites with no completeness conclusion.

lem-sfb-scalar-perfect-dual-realization vs lem-sf-etale-local-dual-interval: the existing theorem assumes finite constant coefficients on an etale site with common interval and a twisted line; the new theorem is the scalar-to-sheaf beta comparison on any ringed site and arbitrary constant-scalar algebra, without a field or finite-ring hypothesis.

lem-sfb-scalar-perfect-dual-realization vs lem-sfb-ringed-site-perfect-duality: existing perfect duality states biduality and derived tensor-Hom evaluation, but does not identify the ordinary scalar dual after constant sheafification and B-extension, or specify beta_V and its signed chain comparison.

lem-sfb-scalar-perfect-dual-realization vs lem-sfb-ringed-site-strict-perfect-hom: existing theorem starts with a sheaf-module complex and states ordinary Hom/bidual/evaluation calculations; it does not compare the scalar dual before constant realization with the sheaf dual after realization. Its ordinary-Hom subresult is reusable when this new scalar comparison is later proved.

lem-sfb-scalar-perfect-dual-realization vs lem-weil-pbc-condensed-finite-free-tensor-exact: existing theorem is exactness of tensor from a locally finite-free internal module, not exactness of internal Hom and the scalar-dual beta chain comparison.

lem-sfb-scalar-perfect-dual-realization vs lem-weil-pbc-condensed-internal-hom-sections: existing statement identifies sections of internal Hom with module morphisms, without computing finite-projective scalar dual realization or its signed complex.

lem-sfb-scalar-perfect-dual-realization vs lem-weil-pbc-derived-coyoneda-evaluation: existing theorem is about external derived Hom groups and homology of a right-derived additive Hom functor, not the sheaf internal dual of a realized scalar perfect complex.

lem-sfb-scalar-perfect-dual-realization vs lem-weil-pbc-ringed-site-locally-free-derived-hom: existing theorem is a hypercohomology formula for derived morphism groups from a degree-zero locally free sheaf with bounded-below target; new theorem is an internal-sheaf complex comparison for a bounded scalar complex.

The two new nodes are also distinct from the parent: one has no derived input, dual or constructibility conclusion; the other works over an arbitrary scalar algebra on a ringed site, assuming no Noetherianity and asserting no finite scalar cohomology or global constructibility. Neither repeats a clause of the item.

## Preserved old argument and assignment

### Old step 1 — lem-sfb-admissible-scalar-realization-exact

The scalar ring $R$ is Noetherian. For finite $A$, every ideal is generated by its finite underlying set; for a field, an ideal is either zero or generated by $1$. For $R=\mathcal O_E$, [lem-weil-l-adic-extension-integers-dvr](2) says every ideal is principal; $R=\mathbf Z_\ell$ is the case $E=\mathbf Q_\ell$, with its valuation ring identified in [def-weil-l-adic-numbers]. These statements give the ideal-finiteness definition [def-weil-pbc-noetherian-ring] in every admissible scalar case, including $\overline{\mathbf Q}_\ell$.

Cited nodes: lem-weil-l-adic-extension-integers-dvr, def-weil-l-adic-numbers, def-weil-pbc-noetherian-ring.

### Old step 2 — parent assembly

By [lem-sf-finite-projective-dual], each $\operatorname{Hom}_R(F_i^{-q},R)$ is finite projective. Thus $F_i^{\vee,\bullet}$ is bounded, in $[-b_i,-a_i]$ if $F_i$ is supported in $[a_i,b_i]$. For either scalar complex $G=F_i$ or $F_i^\vee$, apply [lem-pc-noetherian-finite-kernels-cokernels] to $d^q:G^q\to G^{q+1}$ to see that $Z^q(G)$ is finite. Apply its cokernel clause to $G^{q-1}\to Z^q(G)$ to see that $H^q(G)$ is finite. Step 1 and [lem-sc-noetherian-finite-module-finite-presentation] make it finitely presented. This does not assert that cohomology is projective: finite coefficient rings need not be regular.

Cited nodes: lem-sf-finite-projective-dual, lem-pc-noetherian-finite-kernels-cokernels, lem-sc-noetherian-finite-module-finite-presentation.

### Old step 3 — lem-sfb-admissible-scalar-realization-exact

On any scheme $T$, write $C_T(M)=\Lambda_T\otimes_{\underline R}\underline M$. For finite $A$, [lem-weil-pbc-finite-discrete-condensed-ring-constant] identifies its condensed ring with the constant ring on the point. The inverse image $p_T^*$ of [sk-def-sfb-pullback-from-point] preserves finite coproducts and the terminal object; thus it takes this finite constant ring to $\underline A$, including its operations. Hence $C_T$ is the exact constant module functor of [def-sfb-site-derived-constant-module-functor]. If $R$ is one of the field stages, every short exact sequence of $R$-vector spaces splits: choose a basis of the quotient using [lem-weil-pbc-vector-space-basis-through-vector], lift each basis vector, and extend linearly to a section. Applying $C_T$ preserves this splitting and the finite direct-sum decomposition. Hence $C_T$ is exact on scalar modules for every field stage, including the specified condensed $\overline{\mathbf Q}_\ell$. This argument does not identify $\Lambda_T$ with the discrete constant field sheaf.

Cited nodes: def-sfb-site-derived-constant-module-functor, lem-weil-pbc-finite-discrete-condensed-ring-constant, sk-def-sfb-pullback-from-point, lem-weil-pbc-vector-space-basis-through-vector.

### Old step 4 — lem-sfb-admissible-scalar-realization-exact

For $R=\mathcal O_E$, [det-prop-sfb-qlbar-colimit-x-integral-limit](3) identifies $\Lambda_T$ with $\varprojlim_n\underline{R/\pi_E^n}$. Apply [lem-weil-pbc-completed-constant-sheaf-reduction] with $A=R$ and $I=(\pi_E)$: its hypotheses hold by Step 1. It makes this completed sheaf flat over $\underline R$. Composing tensor with this flat sheaf with the exact constant module functor gives exactness of $C_T$. The same proof with $E=\mathbf Q_\ell$ handles $\mathbf Z_\ell$. Thus $C_T$ is exact in every coefficient case. This uses flatness of completion, not an assertion that inverse limits of arbitrary exact sequences are exact.

Cited nodes: det-prop-sfb-qlbar-colimit-x-integral-limit, lem-weil-pbc-completed-constant-sheaf-reduction, def-sfb-site-derived-constant-module-functor.

### Old step 5 — lem-sfb-scalar-perfect-dual-realization

Fix $i$ and put $E_i^\bullet=C_{U_i}(F_i^\bullet)$ and $B_i=B|_{U_i}$. The finite-projective splittings of [def-weil-pbc-strict-perfect-coefficient-package] remain splittings after constant realization and scalar extension: each $E_i^q$ is a direct summand of some $B_i^{N_q}$. By [lem-sc-finite-free-internal-hom-exact], $\mathcal Hom_{B_i}(B_i^{N_q},-)$ is exact. Its natural idempotent $h\mapsto h\circ(i_qp_q)$ has image $\mathcal Hom_{B_i}(E_i^q,-)$. An exact sequence with such a commuting idempotent is the direct sum of its image and complementary image sequences; equivalently, applying the idempotent to a local lift gives a lift in its image. Therefore the image sequence is exact too. This proves the termwise internal-Hom exactness needed in the next step.

Cited nodes: def-weil-pbc-strict-perfect-coefficient-package, lem-sc-finite-free-internal-hom-exact.

### Old step 6 — lem-sfb-scalar-perfect-dual-realization

By [lem-weil-pbc-ringed-internal-hom-exact-restriction], $P^\vee|_{U_i}\simeq R\mathcal Hom_{B_i}(E_i^\bullet,B_i)$. In the K-injective definition [def-pur-derived-internal-hom], choose $B_i[0]\to I_i^\bullet$. Step 5 verifies every hypothesis of [lem-pc-bounded-exact-term-hom-quasi-iso] for the bounded complex $E_i$: the map $\mathcal Hom^\bullet(E_i,B_i[0])\to\mathcal Hom^\bullet(E_i,I_i^\bullet)$ is a quasi-isomorphism. Consequently $P^\vee|_{U_i}$ is represented by the ordinary dual complex $\mathcal Hom^\bullet_{B_i}(E_i^\bullet,B_i[0])$. No global projectivity of module sheaves is being inferred from their finite-projective local splittings.

Cited nodes: lem-weil-pbc-ringed-internal-hom-exact-restriction, def-pur-derived-internal-hom, lem-pc-bounded-exact-term-hom-quasi-iso.

### Old step 7 — lem-sfb-scalar-perfect-dual-realization

For each finite projective $R$-module $V$, define $\beta_V:C_{U_i}(\operatorname{Hom}_R(V,R))\to\mathcal Hom_{B_i}(C_{U_i}(V),B_i)$ by $\beta_V(b\otimes\phi)(b'\otimes v)=bb'\phi(v)$. For $V=R^N$ it is the usual identification of both sides with $B_i^N$. For the splitting $V\xrightarrow{i}R^N\xrightarrow{p}V$, naturality carries precomposition with $ip$ on the free dual to the same idempotent on the sheaf dual; restricting the free isomorphism to the images gives an inverse for $\beta_V$. Thus $\beta_V$ is an isomorphism, natural in $V$. In degree $q$, apply it to $V=F_i^{-q}$. Both dual differentials send $\phi$ to $-(-1)^q\phi d_F$, by [def-pur-hom-complex], so naturality makes these degreewise isomorphisms a chain isomorphism. Step 6 therefore gives $P^\vee|_{U_i}\simeq C_{U_i}(F_i^{\vee,\bullet})$.

Cited nodes: def-weil-pbc-strict-perfect-coefficient-package, def-pur-hom-complex.

### Old step 8 — parent assembly

Apply [lem-sp-exact-functor-preserves-homology](c) to the exact functor $C_{U_i}$ of Steps 3--4, first for $F_i$ and then for $F_i^\vee$. Apply it also to exact slice restriction [lem-pur-site-restriction-module-adjunction-exact], so that taking $H^q$ commutes with restriction to $U_i$. The given model for $P$ and the model from Step 7 then give, on every original covering object and for every integer $q$,
$$H^q(P)|_{U_i}\cong C_{U_i}(H^q(F_i)),\qquad H^q(P^\vee)|_{U_i}\cong C_{U_i}(H^q(F_i^\vee)).$$
Step 2 supplies the required finite presentation of both scalar modules. In particular these are the original covering objects, not just the finite refinement used below.

Cited nodes: lem-sp-exact-functor-preserves-homology, lem-pur-site-restriction-module-adjunction-exact.

### Old step 9 — parent assembly

The field $k$ is Noetherian by the ideal argument of Step 1, so [lem-weil-pbc-finite-type-over-noetherian] makes $S$ Noetherian, in particular quasi-compact. It is quasi-separated by [lem-weil-pbc-locally-noetherian-quasi-separated]. Choose a finite affine open cover of $S$ by quasi-compactness and apply [lem-sfb-finite-affine-proetale-refinement] to the original covering. This gives a finite covering family $\{V_j\to S\}_{j=1}^n$, with each $V_j\to S$ factoring through some original $U_{i(j)}$. The coefficient identification and exact pullback of [sk-prop-sfb-cartesian-coefficients] restrict the two local models and their scalar formulas to this finite family. For $S=\varnothing$ both complexes and all their sheaves are zero, and the assertion follows with bound $[0,0]$; assume henceforth that $S$ is nonempty.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-locally-noetherian-quasi-separated, lem-sfb-finite-affine-proetale-refinement, sk-prop-sfb-cartesian-coefficients.

### Old step 10 — parent assembly

Choose intervals $[a_j,b_j]$ supporting $F_{i(j)}$ and put $a=\min_j a_j$, $b=\max_j b_j$, enlarging zero-complex intervals if necessary. On the finite cover, the models for $P$ are supported in $[a,b]$ and those for $P^\vee$ in $[-b,-a]$. Apply [lem-sfb-local-model-cohomology-descent] twice: exactness of its scalar functors was proved in Steps 3--4 and finite presentation in Step 2. It gives global cohomology bounds in these intervals and constructibility of every cohomology sheaf on the single stratum $S$. Equivalently, the original-cover formulas of Step 8 already give the finite constant local models required by [sk-def-sfb-constructible]; the finite cover supplies only the uniform bound. Thus both objects belong to $\Dbc(S,\Lambda)$, with the completed integral coefficient sheaf retained throughout.

Cited nodes: lem-sfb-local-model-cohomology-descent, sk-def-sfb-constructible.
