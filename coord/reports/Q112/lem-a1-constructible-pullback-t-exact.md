# Worker report

Repair of the human's 2026-10-21 re-split request, Q112, stage 1 only.

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-constructible-pullback-t-exact.json`: existing statement node; statement unchanged; four-step assembly, 2554 characters.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-integral-stratum-chart-restrictions.json`: new statement, status unsplit; no Mathlib match; empty proof, empty proof_deps, null proof_origin.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-completed-perfect-scalar-pullback.json`: new statement, status unsplit; no Mathlib match; empty proof, empty proof_deps, null proof_origin.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-texact-coefficient-stage-descent.json`: new statement, status unsplit; no Mathlib match; empty proof, empty proof_deps, null proof_origin.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-point-realization-standard-cohomology.json`: new statement, status unsplit; no Mathlib match; empty proof, empty proof_deps, null proof_origin.

- `report.md`: this report, including the full retained argument and its allocation below.
- `citations.json`: one entry per parent-step citation, copied verbatim from the cited statement.
- `searches.jsonl`: actual search-command log, with complete raw output retained in the node-specific search text files. Local scratch files are outside the delivery's node/report set.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag and by constructible pullback / t-exact terminology. The source theorem `Etale.DerivedCategory.boundedConstructible.mapDerivedCategory_upperStar` concerns the derived category of discrete coefficient sheaves, not the specified completed integral, raw rationalized and common-stage categories. The recorded module `Sheaf.Paper.ConstructiblePullbackTExact` has `sorry` at the four theorem bodies (lines 359, 440, 544, 719). In particular the existing Lean statement is not an attachment. I read the signatures and its retained eleven-step docstring; no Lean was edited or compiled.

## WANTED

None. Bhatt–Scholze and the Stacks sources used here are locally available. The coefficient-descent and point-coherence assertions are explicitly agent synthesis, not claimed to be verbatim theorems of Bhatt–Scholze.

## What was wrong and what changed

The returned parent was mathematically developed but its eleven proof steps totaled 11664 characters, leaving nearly all work on one item. The human explicitly reopened this already-reviewed node for parallel proof work. I kept the parent's statement verbatim and extracted four independent statement-only work packages. Their statements are approximately 2.3–3.1 thousand characters each; none states the full parent, and no new node is split in this delivery. No unit/chapter route or target was changed.

The retained sandbox initially contained only the dispatcher briefs, with no node, report or searches.jsonl. I copied the current live item and preserved its full old proof in `returned-argument.json` and below, together with its existing searches and metadata in the copied item. The delivery tool overlays split-owned fields on current server main; no repository git command or repository write was used. There was no retained sandbox split/report on which to run an initial repair dry run.

The first new lemma isolates exact restriction through completed-coefficient comparisons, site-object restriction, and the actual fibre-product chart square, rather than assuming ordinary inverse image is the global completed pullback. The second isolates the projective-summand/Roos calculation and the scalar-flat cohomology argument, including its balanced-tensor maps. The third is an abstract coefficient-family transport theorem, assuming integral t-exactness and proving rational/common-stage exactness and canonical-map coherence; it does not assert any geometric pullback theorem. The fourth concerns the specified point realization of an arbitrary point complex, with its normalized scalar/cohomology square; it does not assert the parent's pullback-to-a-point formula.

## Allocation of every returned argument

1. Old Step 1: the finite-type-to-Noetherian/dimension check remains parent Step 1; the integral-category/chart and constructibility assertions are in `lem-a1-integral-stratum-chart-restrictions`.
2. Old Step 2: all restriction/strict-completion/site-localization/product/Roos comparisons and input chart bounds are the first lemma's work.
3. Old Step 3: all finite reduction, K-flat representative, constant-section matrix, epimorphic projective-summand tower and finite-cone inverse-limit calculations are `lem-a1-completed-perfect-scalar-pullback`.
4. Old Step 4: actual fibre-product strata, base-changed covers and pullback-composition square are the first lemma; evaluation of the pulled-back scalar model is the second. Neither is replaced by set-theoretic factorization through a stratum.
5. Old Step 5: constant-sheaf exactness, scalar flatness, both cohomology formulas, the two inverse balanced-tensor maps, and transfer of vanishing without relative coefficient flatness are the second lemma.
6. Old Step 6: exact restrictions are the first lemma; model bounds are the second. Parent Step 2 retains the small assembly using the existing noetherian stratum-detection theorem and the standard-half definition. This is also the first lemma's chart-detection application, not a new theorem moved wholesale.
7. Old Step 7: integral linear exactness via the canonical strict-tower comparison is the first lemma; extension on fractions and the isomorphism-closure-of-halves argument are the third.
8. Old Step 8: pairs, arrows conjugated by scalar comparisons, stage representatives for halves and distinguished triangles, and common-stage exactness are the third lemma.
9. Old Step 9: uniqueness of truncation maps, shifts/cohomology composites and exactness of the induced heart functor are the third lemma. Its future proof uses the already existing `lem-pod-texact-truncation-comparison` and `lem-weil-heart-short-exact-triangles`, not new duplicates of those.
10. Old Step 10: canonical comparison squares and the identity/tower equations under coefficient extension are the third lemma. I made compatibility of beta with the specified shift comparisons an explicit hypothesis of that abstract lemma. For the actual pullback beta, scalar maps on the termwise reduction towers commute with shifts.
11. Old Step 11: exact point sections, localization, rational truncation identification, degree-zero realization and normalized scalar-extension coherence are the fourth lemma. Parent Step 4 composes its comparison with the pullback/cohomology comparison already obtained in Step 3.

The full original texts and citations are retained below, so extracting statements has not discarded or summarized the arguments future workers must carry out. Each work package is a theorem with its own hypotheses and can be assigned independently; only the parent assembles them.

## Sources and search record

Read Bhatt–Scholze, Lemma 6.5.8, Lemma 6.5.9(4)-(5), Remark 6.5.10, Proposition 6.6.11, Definition 6.8.10, Proposition 6.8.11(3), Proposition 6.8.14(1)-(2), and Remark 6.8.15. Proposition 6.6.11 gives finite stratified perfect scalar models; it does not itself state the canonical restriction-square comparison. Lemma 6.5.8 / Remark 6.5.10 give the immersion and weakly-etale completion route. Proposition 6.8.14 motivates rationalization and finite coefficient stages; the abstract t-exact family lemma is the detailed categorical argument in the old proof, not a quotation from that proposition. For the scalar calculation I read Stacks Tag 093M, `sites-modules.tex`, `lemma-completion-flat` (flatness over the constant Noetherian coefficient ring). I also read Tag 099N, `proetale.tex`, `lemma-pushforward-Noetherian-case`, especially (5), to verify the specified completed-pullback formula used by the pre-existing comparison node. No SGA route is used.

For each new node I ran leanfinder, loogle, grep and leansearch through the mandated msearch.py command. The semantic queries are different phrasings of that node's mathematical question. All sixteen commands succeeded; exact query strings and unaltered printed hits are in mathlib_searches and the command log. I read the hit signatures: ordinary presheaf pullback/restriction and existence of limits do not provide adic stratified chart comparisons; projective-resolution and K-projective lemmas do not compute the completed scalar model under g; linear localization and abelian exact-functor lemmas do not give common-stage t-exact transport and coherent truncation comparisons; residue-field evaluation and etale algebra lemmas do not identify this rational/common-stage point functor. There are zero new Mathlib leaves.

DAG and whole-blueprint searches were made for perfect scalar models, completed pullback, chart/stratum restrictions, t-exact localization, common stages, point realization, and Stacks Tags 093M/099N, using rg and tools/blueprint_refs.py. The potentially relevant statements were opened, including the characterization, finite-perfect tower results, scalar-normalized model theorem, local integral perfect-model cohomology, exact point sections, scalar point sections, point equivalence, scalar localization, and generic truncation comparison. Detailed comparisons follow. The ancestor is `lem-a1-finite-map-purity`, first paragraph, through `lem-a1-finite-etale-weil-fibre-comparison`; the new blueprint via lists include the current item in front. The current main-20261015 ancestor proof and unit/chapter records were read. This supports its geometric-fibre restriction bridge and changes no upper-level proof route.

## Not duplicates

- lem-a1-integral-stratum-chart-restrictions vs lem-weil-pbc-integral-stratified-perfect-characterization: the existing equivalence supplies models but does not state the specified integral-pullback/restriction identifications, base-changed chart square, or its finite-reduction normalization.
- lem-a1-integral-stratum-chart-restrictions vs lem-sf-immersion-completed-pullback-comparison: the existing theorem handles one immersion and the completed construction; the new package also handles site-object covers, the specified integral construction, and both factorizations of the pulled-back charts.
- lem-a1-integral-stratum-chart-restrictions vs lem-sfb-adic-finite-stratification-pullback: the existing statement concerns sheaves over constant discrete R and finite-type local trivializations, not completed derived perfect chart objects and their pullback-composition comparison.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-finite-perfect-adic-tower-limit: that existing theorem assumes a compatible algebraic local tower comparison and reconstructs its restriction; the new statement supplies the g-pullback scalar model, canonical quotient projections and transfer of cohomological vanishing along arbitrary g.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-finite-perfect-adic-complex-roos: the existing theorem identifies a termwise-epimorphic tower's ordinary limit with a derived limit; it has no completed coefficient pullback or scalar cohomology/amplitude statement.
- lem-a1-texact-coefficient-stage-descent vs lem-pod-texact-truncation-comparison: the existing lemma assumes an already t-exact functor between two categories; the new family lemma proves t-exactness after raw scalar localization and common-stage passage, and its coherent comparisons follow using that lemma.
- lem-a1-texact-coefficient-stage-descent vs lem-pur-semilinear-scalar-localization: existing fraction extension preserves linear/exact equations but states neither transported t-exactness nor a common-field-stage/cohomology comparison.
- lem-a1-texact-coefficient-stage-descent vs lem-sfb-linear-localization-descent: that theorem establishes R-linearity of a functor descending through a categorical localization, not t-exactness or common-stage triangulated descent.
- lem-a1-texact-coefficient-stage-descent vs lem-zl-field-shriek-lower-bound-common-stage-exactness: that theorem constructs coherent shifts and triangle preservation for a particular compact-support action, explicitly asserts no lower bound, and gives no t-structure/cohomology comparison package.
- lem-a1-point-realization-standard-cohomology vs lem-weil-point-proetale-sections-exact: the latter is the integral sections functor for arbitrary sheaves of rings; it does not state the raw rationalized/common-stage standard t-exactness or the normalized scalar/cohomology squares.
- lem-a1-point-realization-standard-cohomology vs lem-weil-point-sections-scalar-extension: the latter supplies the normalized phi maps and their tower associativity but not their compatibility with canonical rational truncation/cohomology maps or point t-exactness.
- lem-a1-point-realization-standard-cohomology vs lem-weil-point-fibre-equivalence: the existing equivalence is triangulated; its statement has no standard t-exactness or normalized scalar/cohomology square.
- lem-a1-point-realization-standard-cohomology vs lem-sf-point: the six-functor point package assumes a datum and asserts an exact equivalence, duality and Hom formulas; it does not state the standard t-structure comparison or normalized finite-field scalar squares needed here.
- lem-a1-completed-perfect-scalar-pullback vs lem-trf-point-reduction-unit-normalization: it normalizes point finite-quotient adjunction units, while the new lemma computes completed scalar pullback under arbitrary scheme maps and its cohomological interval.
- lem-a1-completed-perfect-scalar-pullback vs lem-sfb-local-integral-perfect-model-cohomology: it computes local cohomology of an already supplied immersion/slice scalar model; the new lemma additionally computes arbitrary completed g-pullback, all finite projections and bound transfer without relative flatness.
- lem-a1-completed-perfect-scalar-pullback vs def-sfb-quotient-kernel-completeness: it defines local derived completeness for a quotient kernel, not a completed perfect model or its pullback.
- lem-a1-completed-perfect-scalar-pullback vs lem-sfb-finite-constant-model-two-term-free-resolution: it resolves a degree-zero finite scalar module over condensed coefficients; the new lemma treats bounded complexes, arbitrary completed pullback and normalized inverse-limit projections.
- lem-a1-completed-perfect-scalar-pullback vs lem-sfb-integral-quotient-direct-image-comparison: it compares quotient reduction with ordinary direct image on an ambient internal-module category, rather than completed pullback of a scalar perfect complex.
- lem-a1-completed-perfect-scalar-pullback vs lem-sfb-adic-perfect-model-complete-reduction: it proves completeness and residue reduction/bounds from the termwise interval; the new lemma computes arbitrary completed g-pullback, all quotient stages, and transfer of the actual cohomological interval even when P has terms outside it.
- lem-a1-completed-perfect-scalar-pullback vs def-weil-pbc-completed-constant-realization-data: it defines input realization/comparison records; it proves no scalar-model pullback or cohomological bound transfer.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-completed-constant-module-model: it constructs an exact finite-module realization with no derived-complex conclusion; the new lemma has the completed derived pullback and canonical cohomology/quotient formulas.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-completed-constant-algebra-flat-quotients: it asserts flatness and quotient isomorphisms in degree zero, not the projective-complex inverse limit and arbitrary g-pullback.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-completed-constant-sheaf-reduction: it gives scalar flatness and reductions of the completed coefficient sheaf; the new lemma calculates arbitrary perfect-complex pullback, normalized tower limits and the transfer of vanishing.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-constant-completion-equivalence: it identifies completed and constant coefficient complete categories and reductions of ordinary pullback; it does not compute a perfect scalar model with its cohomology/bound transfer.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: it builds the marked scalar quotient tower and canonical comparison on one scheme; the new lemma computes arbitrary scheme pullback and transfer of actual cohomological vanishing.
- lem-a1-completed-perfect-scalar-pullback vs lem-cbc-finite-extension-reduction-cone-bound: it bounds all reductions of an ambient complex using a uniformizer cone, not the completed pullback of a perfect scalar model or the preservation of its original cohomological interval.
- lem-a1-completed-perfect-scalar-pullback vs lem-sp-constant-pullback-scalar: it preserves a scalar endomorphism under ordinary module pullback, without a derived inverse limit or perfect-complex cohomology assertion.
- lem-a1-completed-perfect-scalar-pullback vs lem-sp-constant-inverse-image-section: it transports constant sections and quotient kernels under inverse image; it is not a completed derived scalar-model computation.
- lem-a1-completed-perfect-scalar-pullback vs lem-weil-finite-free-completed-scalar-comparison: it compares coefficient-field extension on one scheme with a completed tower; the new lemma varies the scheme along arbitrary g and transfers scalar-model cohomological vanishing.
- lem-a1-completed-perfect-scalar-pullback vs lem-pod-point-principal-reduction-coefficients: it gives a point coefficient short exact sequence, not a bounded scalar-complex pullback along arbitrary schemes.
- lem-a1-completed-perfect-scalar-pullback vs lem-pod-point-reduction-coefficient-ring: it identifies the kernel and surjectivity of the point coefficient DVR quotient, not a derived scalar-complex model or its pullback.
- lem-a1-completed-perfect-scalar-pullback vs lem-pod-completed-integral-scalar-regular: it proves uniformizer powers injective on completed coefficient sections, not the perfect-complex pullback and cohomology theorem.

## Review by Q112

I checked the re-split against B–E with the statements, archived eleven-step proof, current blueprint ancestor and named source passages open. The parent statement is byte-for-byte unchanged. The four new lemmas state smaller independently assignable facts: restriction charts; scalar-perfect-complex evaluation; abstract coefficient-family descent; and point-realization cohomology. They introduce all schemes, rings, functors and coefficient categories themselves, keep exact completed versus ordinary restrictions separate, and have no proof steps or proof sketches inside their statement fields. Their source places identify the agent-synthesized portions instead of attributing stronger assertions to Bhatt–Scholze. The actual searches and blueprint ancestry were checked, and no matching project proof or Mathlib specialization was found.

For parent Step 1 I opened both finite-type Noetherianity and fibre-dimension-bound statements: the structure maps to Spec k are finite type, that base is quasi-compact and Noetherian, and its only fibre is X or W itself. These hypotheses justify the new chart lemma, whose statement explicitly supplies exact restrictions, constructible output, and linear exactness. Its proof work retains the canonical integral/strict-tower comparison; no identification is inferred from the two constructions having the same name. I read the existing comparison, immersion comparison and site-object inverse-image statements when shaping that package.

For Step 2 I checked that the scalar-model lemma takes a bound on actual cohomology, not on the terms of P. It therefore applies to the chart bound furnished in Step 1 even when a finite-projective resolution has extra negative terms. The chart square identifies the actual output restriction, not an object chosen only up to matching finite cohomology. The existing noetherian stratum-detection statement applies to the underlying abelian cohomology sheaf on W with the finite base-changed strata and their pro-etale covers; its exact inverse images are the restrictions in the new chart statement. The standard-half definition says exactly that the indicated cohomology groups vanish. This justifies both signs by boundedness. The only algebraic identifications left in the assembly are the fibre over the sole point of Spec k and membership in an isomorphism-closed half.

For Step 3 I checked each hypothesis of the abstract descent node: integral exactness and R-linearity are in the chart statement; integral t-exactness was proved in Step 2; prop-weil-pbc-integral-tstructure supplies the bounded integral t-structures under the noetherian finite-dimensional hypotheses already checked, and lem-weil-scalar-extension-exact-triangulated supplies exact finite-field transitions, with the associators of def-weil-algebraically-closed-coefficients; the rational and common-stage halves are isomorphism closures in the unchanged definition; bounded t-structures and canonical scalar-compatible truncations are asserted by prop-constructible-truncations; and lem-pur-integral-operations-scalar-extension states the pullback comparison and identity/tower compatibility. Its shift compatibility comes from the same scalar maps applied termwise on shifted reduction towers. The definition of derived pullback explicitly extends on fractions and acts on common-stage arrows by these conjugations, matching the abstract F_E and F_Omega rather than a replacement functor. The abstract lemma's exact-heart and canonical cohomology conclusions are the parent's remaining general clauses. Its future proof retains the existing abstract truncation uniqueness and heart short-exact-triangle tools; those are not created again.

For Step 4 I checked that s=Spec k is finite type over k and that the new point lemma concerns the specific Fib_s in the parent's definition, not arbitrary geometric stalks on a discrete site. That lemma identifies realization of standard point cohomology with cohomology of realization, for both finite rational and common coefficient stages, including the canonical normalized scalar square. Its inputs are the already established exact point sections, exact coefficient localization, localized t-structure, and the existing phi_{L/E} comparison with tower identity. Composing with Step 3 gives precisely the point formula and degree-zero assertion; scalar-square composition gives the final common-stage clause. No circular use of the parent occurs in any new statement or its work plan.

I tested the chart/scalar statements on W empty, empty pulled-back strata, non-surjective h, P=0, P=R shifted to either side of zero, and the two-term complex [R --pi--> R] representing R/pi. The latter has torsion cohomology and shows why one must not assume flat cohomology or identify its bound with a projective resolution's termwise bound. Scalar flatness over the constant R suffices to compute cohomology and the explicit balanced-tensor map transfers zero; no flatness of B_{V'} over g^{-1}B_V is introduced. For descent I tested an integral torsion object that becomes zero rationally, and objects only isomorphic to a representative in a standard half: the proof uses the isomorphism closures, never bounds on an arbitrary integral lattice. For the point package I checked j positive and negative, a degree-zero torsion integral representative (zero rational realization), identity E=L, and a three-field tower E subset L subset M. No separatedness or k-linearity hypothesis on the arbitrary h is used or added; no restriction on its fibres is present.

The repair request has one substantive demand, repeated in the return: spread the old 11664-character proof across at least three new comparable statement-only nodes and leave at most 3000 characters of parent assembly. Four new nodes now carry the separate arguments, with 2554 characters in the parent and no parent step over 2000. I made the shift-compatibility hypothesis of the abstract transport theorem explicit while checking its exact-functor construction. All former subarguments remain below verbatim with the allocation above. I did not replace the work by a shortened unassigned sketch.

## What could not be finished

Nothing within stage 1: the four new lemmas intentionally remain unsplit, for independent workers to prove/split. There are no Lean changes and no claim that their proofs are finished. Delivery validation and the final push are recorded below after the tools finish.

## Retained returned proof, verbatim

### Old step 1

Put $R=\mathcal O_E$, $\pi=\varpi_E$, $A_n=R/\pi^n$, and $B_T=\varprojlim_n(A_n)_T$. First work integrally. The schemes $X,W$ are Noetherian and finite-dimensional: apply [lem-weil-pbc-finite-type-over-noetherian] and [lem-fin-finite-type-fibre-dimension-bound] to their structure maps to $\operatorname{Spec}k$, whose one-point space is quasi-compact and whose field coordinate ring is Noetherian. Also $\ell$ is invertible since $\ell\ne p$. Thus [lem-weil-pbc-integral-stratified-perfect-characterization] applies to exactly the integral category used here, including its uniform reduction bounds. For $K\in D^b_c(X,R)$, [lem-pur-integral-operations-preserve-constructible](1) ensures $Lh^*K\in D^b_c(W,R)$ with the specified finite reductions. We will prove that any cohomological interval $[a,b]$ for $K$ is also an interval for $Lh^*K$.

Cited nodes: `lem-weil-pbc-finite-type-over-noetherian`, `lem-fin-finite-type-fibre-dimension-bound`, `lem-weil-pbc-integral-stratified-perfect-characterization`, `lem-pur-integral-operations-preserve-constructible`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.6.11; Proposition 6.8.11(3); Lemma 6.5.9(5)

### Old step 2

Choose the finite constructible locally closed stratification $i_\alpha:S_\alpha\to X$ and pro-etale covers $v_{\alpha t}:V_{\alpha t}\to S_\alpha$ in [lem-weil-pbc-integral-stratified-perfect-characterization](ii). Write $K|_{V_{\alpha t}}\cong B_{V_{\alpha t}}\otimes_R P_{\alpha t}^\bullet$, with $P^\bullet$ bounded finite projective. Restrictions here are ordinary exact inverse images, and they agree with the item's integral pullback. By [lem-a1-integral-pullback-completed-comparison] the integral pullback of [def-weil-derived-pullback-tensor-hom] along any morphism is naturally isomorphic to the strict-tower completed pullback, compatibly with the finite reductions; for immersions [lem-sf-immersion-completed-pullback-comparison] identifies the latter with the exact ordinary inverse image. For $v_{\alpha t}$, [lem-weil-proetale-weakly-etale-localization] identifies $V_{\alpha t,\mathrm{proet}}$ with the localized site and [lem-sfb-proetale-object-inverse-image-restriction](3) identifies the module inverse image $v_{\alpha t}^*$ with restriction to it, which is exact by [lem-weil-pbc-site-restriction-exact]. Restriction evaluates a sheaf on the same objects, so it preserves the sectionwise products of [lem-weil-proetale-countable-products-exact] and the inverse limit defining $B$. Applying it to both coordinates of the Roos cone in [lem-sf-strict-roos-derived-limit-comparison] therefore also commutes with completed pullback. In particular these restrictions commute with cohomology by [lem-weil-pbc-exact-functor-complex-cohomology]; hence $K|_{V_{\alpha t}}$ still has cohomology only in $[a,b]$.

Cited nodes: `lem-weil-pbc-integral-stratified-perfect-characterization`, `lem-sf-immersion-completed-pullback-comparison`, `lem-weil-proetale-weakly-etale-localization`, `lem-weil-pbc-site-restriction-exact`, `lem-weil-proetale-countable-products-exact`, `lem-sf-strict-roos-derived-limit-comparison`, `lem-weil-pbc-exact-functor-complex-cohomology`, `lem-a1-integral-pullback-completed-comparison`, `lem-sfb-proetale-object-inverse-image-restriction`, `def-weil-derived-pullback-tensor-hom`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.6.11; Lemma 6.5.8 and Remark 6.5.10; replete inverse-limit model of §3.1

### Old step 3

Here is the scalar-model calculation needed for these chosen $P^\bullet$. Its completed-coefficient representative is bounded and termwise projective, hence K-flat by [lem-pc-bounded-above-flat-kflat-site]. For a morphism $g:V'\to V$, the reduction of $B_V\otimes_RP^\bullet$ is $(A_n)_V\otimes_RP^\bullet$ by [lem-weil-pbc-completed-constant-sheaf-reduction]. Its finite pullback is $(A_n)_{V'}\otimes_RP^\bullet$: the constant-section comparison of [prop-weil-pbc-proetale-constant-ring-map] preserves each scalar matrix, and the finite module pullback is exact by [prop-weil-pbc-proetale-constant-exact]. Consequently the defining reduction-tower formula in [def-weil-derived-pullback-tensor-hom] gives
$$Lg^*(B_V\otimes_RP^\bullet)\cong R\varprojlim_n((A_n)_{V'}\otimes_RP^\bullet)\cong B_{V'}\otimes_RP^\bullet.$$
For the last equality, each projective term is a summand of a finite free module. The tower of that term has epimorphic transitions, so [det-pe-milnor-epimorphic] computes its derived limit as its ordinary limit. Finite sums and projectors commute with the limit, and the exact functor $R\lim$ of [lem-weil-pbc-ringed-strict-tower-homotopy-limit] commutes with the finitely many cones constructing the bounded complex. Thus the same differential matrices occur after the limit. All maps used are the constant-section and quotient maps, so this calculation respects their transitions.

Cited nodes: `lem-weil-pbc-completed-constant-sheaf-reduction`, `prop-weil-pbc-proetale-constant-ring-map`, `prop-weil-pbc-proetale-constant-exact`, `def-weil-derived-pullback-tensor-hom`, `det-pe-milnor-epimorphic`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, `lem-pc-bounded-above-flat-kflat-site`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Lemma 6.5.9(4)-(5), finite perfect scalar models; Lemma 6.5.8; §3.1; Stacks Tag 093M (sites-modules.tex, lemma-completion-flat)

### Old step 4

Base change the chosen strata and covers to $W$. By [lemma-constructible-pullback-stratification], $S'_\alpha=W\times_XS_\alpha\to W$ is a finite stratification; its strata are constructible by [lem-pur-scheme-constructible-preimage]. The base changes $V'_{\alpha t}=W\times_XV_{\alpha t}\to S'_\alpha$ cover in the pro-etale topology, by its base-change-stable covering definition [def-weil-pbc-proetale-site]. Let $g_{\alpha t}:V'_{\alpha t}\to V_{\alpha t}$ be the projection. The two factorizations of $V'_{\alpha t}\to X$, together with the composition comparison [lem-pod-integral-pullback-composition], identify
$$(Lh^*K)|_{V'_{\alpha t}}\cong Lg_{\alpha t}^*(K|_{V_{\alpha t}})\cong B_{V'_{\alpha t}}\otimes_RP_{\alpha t}^\bullet.$$
The first isomorphism uses the exact immersion and site restrictions just established in Step 2; the second is Step 3. Empty base-changed strata contribute no condition. This uses actual fibre-product strata and their projection morphisms.

Cited nodes: `lemma-constructible-pullback-stratification`, `lem-pur-scheme-constructible-preimage`, `def-weil-pbc-proetale-site`, `lem-pod-integral-pullback-composition`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.6.11, pullback of its stratified models; Lemma 6.5.9

### Old step 5

Fix one of the models in Step 4, abbreviating it by $P^\bullet$ on $V$, and put $N^j=H^j(P^\bullet)$. The constant-sheaf functor $M\mapsto\underline M$ is exact, since it is sectionwise exact by [lem-weil-pbc-constant-module-section-properties](1), so $H^j(\underline{P^\bullet})=\underline{N^j}$; tensoring with $B_T$ is exact by flatness of $B_T$ over the constant ring $R$ in [lem-weil-pbc-completed-constant-sheaf-reduction]. Applying [lem-weil-pbc-exact-functor-complex-cohomology] to these two exact functors gives
$$H^j(B_T\otimes_RP^\bullet)=B_T\otimes_R\underline{N^j}_T\quad(T=V,V').$$
For $j\notin[a,b]$ the expression at $V$ is zero by Step 2. Its underived ringed pullback along $g:V'\to V$ is $B_{V'}\otimes_R\underline{N^j}_{V'}$: on balanced tensors the identification is $b'\otimes(b\otimes n)\mapsto b'g^\sharp(b)\otimes n$, with inverse $b'\otimes n\mapsto b'\otimes(1\otimes n)$. Constant sheaves pull back to the same constant module; this follows by applying the constant functor and inverse image to a presentation, both being left adjoints, or directly from their constant-section universal property [def-weil-pbc-constant-sheaf, def-weil-proetale-inverse-image]. Underived pullback sends the zero module to zero. Therefore the expression at $V'$ is zero as well. This only uses scalar flatness over $R$, and does not require flatness of $B_{V'}$ over $g^{-1}B_V$.

Cited nodes: `lem-weil-pbc-completed-constant-sheaf-reduction`, `lem-weil-pbc-exact-functor-complex-cohomology`, `def-weil-pbc-constant-sheaf`, `def-weil-proetale-inverse-image`, `lem-weil-pbc-constant-module-section-properties`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.8.11(3), finite scalar models; Stacks Tag 093M, lemma-completion-flat

### Old step 6

The exact restrictions to $S'_\alpha$ and $V'_{\alpha t}$ commute with cohomology as in Step 2. For $j\notin[a,b]$, Steps 4-5 show that every such restriction of $\mathcal H^j(Lh^*K)$ vanishes. Apply [lem-weil-pbc-noetherian-stratum-detection] on the Noetherian scheme $W$ to its underlying abelian sheaf: $\mathcal H^j(Lh^*K)=0$. Thus integral pullback preserves every cohomological interval $[a,b]$. In particular if $K$ is in the integral nonpositive half, choose a lower bound $a$ and take $b=0$; if it is in the nonnegative half choose an upper bound $b$ and take $a=0$. The integral standard classes in [def-weil-constructible-standard-tstructure] are therefore preserved. No restriction is imposed on the geometric fibres of $h$.

Cited nodes: `lem-weil-pbc-noetherian-stratum-detection`, `def-weil-constructible-standard-tstructure`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.6.11 and Proposition 6.8.11(3), detection on a finite stratification

### Old step 7

Pass to $E$. Integral pullback is $R$-linear by its termwise scalar action. By [lem-a1-integral-pullback-completed-comparison] it is naturally isomorphic on derived complete objects, in particular on $D^b_c$, to the strict-tower completed pullback, which preserves shifts and distinguished triangles of complete objects by [lem-cbc-completed-pullback-triangles]; transporting that shift comparison along the natural isomorphism, the integral pullback is exact on $D^b_c(X,R)\to D^b_c(W,R)$. Its extension on fractions is precisely the rational pullback of [def-weil-derived-pullback-tensor-hom]; [lem-pur-semilinear-scalar-localization] shows it is again exact. An object in either rational standard half is, by [def-weil-constructible-standard-tstructure], isomorphic after rationalization to an integral object in that half. Applying $Lh^*$ to this isomorphism and using Step 6 puts its image in the same rational half. This proves both required inclusions for $E$. The argument uses the isomorphism closures in the definition, and does not infer an integral bound from an arbitrary rational representative.

Cited nodes: `lem-cbc-completed-pullback-triangles`, `lem-pur-semilinear-scalar-localization`, `def-weil-derived-pullback-tensor-hom`, `def-weil-constructible-standard-tstructure`, `lem-a1-integral-pullback-completed-comparison`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.8.14(2); Remark 6.8.15

### Old step 8

At $\Qlb$, use the objects $(F,M)$ and common-stage morphisms of [def-weil-algebraically-closed-coefficients]. Pullback sends this object to $(F,Lh_F^*M)$, and acts on arrows by the scalar-extension comparison specified in [def-weil-derived-pullback-tensor-hom]. An object of either standard half is isomorphic to such a pair with $M$ in that half at a finite field $F$, by [def-weil-constructible-standard-tstructure]. Step 7, applied to $F$, sends it into the required half. The functor is exact: a distinguished triangle has a representative at one common finite field, and its image there is distinguished by Step 7, hence also in the pair category. This proves t-exactness at $\Qlb$.

Cited nodes: `def-weil-algebraically-closed-coefficients`, `def-weil-derived-pullback-tensor-hom`, `def-weil-constructible-standard-tstructure`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.8.14 and the common-stage convention; Remark 6.8.15

### Old step 9

By [prop-constructible-truncations], both standard pairs are bounded t-structures. Steps 7-8 and shift compatibility give preservation of both halves at every integer. Apply [lem-pod-texact-truncation-comparison] to the exact functor $Lh^*$. Its unique comparisons commute with the canonical truncation maps, hence their composite and the shift comparison give the stated natural isomorphism $\mathcal H^j(Lh^*K)\cong Lh^*\mathcal H^j(K)$. T-exactness also sends the intersection of the two halves into their intersection, the hearts of [def-weil-constructible-heart]. A short exact heart sequence gives a distinguished triangle by [lem-weil-heart-short-exact-triangles](4); its image is a distinguished triangle with all vertices in the target heart, hence is a short exact sequence by the same clause. The heart functor is therefore exact.

Cited nodes: `prop-constructible-truncations`, `lem-pod-texact-truncation-comparison`, `def-weil-constructible-heart`, `lem-weil-heart-short-exact-triangles`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.8.11 and Proposition 6.8.14; BBD 1.3.3-1.3.6 for the generic truncation/heart argument

### Old step 10

These comparisons respect finite coefficient extension. Indeed [lem-pur-integral-operations-scalar-extension] supplies the natural pullback comparison and its tower compatibility, while [prop-constructible-truncations] gives the corresponding compatibility of truncations and their natural maps. The natural-transformation and composition assertions of [lem-pod-texact-truncation-comparison] imply that the two truncation comparisons obtained by extending the field satisfy the same characterizing equations and coincide. The same holds for their composite defining $\mathcal H^j$. Thus every map and equality at $\Qlb$ is represented at a common finite field and is unchanged upon further extension. No compatibility of arbitrarily chosen splittings is needed.

Cited nodes: `lem-pur-integral-operations-scalar-extension`, `prop-constructible-truncations`, `lem-pod-texact-truncation-comparison`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Proposition 6.8.14; common-stage functor convention; uniqueness of truncation comparisons

### Old step 11

Finally let $\bar x:s=\operatorname{Spec}k\to X$ be as in the statement. This is a morphism between finite-type $k$-schemes, so apply Step 9 to it. Sections on $s_{\mathrm{proet}}$ are exact and commute with cohomology by [lem-weil-point-proetale-sections-exact]. The functor $\operatorname{Fib}_s$ is, at $E$, exactly sections followed by tensor with $E$ as in [def-weil-finite-coefficient-point]. Tensor with $E=R[1/\pi]$ is exact by [lem-weil-pbc-localization-module-exact], so [lem-weil-pbc-exact-functor-complex-cohomology] identifies its cohomology with the fibre of the integral cohomology, and the same remains true after rationalization: [prop-weil-localized-tstructure] identifies rational truncations with localized integral truncations. Combining this with the pullback/cohomology comparison gives
$$\operatorname{Fib}_s(L\bar x^*\mathcal H^jK)\cong H^j(\operatorname{Fib}_s(L\bar x^*K)).$$
If $K=\mathcal F$ is in the heart, $L\bar x^*\mathcal F$ is in the point heart and the same exact functors put its fibre in degree zero. At $\Qlb$ apply this at a common finite field; [lem-weil-point-sections-scalar-extension] provides the fibre scalar comparisons with their identity and composition compatibility. Together with Step 10 these give exactly the final scalar-extension clause.

Cited nodes: `lem-weil-point-proetale-sections-exact`, `def-weil-finite-coefficient-point`, `lem-weil-pbc-localization-module-exact`, `lem-weil-pbc-exact-functor-complex-cohomology`, `lem-weil-point-sections-scalar-extension`, `prop-weil-localized-tstructure`

Source: `literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf`, Example 6.5.2; exact point evaluation on the replete pro-etale topos; Proposition 6.8.14

