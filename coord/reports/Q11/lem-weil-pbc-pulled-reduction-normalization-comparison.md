# Stage-1 repair: actual re-split

## Worker report

This repairs the returned Q11 delivery, rather than re-pushing its shorter proof. I compared the retained sandbox with the live repository. Only proof, mathlib_searches and split_report differed; the live repository retains the seven full NP arguments (341ac5be) and the Q43 Lean statement. I rebased the new split onto the live node, kept its mathematical statement and stmt_deps exactly, preserved its blueprint/import/review/Lean metadata, and retained all prior search records. The earlier returned report and citations are preserved in work/returned-report.md and work/returned-citations.json. Their claims of “no new nodes” and “shortening suffices” are superseded by this repair.

The first required dry run of the retained delivery exited OK (not pushed) at 063feeebce4. That mechanical result did not address the mathematical return: the repair note explicitly requires new obligations. I therefore made the requested structural change, even though that old version passed the gate.

Files delivered: the item JSON, the two new node JSONs listed below, and this report. citations.json in the sandbox quotes the new statements verbatim for each cited node in each item step. No Lean file was written, no compiler/build tool was run, and the shared repository and launcher were read-only.

## New nodes

- lem-weil-pbc-pulled-reduction-flat-model-formulas: unsplit statement, 4205 characters, extracting base steps 1–4. It requires actual restricted and pulled flat-term K-flat models, their derived identifications, the specified tau formula, and the correctly oriented invertible thetaH and thetaN representatives with inverses. It does not assert the normalization square, triple or unit coherence, or independence of the whole diagram.
- lem-weil-pbc-pulled-reduction-generator-descent: unsplit statement, 4123 characters, extracting base steps 5–7. Given the explicit model maps from the first node, it requires their square, triple and unit generator equations, chain naturality, and descent with the separate scalar-extension and pullback comparisons. It does not construct the models or identify the specified tau and pulled mate from scratch.

Both nodes carry proof=[], proof_deps=[], proof_origin=null and status=unsplit. The assembly has two non-elementary citation steps, 1214 characters in total, and every step is below 2000 characters. These are two comparable proof obligations, not elementary facts made into nodes or one node repeating the whole item. This is precisely the extraction requested by the return and human A6 note. The old full argument is retained verbatim below as a proof plan for their future workers, outside their statements.

## Attachments and searches

No attachment. The whole project source was searched for the item tag and the notion in lean/WeilConjectures; it has generic pullback results, not this complete adic comparison. The theorem AlgebraicGeometry.Scheme.PulledNormalization.pulled_reduction_normalization_comparison at lean/Sheaf/Paper/PulledReductionNormalizationComparison.lean:410 still has sorry at line 411. I read its statement, Comparison specification and proof docstring. That source cannot finish this item. The new ids are absent from the DAG and from the project Lean source.

Before making the new nodes I searched the whole DAG by the Stacks tags 0G7E, 0G7D, 0D6D, 03EL, 06YS, 06YT and 06YY, and by pulled normalization, generator/descent and flat model/formula keywords. I ran blueprint_refs.py ancestor for the item (lemma-weil-pbc-completed-pullback-reduction, via=[]), and blueprint search for normalization, pulled reduction, scalar, K-flat, completed-pullback, scalar-six-pullback and K-flat complexes. The matching imported blueprint nodes supply general operations or the completed result, not either new finite-model statement. same_as is consequently empty. The first new node serves paragraph 2 of the ancestor proof and supplies paragraph 1's model maps; the second serves paragraph 1's normalization cocycles and descent of paragraph 2's comparisons. The fixed chapter and unit route are unchanged.

I reused the retained searches after reading their results. For each new node I additionally ran five exact msearch.py queries: LeanFinder, Loogle, grep, LeanSearch, and a second LeanFinder phrasing. The exact queries, result counts and hits are recorded in that node and searches.jsonl. All ten calls succeeded. No search was fabricated or an unavailable service called “no match.” For the model node grep searched Algebra/Homology for KFlat/K_flat spellings (zero hits). For the descent node grep searched Algebra/Category/ModuleCat/Sheaf and returned pullbackComp, conjugateEquiv_pullbackComp_inv and pullback_assoc. I read their declarations at PullbackContinuous.lean:167,177,193: these concern ordinary sheaf pullbacks. AdicCompletion.ofTensorProductEquivOfFiniteNoetherian and flat_of_isNoetherian at RingTheory/AdicCompletion/AsTensorProduct.lean:328,379 concern ordinary modules, not completed ring sheaves and the specified tau. Algebra.FormallyUnramified.flat_of_restrictScalars at RingTheory/Unramified/Finite.lean:275 requires an unramified algebra and proves a different direction of flatness. Localization.Construction.natTransExtension at CategoryTheory/Localization/Construction.lean:269 is generic extension along localization; it supplies neither the coefficient generator identities nor the K-flat/sheaf-model identifications. DerivedCategory.left_fac at Algebra/Homology/DerivedCategory/Fractions.lean:59 gives a roof, not this result. The remaining hits are presentation, flat-module or generic derived-functor tools. None is an exact match or a one-line specialization for either combined obligation. There are zero Mathlib leaves.

## Sources and proof coverage

I read GOAL.md, the three-level route requirements of SETUP.md, the chapter and unit records, the stage-1 contract and delivery-errors B–E. The current main-20261015 ancestor statement and both paragraphs of its proof are in sec-proper-base-change/sk-prop-pbc-complete/lemma-weil-pbc-completed-pullback-reduction(.proof).md. I also read det-prop-scalar-six-pullback.proof.md in the current scalar-six unit. The ancestor's phrase “compatibilities inherited from the tower structure” is expanded by these concrete generator identities; it is not itself used as a proof of them.

For the model node the primary source is Stacks 0G7E, sites-cohomology.tex, lemma-pullback-K-flat, which preserves BOTH K-flatness and flat terms without flatness of the structural ring map. I also read 06YS/lemma-K-flat-resolution, 06YY/lemma-derived-base-change and 0D6D/lemma-derived-pullback-composition in that file, and 03EL/lemma-tensor-product-pullback in sites-modules.tex. For the descent node the primary source is 0G7D/lemma-factor-through-K-flat, including its flat-term clause. I also read 06YT/lemma-derived-tor-quasi-isomorphism-other-side and the 06YY quasi-isomorphism/descent argument. 07A4/lemma-pullback-tensor-product is support for the derived tensor comparison. I checked all these tag/label correspondences in tags/tags. The particular adic generator formulas are agent refinements of these constructions and of the ancestor, not quotations of a nonexistent Stacks theorem asserting the whole item. No SGA source is used. WANTED: none.

Every one of the base's seven arguments appears below in full and is assigned to an explicit obligation in the new statements. In particular the factorization of tensor with an acyclic restricted complex is an asserted identity plus acyclicity in the model node, not erased; the inverse orientation and formula for the pulled mate are stated there; and scalar-extension and pullback quasi-isomorphism preservation and composable resolution comparisons remain separate assertions in the descent node.

## Review by Q11

The return identified a structural failure, not a false mathematical statement. I repaired it by extracting the two unsplit lemmas requested, preserving all base arguments and keeping the target statement unchanged. The retained report's interpretation of a 3000-character diagnostic was wrong: the human note also demands at least two comparable new nodes. That requirement is now met; the new report no longer describes shortening as the repair.

For assembly step 1 I opened lem-weil-pbc-pulled-reduction-flat-model-formulas and checked that its statement gives the four models with their rings, the identifications in the derived categories, the ACTUAL tau from the strict-tower comparison, and the scalar mate in the correct direction followed by pulled normalization. The step takes invertibility from the statement's two invertible arrows and localized isomorphism, not from its future proof. Arbitrary K and the lack of flatness of the quotient ring map are explicit in the cited statement. Thus the step does not assume completeness to get a resolution or pretend that Z/l^b→Z/l^a is flat.

For assembly step 2 I opened both new nodes. The first supplies precisely the model maps required as input by the second. The second's statement gives the two sides of the square on (([x] tensor r) tensor t) tensor s, then equality of the whole sheafified maps. Its triple statement includes the intermediate q_ba(q_cb(t)s), its equal-index statement identifies the scalar unit with its inverse, and it states the before-inverse-image triple as well. Its last paragraph gives naturality for every chain map, differential compatibility, separate scalar-extension and pullback preservation and canonical composable resolution comparisons, and passage through W^{-1}P≃D(B_T). This is exactly what the assembly needs for all the remaining derived clauses, with the specified comparisons. Neither step is marked elementary; no uncited construction is hidden there. citations.json contains literal extracts from these statements, and proof_deps is the union of uses.

I also opened the statements of all original cited nodes. For old step 1, lem-pc-kflat-resolution gives flat terms as well as K-flatness, lem-weil-pbc-constant-completion-equivalence says B is R-flat, and def-pc-kflat-complex supplies precisely the acyclic tensor test. The displayed tensor factorization and composition of exact functors prove the restriction assertion. For old step 2, lem-weil-pbc-ringed-pullback-preserves-kflat explicitly requires flat terms and explicitly requires NO coefficient flatness; its identity-topos case covers scalar change. The statements of lem-pur-derived-change-of-rings and lem-weil-pbc-ringed-topoi-derived-pullback give the required derived computation, including quasi-isomorphisms. All sites here are the small skeletons fixed by the datum.

For old step 3, the strict-tower comparison statement specifies tau as the pullback/tensor comparison followed by finite constant-to-completed comparison. The flat-coefficient-reduction-adjunct statement gives x tensor t→x tensor t under B-flatness and B tensor_R S≃S; the completion-equivalence statement supplies both hypotheses because S=R/I^n and B/I^nB≃S. The K-flat scalar-comparison-normalization statement identifies the inverse coequalizer comparison with the specified mate. Ringed-tensor-section-calculus supplies actual sheafification-unit pure tensors and determination of maps; [x] is a local inverse-image generator, not a claim that every section is a single pure tensor. Thus these are actual sheaf tensor chain maps.

For old step 4, the scalar-comparison-normalization statement gives the inverse orientation required for V_b tensor S_a→g_a^*(P_b tensor S_a). The datum explicitly supplies the quotient normalization and its inverse, and successive-derived-quotient-normalization gives thetaN and its actual associator formula. I checked both inverse composites by balancing. This matters because replacing the mate by an arbitrary isomorphism would not prove the requested square. The model statement now records the direction and exact composite, not only invertibility.

For old steps 5–6, I recomputed the square using q_ba(r-bar_b)=r-bar_a and multiplicativity, then the triple using q_ba q_cb=q_ca. The datum's statement gives exactly those identities; the actual scalar associator and its generator formula are in successive-derived-quotient-normalization; section-calculus gives equality after sheafification. The intermediate value q_ba(q_cb(t)s), the before-inverse-image formula, and the unit with inverse h→h tensor 1 are all retained in the second node. These computations by themselves are elementary, but the extracted node also includes their non-elementary descent and comparison obligations, as requested by the repair.

For old step 7, the tensor-complex definition gives the actual signed differential and functoriality. The scalar-extension theorem states quasi-isomorphism preservation and canonical resolution comparisons compatible with a third resolution; the ringed-topos-derived-pullback theorem separately states the analogous properties on the flat-term class. Site-derived-tensor-descent states the localization equivalence and determination of natural transformations. The descent node retains each of these distinct obligations. This supplies the bridge from generator computations on complexes to the named derived transformations, rather than a vague claim that “coherence transports.”

Edge cases checked for BOTH new statements: g=id; K=0 and P=0; b=a; c=b and b=a in the triple; empty site/zero coefficient ring when permitted by the datum. I tested A=Z_l, I=(l), in particular b=2,a=1: Z/l^2→Z/l need not be flat, whereas scalar extension of the chosen K-flat models is legitimate. No division, nonzero-object, regular-sequence, boundedness or completeness condition enters either formula. In the unit case the generator identity is multiplication with the displayed two-sided inverse. In the triple case every possible equality of adjacent indices reduces to q_aa=1. No statement dispute was found.

The same-tag and concept searches found the existing generic tools recorded below. In particular ringed-common-quotient-pullback-comparison gives finite insertion and geometric composition coherence but not the quotient-normalization square for this specified tau nor the simultaneous four models and inverse thetaH formula; ringed-kflat-word-comparison-descent supplies a generic lifting principle but no these particular generator equations; quotient-expression-kflat-normalization assumes a DVR coefficient system and addresses expressions in that system, rather than an arbitrary Noetherian adic datum with a constant/completed restriction comparison. Those facts remain reusable tools for future proofs, not replacements for the new concrete obligations. The item itself has additional coherence and representative-independence clauses; neither new statement is its whole content. Existing maintainer-owned tool_uses are retained, not newly asserted by this worker. No new cross-unit proof edge is introduced in the item: its assembly cites just the two new nodes in its own unit.

## Preserved full base argument and allocation

The following is the live seven-step NP proof, not the returned shortened rewording. Steps 1–4 are the proof plan of the flat-model/formula obligation, and steps 5–7 the proof plan of the generator/descent obligation. This appendix preserves every base argument and source, while the new nodes remain strictly statement-only.

### Base step 1 → lem-weil-pbc-pulled-reduction-flat-model-formulas

Choose a flat-term K-flat $B_T$-complex $P$ representing $K$ by [lem-pc-kflat-resolution]. The flatness of $B_T$ over $R_T$ in [lem-weil-pbc-constant-completion-equivalence] implies that $\operatorname{Res}P$ is K-flat over $R_T$: for an acyclic $R_T$-complex $E$, $B_T\otimes_{R_T}E$ is acyclic, and $P\otimes_{R_T}E=P\otimes_{B_T}(B_T\otimes_{R_T}E)$ is acyclic by [def-pc-kflat-complex]. Its terms are $R_T$-flat because the functor $P^i\otimes_{R_T}-$ is the composite of the two exact tensor functors. This uses no completeness of $K$.

Cited nodes: lem-pc-kflat-resolution, lem-weil-pbc-constant-completion-equivalence, def-pc-kflat-complex.
Source: literature/stacks-project/sites-cohomology.tex, Tags 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat), together with the flat coefficient extension specified in the cited node.

### Base step 2 → lem-weil-pbc-pulled-reduction-flat-model-formulas

Put $P_n=P\otimes_{B_T}S_{n,T}$ and $U=g_R^*\operatorname{Res}P$. By [lem-weil-pbc-ringed-pullback-preserves-kflat], applied also to identity-topos scalar extension, $P_n$, $U$, $U\otimes_{R_{T'}}S_{n,T'}$ and $V_n=g_n^*P_n$ are K-flat with flat terms over their respective rings. By [lem-pur-derived-change-of-rings] and [lem-weil-pbc-ringed-topoi-derived-pullback] these represent $K_n,N,N_n,H_n$, respectively. The coefficient identifications and quotient maps are those of [def-weil-pbc-adic-coefficient-datum]. Thus all successive scalar extensions below are computed on these same complexes; no flatness of $S_{b,T}\to S_{a,T}$ is assumed.

Cited nodes: lem-weil-pbc-ringed-pullback-preserves-kflat, lem-pur-derived-change-of-rings, lem-weil-pbc-ringed-topoi-derived-pullback, def-weil-pbc-adic-coefficient-datum.
Source: literature/stacks-project/sites-cohomology.tex, Tags 0G7E (lemma-pullback-K-flat), 06YY (lemma-derived-base-change).

### Base step 3 → lem-weil-pbc-pulled-reduction-flat-model-formulas

Write $[x]$ for a local inverse-image generator of a section $x$ of $P$, and $[x\otimes1]$ for the corresponding generator in $V_n$. If $r$ is a local $R_{T'}$-section, write $\bar r_n$ for its image in $S_{n,T'}$. By [lem-weil-pbc-pulled-reduction-strict-tower-comparison], $\tau_n$ is specifically pullback/scalar comparison followed by the finite constant-to-completed comparison. The latter is $x\otimes t\mapsto x\otimes t$ by [lem-weil-pbc-flat-coefficient-reduction-adjunct]; its hypotheses hold here by the flatness and finite-reduction isomorphisms in [lem-weil-pbc-constant-completion-equivalence]. The former is the ordinary balanced comparison on K-flat representatives by [lem-sfb-kflat-scalar-comparison-normalization]. Consequently its chain-level formula is
$$\tau_n:([x]\otimes r)\otimes t\longmapsto[x\otimes1]\bar r_n t.$$
These are maps of actual sheaf tensor complexes: the local formulas are balanced and restriction-compatible, and the pure tensors determine maps by [def-weil-pbc-ringed-tensor-section-calculus].

Cited nodes: lem-weil-pbc-pulled-reduction-strict-tower-comparison, lem-weil-pbc-flat-coefficient-reduction-adjunct, lem-weil-pbc-constant-completion-equivalence, lem-sfb-kflat-scalar-comparison-normalization, def-weil-pbc-ringed-tensor-section-calculus.
Source: literature/stacks-project/sites-cohomology.tex, Tags 0D6D (lemma-derived-pullback-composition), 0G7E (lemma-pullback-K-flat); ordinary balanced comparison: sites-modules.tex Tag 03EL (lemma-tensor-product-pullback).

### Base step 4 → lem-weil-pbc-pulled-reduction-flat-model-formulas

Apply [lem-sfb-kflat-scalar-comparison-normalization] to the constant coefficient map $S_{b,T}\to S_{a,T}$ and inverse image $g^{-1}$. The ring sheaves on $T'$ are their inverse images by the constant-sheaf identifications of [lem-weil-pbc-constant-completion-equivalence]. In the orientation used in the statement, its comparison identifies $V_b\otimes_{S_{b,T'}}S_{a,T'}$ with $g_a^*(P_b\otimes_{S_{b,T}}S_{a,T})$. Follow by $g_a^*$ of the normalization in [def-weil-pbc-adic-coefficient-datum]. Both arrows are isomorphisms, so this is the specified invertible $\theta^H_{b,a}$. Explicitly,
$$([x\otimes1]t)\otimes s\longmapsto[x\otimes1]q_{b,a}(t)s,$$
with inverse $[x\otimes1]s\mapsto[x\otimes1]\otimes s$. For $N$, [lem-sfb-successive-derived-quotient-normalization] gives $(u\otimes t)\otimes s\mapsto u\otimes q_{b,a}(t)s$, the specified $\theta^N_{b,a}$.

Cited nodes: lem-sfb-kflat-scalar-comparison-normalization, lem-weil-pbc-constant-completion-equivalence, def-weil-pbc-adic-coefficient-datum, lem-sfb-successive-derived-quotient-normalization.
Source: literature/stacks-project/sites-cohomology.tex, Tags 0D6D (lemma-derived-pullback-composition), 0G7E (lemma-pullback-K-flat); sites-modules.tex Tag 03EL (lemma-tensor-product-pullback).

### Base step 5 → lem-weil-pbc-pulled-reduction-generator-descent

Evaluate the two sides of the desired square on $(([x]\otimes r)\otimes t)\otimes s$. The upper route gives $[x\otimes1]q_{b,a}(\bar r_b t)s$; the lower route gives $[x\otimes1]\bar r_a q_{b,a}(t)s$. These agree because $q_{b,a}$ is a ring map and $q_{b,a}(\bar r_b)=\bar r_a$. The latter identity follows from the compatible coefficient quotient maps of [def-weil-pbc-adic-coefficient-datum]. Additivity and balancing, followed by sheafification, prove equality on the whole complexes by [def-weil-pbc-ringed-tensor-section-calculus]. Hence $\theta^H_{b,a}(\tau_b\otimes1)=\tau_a\theta^N_{b,a}$.

Cited nodes: def-weil-pbc-adic-coefficient-datum, def-weil-pbc-ringed-tensor-section-calculus.
Source: literature/stacks-project/sites-cohomology.tex, Explicit balancing calculation for the canonical maps in Tags 03EL and 0D6D.

### Base step 6 → lem-weil-pbc-pulled-reduction-generator-descent

For $c\ge b\ge a$, the route through $b$ sends $(([x\otimes1]t)\otimes s)\otimes v$ to
$$[x\otimes1]q_{b,a}(q_{c,b}(t)s)v=[x\otimes1]q_{c,a}(t)q_{b,a}(s)v.$$
The direct route first reassociates the two coefficient tensors and has exactly the latter value. Here $q_{b,a}q_{c,b}=q_{c,a}$ is part of [def-weil-pbc-adic-coefficient-datum], and the canonical scalar associators and their generator formulas are [lem-sfb-successive-derived-quotient-normalization]. For $b=a$, the same formula is $h\otimes s\mapsto hs$, with inverse $h\mapsto h\otimes1$, so it is the scalar-extension unit identification. The calculation before inverse image is identical with $[x\otimes1]$ replaced by $x\otimes1$; the balancing formula then is precisely $(x\otimes t)\otimes s\mapsto x\otimes q_{b,a}(t)s$. The local tensor generators determine these chain maps by [def-weil-pbc-ringed-tensor-section-calculus].

Cited nodes: def-weil-pbc-adic-coefficient-datum, lem-sfb-successive-derived-quotient-normalization, def-weil-pbc-ringed-tensor-section-calculus.
Source: literature/stacks-project/sites-cohomology.tex, Tags 0D6D (lemma-derived-pullback-composition) and 03EL, with the explicit triple and unit balancing calculations.

### Base step 7 → lem-weil-pbc-pulled-reduction-generator-descent

For a chain map $f:P\to P'$, each formula above changes only $x$ to $f(x)$, proving naturality on flat-term K-flat models. These formulas commute with differentials because the coefficient sheaves are in degree zero and their multiplications commute with the tensor differential of [def-pc-tensor-complex-sheaves]. Scalar extension preserves quasi-isomorphisms between K-flat complexes and has canonical, composable resolution comparisons by [lem-pur-derived-change-of-rings]; pullback has the same property on the chosen flat-term class by [lem-weil-pbc-ringed-topoi-derived-pullback]. Finally [lem-weil-pbc-site-derived-tensor-descent] identifies the localization of this class with $D(B_T)$. Thus the natural chain maps, their inverse maps, the square, the triple equality and the unit equality all descend through quasi-isomorphisms, and their values are independent of $P$. This proves all clauses for arbitrary $K$ in the stated derived categories.

Cited nodes: def-pc-tensor-complex-sheaves, lem-pur-derived-change-of-rings, lem-weil-pbc-ringed-topoi-derived-pullback, lem-weil-pbc-site-derived-tensor-descent.
Source: literature/stacks-project/sites-cohomology.tex, Tags 06YT (lemma-derived-tor-quasi-isomorphism-other-side), 06YY (lemma-derived-base-change), 0G7D (lemma-factor-through-K-flat).

## Not duplicates

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-coef-semilinear-system-models: the existing node concerns Generic strict semilinear system constructions and representative normalization; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pbc-successive-derived-scalar-normalization-data: the existing node concerns Normalized presentation data for successive derived scalar extensions; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pur-change-of-rings-complex: the existing node concerns Termwise change of rings of a cochain complex; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pur-derived-constant-pullback-comparison: the existing node concerns Canonical derived constant-sheaf pullback comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pur-etale-scalar-pullback-iso: the existing node concerns Canonical derived scalar and pullback isomorphism; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pur-open-coefficient-normalizations: the existing node concerns Exact-pullback and open-unit coefficient normalizations; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-pur-strict-quotient-expressions: the existing node concerns Strict quotient expressions with actual horizontal transitions; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-sfb-integral-quotient-coefficients: the existing node concerns Canonical integral uniformizer quotient coefficient maps; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-sfb-integral-quotient-projection-map: the existing node concerns Integral quotient internal projection arrow; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs def-sfb-internal-derived-scalar-comparisons: the existing node concerns Normalized internal derived scalar comparison interface; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-a1-finite-pullback-strict-tower-comparison: the existing lemma is the DVR/Koszul strict-tower and shift comparison; the new lemma identifies general adic constant/completed models and quotient normalization formulas without those DVR hypotheses.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-a1-pulled-koszul-tower-chain-comparison: the existing node concerns Ordinary pullback of principal Koszul towers and target augmentation; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-cbc-completed-open-kflat: the existing node concerns Completed-coefficient open extension preserves flat-term K-flat models; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-exc-proetale-constant-support-projection: the existing node concerns Constant-coefficient projection for compact support; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-fix-tensor-pullback-square: the existing node concerns Tensor inverse-image comparisons commute around an open square; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pd-module-ringed-topos-derived-comparison: the existing node concerns Module-object and ringed-topos derived tensor comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-per-proetale-scalar-slice-comparison: the existing node concerns Normalized scalar extension comparison on a pro-etale slice; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pod-point-extension-kflat: the existing node concerns K-flatness of the point extension of a flat-term module complex; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-coefficient-pullback-comparison: the existing lemma constructs generic ordinary and derived comparison data only; the new lemma identifies those maps with the specified adic tau and quotient normalizations and fixes their concrete models.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-etale-scalar-flat-kflat-comparison: the existing node concerns Native flat-term K-flat étale complexes in scalar coordinates; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-etale-scalar-pullback-existence: the existing node concerns Existence of normalized derived scalar/pullback comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-etale-scalar-pullback-uniqueness: the existing node concerns Uniqueness of normalized derived scalar/pullback comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-external-rhom-evaluation-naturality: the existing node concerns Four-variance naturality of the external evaluation transpose; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-integral-ambient-operation-models: the existing node concerns Ambient completion presentations for integral pullback and tensor; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-integral-operations-well-defined: the existing node concerns The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-kflat-change-of-rings: the existing node concerns Change of rings preserves K-flat complexes with flat terms; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-kflat-change-of-rings-all-independent: the existing node concerns Change of rings preserves all K-flat complexes with independent coefficient universe; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-kflat-change-of-rings-independent: the existing node concerns Change of rings preserves K-flat complexes with flat terms in independent universes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-normalized-scalar-comparison-realization: the existing node concerns Normalized realization of scalar comparisons on quotient systems; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-quotient-expression-kflat-normalization: the existing lemma assumes DVR coefficients and gives strict expression transitions; the new lemma works for the general Noetherian adic datum and pins the constant/completed comparison and its pulled scalar mate.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-quotient-system-flat-models: the existing lemma constructs whole semilinear system tensor/pullback models; the new lemma also handles constant/completed coefficient restriction and fixes tau and the inverse-oriented pulled quotient mate.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-scalar-tensor-pullback-normalization: the existing node concerns Scalar/tensor pullback normalization on a K-flat representative; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-pur-varying-ring-tensor-comparison: the existing node concerns Normalized tensor comparison for one varying-ring inverse image; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-boundary-bounded-tensor-comparison: the existing node concerns Bounded tensor preparation for the boundary direct-image comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-canonical-open-restriction-model: the existing node concerns Canonical open restriction on augmented quotient models; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-open-operation-models: the existing node concerns Open operation comparisons with fixed tensor models and right square; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-open-pullback-support: the existing node concerns Derived pullback preserves open support; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-open-restriction-completeness: the existing node concerns Completeness and the actual completion unit after ordinary open restriction; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sf-scalar-pullback-composition: the existing node concerns Composition coherence of normalized scalar/pullback comparisons; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-constant-module-kflat: the existing node concerns Constant realization preserves flat-term K-flat complexes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-constant-realization-derived-scalar-extension: the existing node concerns Derived constant realization commutes with derived scalar extension; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-flat-term-kflat-functor: the existing node concerns Flat-preserving colimit functors preserve flat-term K-flat complexes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-internal-scalar-mate-transitivity: the existing node concerns Successive internal coefficient mates and normalized scalar units; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-internal-scalar-pullback-normalization: the existing lemma compares generic condensed scalar/pullback operations; the new lemma identifies constant/completed adic restriction, the strict tau and successive quotient maps on the explicit models.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-kflat-scalar-comparison-normalization: the existing lemma identifies a single generic scalar mate; the new lemma combines it with the constant/completed finite comparison to identify strict tau and both normalization model maps.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-ringed-site-point-kflat-resolution: the existing node concerns K-flat resolution with K-flat stalk; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-scalar-extension-kflat: the existing node concerns Scalar extension preserves all K-flat sheaf complexes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sfb-successive-derived-quotient-normalization: the existing lemma gives scalar associativity only; the new lemma additionally computes restricted/pulled models and pins the strict tau and pulled scalar mate.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-sp-bounded-flat-coefficient-site-square: the existing node concerns Bounded-flat coefficient/site square with its canonical derived comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-trf-ringed-kflat-word-comparison-descent: the existing lemma lifts ordinary natural transformations along finite words; the new lemma additionally handles restriction along the flat constant/completed map and identifies the concrete strict tau and quotient mate on four adic models.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-etale-native-tensor-pullback: the existing node concerns Native unbounded derived tensor commutes with etale inverse image; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-cochain-pullback-tensor-shift: the existing node concerns The prescribed cochain pullback tensor comparison commutes with both signed shifts; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-completed-adic-koszul-kflat: the existing node concerns K-flatness of the actual completed exterior Koszul complexes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-constant-derived-normalization-universal: the existing node concerns Constant derived realization preserves universal coefficient arrows; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-derived-scalar-extension-local-systems: the existing node concerns Coherent localized derived scalar extension and comparison; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-diagram-kflat-replacements: the existing node concerns Objectwise K-flat replacements in strict diagram categories; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-flat-coefficient-reduction-adjunct: the existing lemma supplies the finite scalar comparison and its adjunct property; the new lemma also constructs the pulled models and identifies the two different normalization maps.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-kflat-tensor-pullback-computation-universes: the existing node concerns Derived pullback computes K-flat tensor representatives; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-normalized-derived-isomorphism-transport: the existing node concerns Universal normalization and evaluation of source-site local Isom sheaves; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-pullback-resolving-computation: the existing node concerns Derived pullback computes on resolving complexes with independent universes; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-pulled-reduction-normalization-comparison: the item also asserts the square, triple/unit coherence and full representative independence; the new model lemma extracts only the construction and identification of its concrete flat models and maps (base steps 1–4), as required by the human re-split note.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-common-quotient-pullback-comparison: the existing lemma gives insertion and finite-reduction isomorphisms with geometric composition coherence; the new lemma identifies all four simultaneous models and the specified strict tau, inverse-oriented quotient mate and thetaH/thetaN formulas.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-pullback-preserves-kflat: the existing lemma states generic preservation only; the new lemma also proves restricted K-flatness and identifies all concrete adic comparison and normalization maps.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback: the existing node concerns Derived tensor comparison for arbitrary ringed topoi; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-existence: the existing node concerns Canonical tensor comparison unit existence; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topoi-derived-tensor-pullback-unit-uniqueness: the existing node concerns Canonical tensor comparison unit uniqueness; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topos-acyclic-kflat-pullback: the existing node concerns Ringed-topos pullback in the acyclic K-flat case; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topos-kflat-pullback: the existing lemma states generic preservation only; the new lemma also proves restricted K-flatness and identifies the specified tau and both quotient normalization maps.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution: the existing node concerns A flat resolution whose ringed-topos pullback is K-flat; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: the existing node concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-point-derived-tensor-tower-coherence: the existing node concerns Ordinary derived scalar associators and point sections-tensor tower coherence; the new lemma additionally fixes the four constant/completed adic models and the specified strict tau and inverse-oriented thetaH/thetaN maps, which that statement does not jointly give.

lem-weil-pbc-pulled-reduction-generator-descent vs def-pur-external-rhom-pairing-interface: the existing node defines an external Hom pairing interface; the new node is a theorem about concrete quotient tensor maps and their derived descent.

lem-weil-pbc-pulled-reduction-generator-descent vs def-sfb-condensed-pullback-tensor-comparison: the existing node defines the normalized binary tensor comparison; the new node asserts the concrete quotient comparison square, triple, unit and resolution independence.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-etale-scalar-flat-kflat-comparison: the existing lemma identifies two K-flatness conventions; the new lemma computes and descends explicit quotient normalization maps.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-external-rhom-derived-braiding: the existing lemma compares the native localization braiding; the new lemma gives coefficient quotient square/triple/unit identities for the specified adic maps.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-external-rhom-signed-cones: the existing lemma transports signed coefficient cone triangles; the new lemma computes the adic quotient square/triple/unit without external Hom or cone hypotheses.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-finite-product-derived-tensor-calculus: the existing lemma concerns finite clopen decomposition and monoidal gluing; the new lemma concerns quotient normalization between constant/completed pullback models.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-flat-term-kflat-map-factorization-native: the existing lemma gives abstract flat-term factorization for one map; the new lemma asserts the actual quotient generator equations and their coherent derived identifications.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-global-hom-evaluation-flat-lift: the existing lemma constructs an evaluation chain map and a K-flat lift; the new lemma computes quotient generators and descends their square and cocycle.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-pur-kflat-map-factorization: the existing lemma factors one chain map through a K-flat target; the new lemma requires the concrete adic generator equations and their simultaneous natural descent.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-sfb-condensed-support-projection-formula: the existing lemma is a support projection formula for an open/closed pair; the new lemma computes quotient generator identities independently of supports.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-sfb-ringed-equivalence-resolving-tensor-descent: the existing node concerns Transfer of ringed-site resolving tensor localization across an exact equivalence; the new lemma additionally asserts the displayed adic generator square/triple/unit and its specified derived descent.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-weil-completed-scalar-shift-descent: the existing lemma descends shifts for extension of coefficient fields; the new lemma descends a finite quotient normalization square, triple and unit for arbitrary adic K.

lem-weil-pbc-pulled-reduction-generator-descent vs lem-weil-pbc-site-derived-tensor-descent: the existing lemma is the generic localization equivalence and tensor transformation extension; the new lemma requires the explicit adic square/triple/unit equations and their identification under separate scalar and pullback resolution comparisons.

lem-weil-pbc-pulled-reduction-flat-model-formulas vs lem-weil-pbc-pulled-reduction-generator-descent: the first constructs and identifies the models/maps; the second assumes those specified maps and proves their diagram equations and descent. Neither repeats the whole item.
