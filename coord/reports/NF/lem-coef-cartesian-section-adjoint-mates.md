## Worker report

Repaired the 2026-10-22 long-proof return for lem-coef-cartesian-section-adjoint-mates. The sandbox initially contained only dispatcher marker files, with no retained delivery nodes, report, citations or searches. I copied the current read-only repository item, whose 17-step proof matches the returned 13738-character argument, and retained that entire baseline as returned-node.json. No repository or launcher file was written and no git command, compiler or Lake command was run by this worker.

The item's statement, statement dependencies, imported metadata and blueprint ancestry are retained. Its proof is now a six-step assembly of 2441 characters. This delivery adds six statement-only nodes, all status unsplit, with empty proof/proof_deps and null proof_origin/mathlib_match. There are no new Mathlib leaves. The new nodes are separate arguments, not six copies of the parent: they respectively construct projection data, identify free-insertion mates, descend an already-given adjunction, represent mapping systems, enrich an already-given adjunction, and compare actual transposes. In particular the descent and enrichment statements have explicit prerequisite adjunctions; neither asserts the whole parent from scratch.

## Return repaired

The return has one substantive point: spread all 17 old arguments across at least four new unsplit nodes, keeping the parent statement and limiting its assembly to 3000 characters. Six new nodes meet that point. The original arguments have not been shortened or erased: the assignment table below allocates every step, and the final section reproduces each old step verbatim with its source and cited nodes. These retained arguments are proof material for the future workers, not proof fields of the new unsplit nodes. The old individual step sizes range from 297 to 1311 characters; the allocated groups have comparable total work, rather than moving the whole argument into one child.

## New nodes

- lem-coef-system-compact-support-projection: Unbounded strict-system compact support and its projection comparison. Returned steps 1, 2, 3; 2569 characters of retained argument. Status unsplit.
- lem-coef-free-insertion-compact-support-coherence: Free-insertion comparison detects exceptional quotient mates. Returned steps 4, 5, 6; 2613 characters of retained argument. Status unsplit.
- lem-coef-levelwise-normalized-adjoint-descent: Descent of an evaluated adjunction without a common level bound. Returned steps 7, 8, 9, 10; 3151 characters of retained argument. Status unsplit.
- lem-coef-system-internal-hom-representability: Sequence-site internal Hom and punctual representation of mapping systems. Returned steps 11, 12; 2270 characters of retained argument. Status unsplit.
- lem-coef-system-enriched-projection-adjunction: Enriched system adjunction from the actual counit and projection. Returned steps 13, 14, 15; 1806 characters of retained argument. Status unsplit.
- lem-coef-system-adjunction-transpose-coherence: Resolution-normalized tensor transposes and mates of system adjunctions. Returned steps 16, 17; 1329 characters of retained argument. Status unsplit.

## Sources and route

I read the actual main-20261015 prop-coef-integral-exceptional-adjoint.proof.md, in particular the middle three-line RHom calculation and final paragraph about finite units/counits before derived limit, together with the master lem-coef-finite-exceptional.md statement and proof. I also read the chapter and unit records sec-six-functors and sk-prop-sf-biduality-general. The node-level construction is an agent refinement of that calculation, not a theorem verbatim in Stacks: the new source places say this explicitly. Each of the six source places records exactly which returned steps it separates. No forbidden source is used for the repair. The old source of the parent remains unchanged.

For projection I opened the statements of lem-amb-proper-coproducts-projection (unbounded ordinary etale projection, with no Tor bound), lem-pur-system-level-left-extension (componentwise coproducts and conservative derived evaluations), and lem-pur-coefficient-system-derived-comparison (actual derived system adjunctions and counit-compatible evaluations). For free insertion I read the full statement of lem-pur-coefficient-evaluation-derived-left-adjoint, including its sigma precomposition formula, and lem-pur-etale-coefficient-system-adjoint, which already supplies the ambient exceptional adjoint and counit-compatible finite comparisons. For descent I read lem-sfb-unbounded-site-comparison and lem-sfb-unbounded-direct-image-comparison, which actually state unbounded comparison, and lem-coef-finite-exceptional, which states the invertible finite coefficient mate, its cocycle and its unit/counit equations. The bounded-below last clause of the ordinary comparison theorem alone would not suffice here. For Hom representation I opened lem-coef-derived-system-evaluation-calculus, including its actual system evaluation and definition of H, and thm-sf-hom-comparison-constructible, whose first input has finite Tor amplitude. For enriched adjunction I read prop-asd-internal-adjunction (the unbounded finite etale internal adjunction). For final mate coherence I read the four clauses of lem-weil-pbc-mate-pasting. These sources motivate the new open arguments; the old detailed citations are retained below rather than falsely marking the new nodes proved.

## Searches and attachment check

I searched lean/WeilConjectures for the exact blueprint tag and the notion of cartesian sections, and searched the SixFunctors/CategoryTheory sources for coefficient-system adjoints. The isolated cartesian-section hit in LowerShriek/MorphismDefs.lean concerns extension-by-zero base change, not this theorem. AdicSystem.lean and related coefficient-change files discuss finite perfect towers, not all the clauses of this ordinary system adjunction. There is no exact project declaration to attach. I also searched the proposed new notions there before creating them.

Whole-DAG statement/title searches used free insertion, system projection, mapping-system isomorphism, internal-Hom identification, etale-origin levels and tensor-Hom transposes. Blueprint searches were made with tools/blueprint_refs.py for free insertion, system projection, normalized systems, mapping systems, ordinary mates and each of the six more specific phrases saved in blueprint-searches.txt. None states a proposed new argument. The ancestor command identifies prop-coef-integral-exceptional-adjoint; all six new from.via lists start with this item then lem-coef-finite-adjunction-diagram-realization. Existing same_as is empty and remains so.

For every new node, I ran LeanFinder with two different phrasings, LeanSearch, Loogle, and grep through the required msearch.py. Exact output, including hit types and source line numbers, is retained in search-results/, and the required command log is searches.jsonl. I read the hits: Evaluation.lean:38-70 gives ordinary functor-category evaluation, not quotient-semilinear derived free insertion; Mates.lean:84-140 and :170 onward gives ordinary mates and pasting, not their actual coefficient-system realization; Functor/Derived/Adjunction.lean:52 onward concerns derived adjunctions under existing derivation hypotheses; Monoidal/Closed/Basic.lean:305 gives a closed-category parametrized adjunction, not normalized system Hom evaluation. The other semantic hits concern standard etale presentations, condensed/locally constant adjunctions, adic algebra, rigid duality and ordinary linear tensor-Hom. None gives any of the new statements in one specialization. LeanSearch returned rate-limit/unavailable for the descent and internal-Hom queries; both are recorded as unavailable, with successful LeanFinder, Loogle and source grep covering them. No unrun search was recorded. The parent's earlier search records remain intact.

## Not duplicates

lem-coef-system-compact-support-projection vs lem-pur-etale-coefficient-system-adjoint: the existing node gives the exceptional right adjoint and its evaluation; the new node supplies the actual unbounded system projection and coefficient-change construction, without a new right-adjoint existence assertion.
lem-coef-system-compact-support-projection vs lem-amb-proper-coproducts-projection: the existing theorem is a single fixed finite-coefficient etale proper morphism; the new theorem concerns strict varying-coefficient systems, open/proper composition and its actual quotient maps.
lem-coef-system-compact-support-projection vs lem-pur-system-level-projection-formula-coherence: that node proves composition coherence for already realized normalized pro-etale compact supports; the new theorem establishes the unbounded etale system projection and its invertibility. Citing the downstream coherence realization for existence would be circular.
lem-coef-free-insertion-compact-support-coherence vs lem-pur-coefficient-evaluation-derived-left-adjoint: the existing node constructs L_n and sigma for one topos; it does not compare them with compact support or specify the resulting exceptional mate under that comparison.
lem-coef-free-insertion-compact-support-coherence vs lem-pur-etale-coefficient-system-adjoint: the latter already supplies the adjoint, which the new node assumes; the new statement fixes the actual a_n comparison, its sigma equation and the representing Hom normalization producing the specified transition formula.
lem-coef-levelwise-normalized-adjoint-descent vs lem-pur-coefficient-system-derived-comparison: the latter's essential-image conclusion assumes one global bounded-below system; the new conclusion permits only separate bounds at individual levels and transports an exceptional compact-support adjunction using unbounded site comparison.
lem-coef-levelwise-normalized-adjoint-descent vs lem-coef-finite-exceptional: the finite node has no actual ordinary derived-system site descent or adjunction restriction assertion.
lem-coef-system-internal-hom-representability vs lem-coef-derived-system-evaluation-calculus: the existing node supplies the fiberwise I and H and their evaluation maps; the new theorem identifies I with sequence-site internal Hom and supplies punctual etale coefficient-system representability and its sections comparison.
lem-coef-system-internal-hom-representability vs lem-coef-semilinear-system-existence: the generic calculus gives cartesian fiber Hom evaluation, but does not assert finite-Tor etale/pro-etale Hom descent and the global representing coefficient system.
lem-coef-system-internal-hom-representability vs lem-coef-finite-hom-site-descent: the latter proves finite scalar/site comparison, not sequence-site internal Hom and global mapping-system representation.
lem-coef-system-enriched-projection-adjunction vs lem-coef-closed-adjunction-enriched-isomorphism: the latter assumes a strong tensor comparison for F itself, and identifies internal H against G H. Here compact support has a projection formula relative to coefficient-point action; it is not assumed strong monoidal. The conclusion is an evaluated coefficient-system mapping adjunction with fixed finite counit normalization.
lem-coef-system-enriched-projection-adjunction vs lem-coef-finite-mapping-adjunction: the finite node does not construct maps and inverse identities of ordinary derived coefficient systems before total inverse limit.
lem-coef-system-adjunction-transpose-coherence vs lem-weil-pbc-mate-pasting: ordinary pasting is already available and is part of the retained argument, but does not identify the simultaneous derived tensor/Hom resolution models or their actual finite evaluation maps.
lem-coef-system-adjunction-transpose-coherence vs lem-coef-sequence-adjunction-cochain-transposes: that node describes the specific reduction/total-limit adjunction's cochain formulas, whereas the new node compares actual compact-support adjunction mates and tensor transposes across finite evaluation.
lem-coef-system-adjunction-transpose-coherence vs lem-coef-finite-scalar-mate-realization: the latter is an integral finite-free scalar-extension comparison after a completed adjunction; the new theorem is before total inverse limit, for specified transformations of actual system functors, and assumes neither a scalar field extension nor an integral realization.

## Review by NF

I checked the parent statement clause by clause against the six written statements, rather than treating equality at every evaluation as faithfulness on morphisms. The parent remains verbatim. Step 1 cites the new projection theorem for F, coproducts, q and projection, and the existing etale-system adjoint theorem for actual G, eta, epsilon and triangles; its source statement explicitly includes the ambient unbounded adjunction and map action. Step 2 cites the free-insertion theorem for the sigma equation, counit-normalized representing bijections, both evaluated adjunction maps and exactly the displayed transition word. It cites the projection theorem only for F's transition. The types in the sigma equation start at L_n F_n T_{m,n} and end at F L_m: the inverse q is essential. No conclusion about arbitrary system arrows follows merely from evaluating them.

Step 3 uses precisely the descent theorem's conclusion: first assume the already constructed ambient adjunction and its transition formulas, then obtain preservation and the etale/pro-etale equivalences without a global bound. Finite rings are R/(varpi^n), killed by powers of ell, ell is invertible on the schemes, the schemes and compactification are finite type and Noetherian, and finite dimension gives the finite-Tor proper-image hypothesis separately for each level. This conclusion does not postulate an ambient pro-etale exceptional adjoint. The finite mate's invertibility and identity/cocycle are restricted to finite-Tor constructible inputs, not asserted for arbitrary ambient inputs.

Step 4 uses the internal-Hom representability theorem's actual tensor comparison and its statement about I, punctual etale sections and the underlying pro-etale mapping tower. The normality hypothesis here is cartesian coefficient transitions, not normal schemes. Both relevant inputs have the required finite-Tor/constructible levels from step 3; only the first input's normalization is needed for the raw internal-Hom evaluation. The base is Spec of the algebraically closed k, so the etale coefficient point is punctual. Pro-etale global sections were not replaced by coefficient-forgetting: the theorem explicitly supplies the site/sections comparison.

Step 5 uses the enriched theorem under projection from step 1, adjunction from step 3 and representability from step 4. Its statement gives the actual inverse equations, counit normalization, finite mapping-complex evaluations and both degree-zero formulas; it therefore proves each part taken from it. Its derived-limit assertion is applied only after those system maps exist. Step 6 uses the coherence theorem for specified transformations between actual system left adjoints and for simultaneous flat-term K-flat tensor transposes; all its evaluation and closed-Hom hypotheses are the preceding constructed data. It says nothing about lifting unrelated finite transformations. citations.json quotes the complete verbatim statement for every cited node in every one of these steps, so there are eight explicit C4 witnesses.

For each new statement I checked the identified source place above and its precise role in the retained proof. B1: new nodes have no proof, proof dependencies or proof sketch in the statement. B2/B3: their common preamble defines the field, coefficient ring, uniformizer, quotient indices, morphism, compactification, sites, strict systems, evaluation and reduction maps; additional adjunctions, normalization, finite-Tor conditions, internal Hom, tests and comparison morphisms are explicitly introduced, with statement dependencies naming the existing notions. B4: TeX is written once in Python raw strings and JSON encoded, not double-escaped. B5/B7: these are explicitly agent-formulated blueprint refinements, not misattributed standalone Stacks theorems or statements defined by tag numbers. B6/B8: no false Mathlib leaf is asserted. B9: ancestry and exact blueprint proof places are filled. B10: no exact closed upstream attachment was found.

C1-C4: the assembly has only short, non-elementary cited applications, with no hidden passage from finite evaluations to equality of system maps; the new workers receive all old arguments verbatim. C5: the named existing candidates above were opened and distinguished, including the existing ambient adjoint and generic Hom calculus. C6: no child depends on the parent; the six are available for independent work, with their conditional hypotheses stated explicitly and no proof-dependency edges among them. C7/C8: the assembly remains in the item's unit; the older cross-unit foundational tools occur only in the archived argument and the statements' notion dependencies, rather than a replacement route. No maintainer tool_uses field was added.

D1/D2: no new node repeats the full conclusion, and their prerequisite hypotheses and outputs differ. The descent theorem deliberately assumes the ambient adjunction rather than re-proving existence; enrichment assumes the actual adjunction, projection and representing Hom. D3-D5: every old construction, quotient comparison, representability calculation, sigma identity, cocycle computation, site descent, tensor model and mate argument is present in the preserved allocation below. In particular no 'standard' passage was silently deleted to reach the character limit.

E: I checked n=1 and m=n (L_n has zero levels above n, a_n at level n is identity, q and b at equal indices are identities and b uses the triangle equation), triple quotients (the cocycle is in the descent statement and the old explicit mate computation is retained), f=id (ordinary identity adjunction and projection), empty X and zero systems (zero compact support/adjoint and zero mapping objects), arbitrary ramified E (powers of varpi, never powers of ell), and levels with no common cohomological interval. The closed-Hom comparison requires normalization of its first input; the finite site comparison uses finite Tor there. After the first successful dry run I also made the quotient index range m >= n >= 1 explicit in every new statement and regenerated the quotes; this prevents reading a quotient map in the reverse direction. Actual units, counits and representing bijections, not joint conservativity on arbitrary maps, justify inverse equations. No imported statement correction was necessary. The first dry run detected that the new statements had their notion references only in stmt_deps. I repaired all six by inserting explicit inline definition/theorem references at the notions they introduce, and refreshed citations.json to quote the revised statements. The substantive repair is the six-node decomposition and explicit proof-material allocation; I did not merely summarize or re-push the returned argument.

## Complete retained proof material

The following is the returned argument verbatim, including every original step, source and cited node. Its assignment to the new open arguments is explicit. Its mathematical claims remain work for those nodes; this appendix is not a new proof field and does not mark them split.

### lem-coef-system-compact-support-projection

Returned step 1:

First work on the small etale sites. Denote their strict $A_\bullet$-module system categories by $\mathscr S_W^{\mathrm{et}}$. They are module categories on the ringed topos of inverse sequences, hence Grothendieck abelian by the ringed-site theorem. The ordinary system inverse/direct-image theorem constructs $P_u\dashv S_u=Ru_{*,\bullet}$ on unbounded derived categories, with $e_nS_u\cong Ru_{*,n}e_n$ including the evaluated units and counits. Exact open extension $J_j\dashv P_j$ applies termwise. Thus $F=S_pJ_j$ is an actual exact functor on $D(\mathscr S_X^{\mathrm{et}})$ and $e_nF=F_n^{\mathrm{et}}e_n$ on this entire unbounded category. No assertion on unrestricted pro-etale compact supports is needed.

Cited nodes: lem-pur-ringed-site-grothendieck-abelian, lem-pur-coefficient-system-derived-comparison, lem-pur-site-restriction-module-adjunction-exact, lem-sf-exact-functor-derived-triangulated, lem-pc-right-derived-functor-triangulated, lem-pur-system-level-left-extension.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Ordinary ringed system operations; preparation for the middle RHom calculation"}.

Returned step 2:

For a family $(K_i)$ the canonical sum map $\bigoplus_i FK_i\to F(\bigoplus_i K_i)$ evaluates to the corresponding finite compact-support sum map: $J_j$ preserves sums because it is a left adjoint, and proper etale derived direct image preserves sums for module coefficients. Evaluations are exact and coproducts of systems are levelwise, so this map is an isomorphism. Brown representability for the unbounded derived category of a Grothendieck abelian category now gives $F\dashv G$ on the ambient etale system categories. Its unit $\eta$ and counit $\epsilon$ already are natural derived system maps with triangle identities.

Cited nodes: lem-pur-coefficient-system-derived-comparison, lem-etale-proper-derived-lower-star-coproducts-for-grothendieck, lem-grothendieck-derived-brown-right-adjoint, lem-pur-system-level-left-extension.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Brown construction of the system adjunction; Stacks 0F5Y and etale-cohomology Tag 0F0D"}.

Returned step 3:

Put $L_n=LE_n\dashv e_n$ as in the coefficient-evaluation theorem. Thus $(L_nK)_r=K\otimes^L_{A_n}A_r$ for $r\le n$, zero otherwise; in particular $e_nL_n=1$. Use its actual maps $\sigma_{m,n}:L_nT_{m,n}\to L_m$. The system tensor operations, including their projection maps, are formed on the ringed sequence site by K-flat resolutions and the inverse-image/direct-image counits. The proper projection map for $S_p$ evaluates to the finite etale projection map, which is invertible on all unbounded finite-coefficient inputs. Exact open extension has its tensor comparison. Consequently the actual compact-support projection map is invertible on the etale system category, by conservative evaluation. Applying it to a constant coefficient module $A_r$ also gives the unbounded finite coefficient-change maps $q_{n,r}$. The coefficient-change target is the ordinary etale one: derived extension and exact restriction are adjoint, and their commutation with geometric pullback identifies the two composites of right adjoints by counit-compatible uniqueness. Open extension commutes with restriction termwise. Thus the projection with $A_r$ gives the changed-coefficient compact support, not merely its underlying $A_n$-complex.

Cited nodes: lem-pur-coefficient-evaluation-derived-left-adjoint, lem-pur-coefficient-system-derived-comparison, lem-weil-pbc-ringed-projection-mate-exact, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-amb-proper-coproducts-projection, lem-pur-site-restriction-module-adjunction-exact, lem-pc-kflat-resolution, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-ringed-topoi-derived-pullback, lem-pc-derived-adjoint-functors, det-sp-unique-right-adjoint, lem-pur-system-level-left-extension.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "System projection construction; Stacks 06YS and 0F0G"}.

### lem-coef-free-insertion-compact-support-coherence

Returned step 4:

Define $a_n:L_n^YF_n^{\mathrm{et}}\to FL_n^X$ as the $L_n^Y\dashv e_n^Y$ transpose of the identity $F_n^{\mathrm{et}}=e_n^YFL_n^X$. This is an actual system transformation. At $r\le n$ its component is the coefficient-change projection $q_{n,r}$, by the counit definition of that projection; above $n$ both sides vanish. Thus $a_n$ is invertible. The maps $a_n$ also respect the $\sigma_{m,n}$: explicitly the two maps from $L_nF_nT^X_{m,n}$ to $FL_m$ are $F(\sigma^X_{m,n})a_n$ and $a_m\sigma^Y_{m,n}L_n(q_{m,n}^{-1})$. Under $L_n^Y\dashv e_n^Y$ both transpose to $q_{m,n}^{-1}$, using the displayed formula for precomposition with $\sigma$ in the evaluation theorem. Equality follows from this adjunction bijection, without faithfulness of evaluation on arbitrary maps.

Cited nodes: lem-pur-coefficient-evaluation-derived-left-adjoint, lem-weil-pbc-ringed-projection-mate-exact, def-weil-pbc-adjunction-mate.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Derived free insertion comparisons and their truncation compatibility"}.

Returned step 5:

For every $K\in D(X_{\mathrm{et}},A_n)$ and $N\in D(\mathscr S_Y^{\mathrm{et}})$ compute naturally
$$\operatorname{Hom}(K,e_nGN)=\operatorname{Hom}(L_nK,GN)=\operatorname{Hom}(FL_nK,N)\cong\operatorname{Hom}(L_nF_nK,N)=\operatorname{Hom}(F_nK,N_n).$$
The final functor is represented by the finite etale right adjoint $G_n^{\mathrm{et}}N_n$ (the same Brown argument at one level). Yoneda gives a natural isomorphism $\theta_n:e_nG\cong G_n^{\mathrm{et}}e_n$. Fix precisely this isomorphism. The defining equality identifies the evaluated counit with $\epsilon_n$; uniqueness of the counit-compatible identification of right adjoints leaves no choice of signs or automorphisms. The existing etale coefficient-system adjoint theorem supplies these same ambient finite adjoints and counit-compatible evaluations. On finite constructible inputs their pro-etale transports are exactly the definition of $Rf_n^!$; finite-Tor preservation is a separate theorem, used next.

Cited nodes: lem-pur-coefficient-evaluation-derived-left-adjoint, lem-grothendieck-derived-brown-right-adjoint, lem-etale-proper-derived-lower-star-coproducts-for-grothendieck, lem-galois-yoneda-hom-bijection, det-sp-unique-right-adjoint, lem-coef-finite-exceptional, lem-pur-etale-coefficient-system-adjoint, def-weil-exceptional-inverse-image.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Identification of the levels by representability, not a lift of finite functors"}.

Returned step 6:

Precompose the Hom calculation of the preceding step with $\sigma_{m,n}$. The evaluation theorem says that on its left this is $h\mapsto t^{GN}_{m,n}T^X_{m,n}(h)$. On its right the compatibility of $a$ with $\sigma$ says that it is $h\mapsto t^N_{m,n}T^Y_{m,n}(h)q_{m,n}^{-1}$. Transposing by $F_n\dashv G_n$ therefore identifies the actual reduction map of $GN$ with
$$G_n(t^N_{m,n})b_{m,n,N_m},\qquad b_{m,n}=G_n(T^Y_{m,n}\epsilon_m)G_n(q_{m,n,G_m}^{-1})\eta_{n,T^X_{m,n}G_m}.$$
This identity is determined on every test $K$ in the Hom calculation, hence by Yoneda. Changing from the Brown finite adjoints to the specified constructible ones conjugates this formula by their counit-compatible isomorphisms, exactly as in the unique-adjoint coefficient theorem. Evaluating the actual unit gives $\eta_n$ too: under the same Hom calculation it is the transpose of $1_{F_nM_n}$.

Cited nodes: lem-pur-coefficient-evaluation-derived-left-adjoint, def-weil-pbc-adjunction-mate, lem-galois-yoneda-hom-bijection, det-sp-unique-adjoint-coefficients, det-sp-unique-right-adjoint.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Transitions and unit from the derived evaluation adjunctions"}.

### lem-coef-levelwise-normalized-adjoint-descent

Returned step 7:

On bounded constructible finite-Tor levels, the finite exceptional theorem identifies this $b$ with its canonical invertible coefficient comparison and supplies the two unit/counit mate identities. The compact-support comparisons $q$ and the formula for the reduction maps of $F$ are the projection comparisons of the system operations. Consequently normalized inputs are sent to normalized outputs by both $F$ and $G$: their reduction maps are composites of the displayed invertible maps. Finite constructibility and finite Tor amplitude are preserved separately at each $n$ by exact open extension followed by proper finite direct image, and by the finite exceptional preservation theorem. For the former use lem-trf-open-ctf and cor-sf-direct-image-ctf-proetale on the finite-dimensional compactification; for the latter use thm-sf-preservation-class. No uniform bound is used. This restricts the actual ambient adjunction to the stated full subcategories. These are the levelwise-finite subcategories in the statement, not the uniformly bounded subcategories of sk-def-sp-normalized-towers.

Cited nodes: lem-coef-finite-exceptional, cor-sf-direct-image-ctf-proetale, lem-pur-coefficient-system-derived-comparison, def-coef-normalized-dvr-tower, lem-trf-open-ctf, thm-sf-preservation-class, def-weil-exceptional-inverse-image, lem-kun-dimension-finite-type.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Restriction to normalized finite-Tor constructible systems"}.

Returned step 8:

The mate cocycle can also be checked independently. For $k\ge m\ge n$, transpose $b_{m,n,T_{k,m}N}T_{m,n}(b_{k,m,N})$ under $F_n\dashv G_n$. Ordinary mate pasting gives the composite $T_{m,n}T_{k,m}\epsilon_k$ after $q_{k,m}^{-1}$ and $q_{m,n}^{-1}$. Coefficient associativity and the cocycle of $q$ identify it with the transpose of $b_{k,n,N}$. For $m=n$ the mate word is $G_n\epsilon_n\,\eta_nG_n=1$. This proves the cocycle and identity indices using finite adjunctions. The finite exceptional theorem gives the same canonical cocycle.

Cited nodes: lem-weil-pbc-mate-pasting, def-weil-pbc-adjunction-mate, lem-coef-finite-exceptional, lem-sf-ringed-derived-closed-symmetric-monoidal, lem-pur-derived-change-of-rings.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Mate cocycle and identity indices"}.

Returned step 9:

The system triangle identities hold because $\eta,\epsilon$ were obtained with the Brown adjunction, before restricting objects or evaluating. Explicitly the Hom transposes are $h\mapsto G(h)\eta_M$ and $g\mapsto\epsilon_NF(g)$; their composites reduce by naturality to $h\epsilon_{FM}F\eta_M=h$ and $G\epsilon_N\eta_{GN}g=g$. These are equations in the ambient ordinary derived category of systems. They remain equations on the full normalized subcategories.

Cited nodes: lem-grothendieck-derived-brown-right-adjoint, def-weil-pbc-adjunction-mate.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Actual unit/counit and triangle identities before total limit"}.

Returned step 10:

Apply the unbounded system inverse/direct-image construction to $\nu_W:W_{\mathrm{proet}}\to W_{\mathrm{et}}$. The unit and counit are actual system maps; their evaluations are the finite site-comparison maps. Unbounded finite-coefficient full faithfulness implies that the system unit is invertible. For any system whose every level has etale origin, the counit is likewise invertible, by conservative evaluation. Thus $\nu_W^*$ identifies $D(\mathscr S_W^{\mathrm{et}})$ with the full subcategory of pro-etale derived systems with etale-origin levels. Finite constructible levels have this origin. The actual compact-support comparison $\nu_Y^*F\to Rp_{*,\bullet}J_j\nu_X^*$ is the proper direct-image mate after exact open extension. Its evaluations are invertible by unbounded etale/pro-etale direct-image comparison. Transfer the adjunction and its specified maps along these equivalences. This constructs $\mathcal F_f,\mathcal E_f$ on every system in $\mathscr N$, without a common bound and without postulating a pro-etale ambient exceptional adjoint.

Cited nodes: lem-pur-coefficient-system-derived-comparison, lem-sfb-unbounded-site-comparison, lem-sfb-unbounded-direct-image-comparison, lem-sf-proetale-constructible-origin, lem-pur-site-restriction-module-adjunction-exact, def-weil-pbc-adjunction-mate, lem-pur-system-level-left-extension.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Etale-origin realization of the normalized pro-etale system adjunction"}.

### lem-coef-system-internal-hom-representability

Returned step 11:

We next identify the mapping systems using closed adjunctions on the ordinary ringed sequence sites. For normalized $M$ and arbitrary $N$, let $H^{\mathrm{sys}}_W(M,N)$ be their ringed-site derived internal Hom. Its $n$th evaluation is the finite derived internal Hom. Indeed for a test $K$ on the level-$n$ site the canonical tensor map $L_n(K\otimes^LM_n)\to L_nK\otimes^LM$ is invertible: at $r\le n$ this is normalization of $M$ and tensor associativity, and above $n$ both are zero. The map is the $L_n\dashv e_n$ transpose of the level-$n$ identity, so exists before evaluation. The closed and evaluation adjunctions give
$$\operatorname{Hom}(K,e_nH^{\mathrm{sys}}(M,N))=\operatorname{Hom}(L_nK\otimes^LM,N)=\operatorname{Hom}(K\otimes^LM_n,N_n).$$
For internal sheaf Hom apply this calculation also on each localized site; the same ringed-site statements apply there. Yoneda gives the asserted finite internal-Hom identification, preserving evaluation.

Cited nodes: lem-sf-ringed-derived-closed-symmetric-monoidal, lem-pur-coefficient-evaluation-derived-left-adjoint, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-galois-yoneda-hom-bijection.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Ordinary mapping systems; Stacks 08J9 and 06YS"}.

Returned step 12:

The evaluation calculus supplies an actual system map $\mathcal I_W(M,N)\otimes^LM\to N$. Its closed transpose gives $\mathcal I_W(M,N)\to H^{\mathrm{sys}}_W(M,N)$; the preceding finite-Hom identification shows every evaluation is the identity, so this map is invertible. For normalized etale inputs, the pullback tensor map and evaluation similarly transpose to an actual comparison $\nu_W^*H^{\mathrm{sys}}_{W,\mathrm{et}}\to H^{\mathrm{sys}}_{W,\mathrm{proet}}$. Its evaluations are invertible by thm-sf-hom-comparison-constructible: the first input is finite-Tor and both inputs are bounded constructible at each level. Thus the pro-etale Hom system has etale origin.
Carry out the representing calculation on etale systems. Since $s_{\mathrm{et}}$ is punctual, $\widehat{\mathcal H}_W=Ra_{W,*,\bullet}^{\mathrm{et}}H^{\mathrm{sys}}_{W,\mathrm{et}}(M,N)$ is an ordinary derived $A_\bullet$-module system, representing
$$P\longmapsto\operatorname{Hom}(a_W^*P\otimes^LM,N).$$
This uses the closed and inverse/direct-image adjunctions. The site-comparison unit and derived pushforward composition identify its image in abelian-group towers with the pro-etale mapping system $\mathcal H_W$. Global sections on the pro-etale coefficient point are taken here, not silently identified with forgetting coefficients.

Cited nodes: lem-coef-derived-system-evaluation-calculus, lem-sf-ringed-derived-closed-symmetric-monoidal, lem-pur-coefficient-system-derived-comparison, lem-galois-yoneda-hom-bijection, thm-sf-hom-comparison-constructible, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-pur-system-level-left-extension, lem-sfb-unbounded-site-comparison, lem-weil-pbc-ringed-topoi-derived-pushforward-composition.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Identify the specified fiberwise mapping systems by their actual evaluation maps"}.

### lem-coef-system-enriched-projection-adjunction

Returned step 13:

For an arbitrary test coefficient system $P$ on $s$, the system projection isomorphism constructed above gives $a_Y^*P\otimes^LFM\cong F(a_X^*P\otimes^LM)$. Hence
$$\operatorname{Hom}(P,\widehat{\mathcal H}_Y(FM,N))\cong\operatorname{Hom}(a_Y^*P\otimes^LFM,N)\cong\operatorname{Hom}(F(a_X^*P\otimes^LM),N)\cong\operatorname{Hom}(a_X^*P\otimes^LM,GN)\cong\operatorname{Hom}(P,\widehat{\mathcal H}_X(M,GN)).$$
Every bijection is an actual system adjunction or the system projection isomorphism. It is natural for all $P$, so Yoneda gives a specified mapping-system isomorphism with inverse. Restriction to abelian-group towers gives $\Phi$. The inverse equations follow from the inverse representing bijections, in the ordinary derived category of coefficient systems; no equality is inferred from finite evaluations.

Cited nodes: lem-sf-ringed-derived-closed-symmetric-monoidal, lem-pur-coefficient-system-derived-comparison, lem-galois-yoneda-hom-bijection, lem-amb-proper-coproducts-projection, lem-weil-pbc-ringed-projection-mate-exact.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Middle RHom adjunction as an isomorphism of ordinary derived systems"}.

Returned step 14:

The representing bijections use the actual counit $FGN\to N$ and projection map, so their finite evaluations are the ordinary finite tensor-Hom/counit transposes. This can be read by testing on $L_nP_n$ in the same calculation, rather than lifting a finite transpose. The counit-compatible identifications already fix the finite adjunctions; the standard finite internal adjunction and site comparison identify their derived mapping-complex maps with those in the statement. At degree-zero Hom the forward and inverse maps are $h\mapsto G(h)\eta_M$ and $g\mapsto\epsilon_NF(g)$ by the actual adjunction. Their inverse identities were proved as system identities in the representing calculation.

Cited nodes: lem-pur-coefficient-evaluation-derived-left-adjoint, prop-asd-internal-adjunction, thm-weil-pbc-site-comparison, det-sp-unique-right-adjoint, def-weil-pbc-adjunction-mate.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Specified finite evaluations of the system mapping adjunction"}.

Returned step 15:

Apply the total derived inverse-limit functor to $\Phi$ and its already specified inverse. A functor preserves compositions and identities, so their images are inverse isomorphisms in $D(\operatorname{Ab})$. Naturality and the evaluation/transpose identities are carried along by the same functor.

Cited nodes: lem-coef-derived-system-evaluation-calculus.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Pass to total derived inverse limit only after constructing the system isomorphism"}.

### lem-coef-system-adjunction-transpose-coherence

Returned step 16:

For a specified ordinary transformation between system compact-support functors, take its ordinary adjunction mate using the actual units and counits above. Its evaluation is the finite mate because the identifications preserve those units and counits. For composition comparisons use the composite adjunction; ordinary mate pasting gives the horizontal and vertical composition laws as equalities of derived system transformations. Counit-compatible uniqueness identifies different choices of ambient right adjoints. Thus this applies to the geometric composition maps used by the citers. It makes no claim of lifting transformations specified only at the finite levels.

Cited nodes: def-weil-pbc-adjunction-mate, lem-weil-pbc-mate-pasting, det-sp-unique-right-adjoint.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Naturality and composition by ordinary system mates"}.

Returned step 17:

Finally form tensors on flat-term K-flat system resolutions. K-flat existence, the flat-term K-flat total-tensor model and the ringed-site closed structure make these operations and their evaluation transposes independent of representatives. Composing their actual system maps with $\eta,\epsilon$ and using the system closed-adjunction bijection produces actual tensor-Hom transposes. Evaluation of those composites and bijections is the finite construction by the preceding internal-Hom identification. Their compatibility with transitions is therefore a property of these constructed system maps, rather than a criterion for lifting unrelated finite maps.

Cited nodes: lem-pc-kflat-resolution, lem-sf-ringed-derived-closed-symmetric-monoidal, lem-coef-derived-system-evaluation-calculus, lem-pur-kflat-total-tensor-model.

Source: {"document": "literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md", "place": "Tensor-evaluation transposes on ordinary system resolutions; Stacks 06YS, 08J9, 0A95"}.

