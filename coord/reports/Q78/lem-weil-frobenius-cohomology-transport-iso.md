## Worker report

Repaired the returned stage-1 split, rather than re-pushing the prior zero-node delivery. Files written:

- `dag/nodes/sec-six-functors/lem-weil-frobenius-cohomology-transport-iso.json`: existing statement, split; statement unchanged, 2080-character assembly in three steps.
- `dag/nodes/sec-six-functors/lem-weil-point-automorphism-derived-transport-inverse.json`: new statement, unsplit, no Mathlib match. Explicit inverse of the actual point composite for an arbitrary scheme automorphism, on unbounded finite-coefficient or derived-complete integral inputs.
- `dag/nodes/sec-six-functors/lem-weil-frobenius-finite-exchange-inverse.json`: new statement, unsplit, no Mathlib match. General-morphism finite direct/compact exchange, the inverse of the fixed compactification composite, and conjugation on the witnessed comparison domain.
- `dag/nodes/sec-six-functors/lem-weil-frobenius-system-exchange-inverse.json`: new statement, unsplit, no Mathlib match. Whole-system exchanges on every derived semilinear system, their evaluated inverses, and realization of those inverses as the specified integral exchanges.

Auxiliary evidence: `citations.json`, genuine appended `searches.jsonl`, this report, and retained proof/audit files. All three new nodes have empty proof and proof_deps and null proof_origin; the detailed arguments below are handoffs, not proofs installed in their statements. No Lean or repository file was written. No compiler, Lake, local DAG checker, or git command was run.

Attachments: none. The exact blueprint-tag search and name/concept searches under `lean/WeilConjectures/` found no declaration of this whole item. The project's `lean/Sheaf/SixFunctors/FrobeniusCohomologyTransportIso.lean` was read: its isomorphism theorem at line 588 ends in `sorry` at line 650, and the naturality theorem is also unfinished. Its docstring's nine-step plan is the returned proof, including the now-obsolete summand and inverse-limit language, not a completed attachment. Searches for the three new notions likewise found no exact finished upstream declaration.

WANTED: none.

What was wrong: the previous repair correctly fixed integral pullback, strict-system maps and the nonexistent Karoubi completion, but left zero new obligations. That did not fulfill the explicit human re-split decision. This repair adds three genuinely different subarguments; none states all coefficient stages of a clause of the parent. The parent statement, source, import flags, historical blueprint fields and Lean metadata remain intact, with current live non-split metadata retained. No target statement changes, statement dispute, or unit-route replacement are involved.

The original integral tensor argument was false for the current completed pullback definition. It remains corrected using the specified whole-cone normalization. The inverse-image indexing must be read contravariantly: an initial object of the comma category is terminal in its opposite, which actually indexes the colimit. The obsolete summand paragraph remains replaced by raw scalar localization, since the current definition explicitly has no Karoubi completion. A levelwise family of derived maps is never treated as a system map: the new third obligation concerns the already constructed system mates.

The retained `expanded-proof.json`, `report-expanded-audit.md`, `proof-before-resplit.json`, and `report-before-resplit.md` preserve the earlier work and searches. The full expanded argument is also reproduced below by ownership, with explicit additions for the stronger arbitrary-automorphism and arbitrary-system statements. Nothing is being discarded merely to meet the character cap. Only server validation and push remain to be recorded at the end.

## Source and blueprint review

I read AGENTS, GOAL, the worker brief, the worker role, stage 1, tools/README, the three levels in SETUP, current STATE and both copies of delivery-errors B-E. I read the chapter `sec-six-functors` and historical unit `sk-prop-sf-rf-shriek-preservation`. That unit now lives in six-functors-basics and treats finite-coefficient upper shriek; the item retains its historical placement. Its actual blueprint ancestor remains `def-weil-global-geometric-frobenius`, confirmed by `tools/blueprint_refs.py ancestor`. The current main-20261015 ancestor was opened: the first arrows of both its ordinary and compact-support displayed composites are marked isomorphisms. I also read main-20261015 `lem-trf-frobenius-operator-compact-description.proof.md`, which describes transport along the compact base-change isomorphism.

For the item AND each new node I read the local Deligne, Weil II PDF, (1.1.7), (1.1.10)-(1.1.11), (1.1.14), printed pp. 150-153 (PDF pages 15-18). These give transport of structure on fibres, inverse images, and both sorts of cohomology. They distinguish Galois geometric Frobenius from the scheme power map. The explicit verification in the project's derived coefficient categories is agent work, as the item proof_origin says. These three new source entries identify exactly which old proof work is extracted; none pretends Deligne proves the project's whole-cone or strict-system normalizations. The existing normalization and system nodes supply those precise interfaces, and were opened in full. No SGA source is used.

Whole-DAG statement searches and whole-blueprint searches were made for Frobenius exchange, integral exchange, point automorphism, automorphism transport, restriction insertion, restriction transport, system exchange and finite exchange. The finite-origin/proper finite-exchange blueprint results impose properness or concern an underived finite map; they do not give these unbounded semilinear Frobenius comparisons. The three new names were checked absent before writing. Every new blueprint.from points to the confirmed ancestor with via=[the item], and place explicitly maps the old work; same_as=[] reflects these searches.

## Mathlib searches

All search records come from real `msearch.py Q78 lem-weil-frobenius-cohomology-transport-iso ...` executions. The previous item searches were read and retained without repetition. For each new id the four recorded queries are its own natural-language LeanFinder query, a differently phrased LeanSearch query, a Loogle query and a Mathlib grep. Exact strings, result names, dates, and grep subdirectories are recorded in each node, and query/tool strings agree with searches.jsonl. All services answered for these new searches; none is falsely recorded as unavailable or as an unrun negative search.

For the point inverse, LeanFinder found scheme restriction identifications and `SheafOfModules.conjugateEquiv_pullbackComp_inv`; LeanSearch found ring-section maps of scheme isomorphisms. Loogle gave over-site pullback and sheafification comparisons. I read `Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`, including pullbackComp and its conjugate comparison: these concern ordinary module adjunction compositors, without our specified completion-unit cone, point coprojection or transport inverse. The AlgebraicGeometry grep found no point-automorphism transport.

For finite exchange, LeanFinder found scheme finite-morphism facts; LeanSearch gave `CategoryTheory.mateEquiv`, its unit/counit equations, and a Galois fibre-functor endomorphism result. I read `CategoryTheory/Adjunction/Mates.lean`, including the definition and its warning that a mate of an isomorphism need not be an isomorphism. Loogle gave `Adjunction.toEquivalence` and fully faithful adjunction lemmas; `Adjunction/Basic.lean` around line 676 constructs an equivalence GIVEN invertible unit/counit. None identifies these Frobenius mates or the compact proper/open composite as invertible. The AlgebraicGeometry grep found no Frobenius-exchange result.

For system exchange, LeanFinder found perfection and Witt-vector Frobenius formulas; LeanSearch found the monoidal categorical Frobenius morphism (a different notion), profinite limits and R^0 of an additive functor. Loogle gave Functor.map_isIso and map_inv. I read `CategoryTheory/Iso.lean` lines 493ff: preservation of an ALREADY invertible map is elementary and remains a calculation in the report, not a new leaf obligation. It does not prove invertibility of our actual system mate or compare its evaluated inverse to the finite mate. The CategoryTheory grep found no semilinear-system or Frobenius-limit theorem.

The earlier item audit also read `AlgebraicGeometry/Sites/ElladicCohomology.lean`: its coefficient sheaf and degreewise cohomology groups do not supply these specified four-stage transports. No result is an exact match or a one-line specialization for an entire new node. Generic categorical component facts are not misreported as new geometric Mathlib leaves.

## Not duplicates

lem-weil-point-automorphism-derived-transport-inverse vs lem-weil-point-automorphism-restriction-natural: the existing node gives normalized insertion, linearity and naturality of sigma; the new node asserts the two-sided inverse of the full sigma--specified-kappa composite, finite and completed integral, and identifies its actual inverse. Neither a point pullback object nor naturality alone states that result.
lem-weil-point-automorphism-derived-transport-inverse vs lem-weil-isomorphism-derived-pullback-comparison-normalization: the existing node normalizes kappa on a scheme isomorphism; the new node concerns derived point sections and the colimit restriction/insertion composite, and includes the finite inverse as well. It uses the existing theta normalization, rather than recreating that theorem.
lem-weil-point-automorphism-derived-transport-inverse vs lem-weil-frobenius-point-transport-natural: the existing theorem gives naturality for Frobenius and coefficient extension, without an inverse; the new theorem allows any scheme automorphism and unbounded complete inputs and identifies the inverse of its particular transport. It does not restate the parent's all-stage Frobenius clause.
lem-weil-point-automorphism-derived-transport-inverse vs lem-weil-point-automorphism-transport-scalar-extension: the latter proves scalar-compatibility equations, without asserting the inverse of the specified point composite; the new node does not claim those equations.
lem-weil-point-automorphism-derived-transport-inverse vs lem-trf-integral-point-transport-tower-realization: the latter identifies Frobenius point transport with a tower realization; it does not give the arbitrary-automorphism finite/integral composite inverse here.
lem-weil-point-automorphism-derived-transport-inverse vs lem-trf-integral-point-transport-tower-powers: the latter gives powerwise tower maps and realization/compositor equations for Frobenius, and includes kappa invertibility but not the full point-transport inverse for arbitrary automorphisms and finite/unbounded complete domains.
lem-weil-frobenius-finite-exchange-inverse vs lem-weil-mate-iso-along-equivalences: the latter is abstract category theory. The new node identifies the actual pro-etale Frobenius mates, their coefficient/site equivalences, and chosen proper/open compactification composite and inverse, including its precise witnessed conjugation domain.
lem-weil-frobenius-finite-exchange-inverse vs lem-weil-isomorphism-derived-pullback-equivalence: the latter proves one finite pullback functor is an equivalence, without the specified direct or compact exchanges.
lem-weil-frobenius-finite-exchange-inverse vs lem-trf-open-square-exchange: the latter is the open-extension factor only; the new obligation assembles the general-morphism direct mate and proper/open inverse and handles its fixed compactification coordinates.
lem-weil-frobenius-finite-exchange-inverse vs lem-coef-frobenius-exchange-equivalence: the latter asserts raw RATIONAL compact exchange on bounded constructibles between separated schemes; the new theorem is FINITE coefficient, also direct image, and ambient unbounded, with chosen model and explicit inverse.
lem-weil-frobenius-finite-exchange-inverse vs lem-pod-weil-frobenius-compact-support-exchange: the latter concerns rational/common-stage compact exchange on bounded constructible operation domains; the new node is the finite ambient direct/compact argument and exact chosen-model inverse.
lem-weil-frobenius-finite-exchange-inverse vs fix-lem-exchanges: the latter's geometric squares have k-linear arrows and its direct isomorphism clause requires smooth base change and witnessed coefficient domains. The new square has semilinear Frobenius horizontal arrows, arbitrary ambient finite inputs and no k-linearity premise.
lem-weil-frobenius-finite-exchange-inverse vs lem-sf-native-adic-pullback-frobenius-mates: the latter concerns native continuous adic coefficient MODULE functors and identifies their underived mate; it is not the finite constant-coefficient derived direct/compact result here.
lem-weil-frobenius-system-exchange-inverse vs lem-coef-semilinear-derived-sections: the latter constructs simultaneous operations and proves evaluation conservativity, explicitly without invertibility of arbitrary comparisons; the new node proves invertibility of the specific Frobenius direct and compact system mates and identifies their realized integral inverses.
lem-weil-frobenius-system-exchange-inverse vs prop-weil-pbc-rlim-functoriality: the latter supplies a functor, not invertibility of these whole-system mates. Functorial preservation of inverse identities is only the final calculation, not the new node's whole content.
lem-weil-frobenius-system-exchange-inverse vs def-weil-system-operation-exchange-realization: the latter defines specified maps and source comparisons; the new theorem asserts whole-system and integral inverse identities, which a definition does not prove.
lem-weil-frobenius-system-exchange-inverse vs lem-sf-integral-compactification-system-realization: the latter compares bounded normalized finite-Tor systems with integral operations and their geometric maps; the new result concerns invertibility of the actual Frobenius exchanges on EVERY system, with no such bounds or normalization, then restricts to integral inputs for realization.
lem-weil-frobenius-system-exchange-inverse vs lem-trf-compact-support-system-realization-normalization: the latter pins alpha/beta for compact Frobenius powers and reduction systems; it does not assert invertibility of direct and compact exchanges on arbitrary unbounded system inputs.
lem-weil-frobenius-system-exchange-inverse vs lem-trf-integral-compact-transport-system-mate-pasting: the latter gives a typed power-pasting equation for compact exchanges before evaluation; it does not assert the inverse of either the direct or compact system mate or its integral realization.

All three new nodes vs lem-weil-frobenius-cohomology-transport-iso: the first concerns arbitrary point automorphisms at two coefficient stages and identifies specific inverses; the second concerns general f_0 at finite coefficients; the third concerns maps on whole systems and integral realization. Each is a separate construction argument, strictly below the parent's combination of all stages, structure-map specialization, derived cohomology and naturality. The explicit return asks these existing long arguments to become worker obligations; these are not copied clauses and no single node absorbs the parent.

## Review by Q78

I checked the three extracted source statements against the old nine-step argument, the saved eleven-step corrected expansion and the local sources just named. The point obligation carries the restriction/insertion calculation, scalar action and finite/completed comparison with its exact inverse; the finite obligation carries the ambient mate and chosen compactification argument; the system obligation carries the whole-system invertibility and strict-tower realization. The scalar images, structure-map specialization and cohomology assembly remain in the parent. The detailed handoffs below reproduce every previous argument, with the necessary repairs made explicitly.

Parent step 1 uses the new point inverse statement (sigma and specified kappa, including both inverse identities), `lem-weil-frobenius-square-cartesian` (g_s really is a scheme automorphism), and `def-weil-frobenius-point-transport` (iota is exactly that composite, not an arbitrary isomorphism of endpoints). `def-weil-derived-complete-integral-detailed` supplies completeness of integral constructible inputs. The rationalization definition has identical objects and a scalar-localization functor; the algebraically closed coefficient definition has finite-stage objects and morphism classes whose composition is taken at a common stage. Those statements justify image inverses at E and Qbar. I verified no Karoubi completion or extra completeness hypothesis is inserted into the parent.

Parent step 2 uses the new finite statement on the same fixed compactification, and the new system statement on the actual reduction system of the integral input. Their statements give inverse morphisms, not just componentwise quasi-isomorphisms. The square-exchange definition was opened in full: its e_f and e_f^c are actual derived system maps; its alpha/beta are the specified isomorphisms; it defines rationalization and common-stage exchange in exactly that order. The cohomology-transport definition identifies its two exchanges with f_0=a_{Y_0}. The parent's separated finite-type hypothesis is precisely the hypothesis needed for this specialization; properness is not used. Fullness allows the inverse morphism between the same constructible endpoints. The new finite theorem gives ambient unbounded maps so evaluation of ANY derived system in the third theorem is within its scope.

Parent step 3 uses the cohomology-transport definition's ordered composite with iota; its inverse formula has the factors in reverse order. The point-fibre definition actually defines a functor at every stage, so it preserves both inverse identities. The point-transport naturality theorem explicitly quantifies over all derived morphisms and includes common-stage scalar compatibility. The square-exchange definition says its maps are natural transformations, and the two naturality squares paste along the shared point-pullback edge. Thus no unstated naturality theorem is hidden in 'transport'. The ordinary/compact cohomology definition gives H^i of the derived complexes; applying that functor supplies every integer degree and its naturality. All those node statements were read; citations.json contains verbatim portions for every step/node pair.

For A I checked that the evaluation identification is the one that sends the actual coprojection to identity, that inverse restriction has the opposite site arrow, that c^{-1} is the target scalar action, and that delta lands in GN. The finite tensor inverse is balanced. Integrally the cited theta equation is for the specified entire cone map, with its zero shifted coordinate; its inverse is available for all derived-complete inputs, not incomplete ones. k is algebraically closed, so exact point sections applies. Both statements about linearity and derived naturality are supplied by the existing restriction theorem/normalization; inverse naturality follows by multiplying their naturality equations by the inverses.

For B the horizontal scheme maps are automorphisms even though not k-linear. The finite pullback-equivalence theorem applies since ell is invertible on every k-scheme involved. Its mate argument uses L=L'=Lf^*, G=Lg_Y^*, G'=Lg_X^* and the actual pullback compositor; I checked the full statement of the mate theorem, not just its title. Proper p_0 is a separated finite-type morphism between finite-type k_0-schemes, so the direct argument applies to p. The open square is precisely the one of the Frobenius-open-square lemma; its b is the canonical open exchange. The chosen model Rp_*j_! is defined on the whole ambient derived category, but C_{d,c} is used only when both K and its pullback have the witnessed etale-origin condition. The square-exchange definition supplies the latter witness. No stronger arbitrary compactification independence is asserted.

For C I checked the statement of semilinear-derived-sections in full: e_n is exact and jointly detects isomorphisms; units, counits, open adjunction and mates are formed on ordinary derived categories of systems and evaluate to the finite constructions. These operations permit the same e_f and e_f^c on an arbitrary C, without a normalization condition. Their inverses are therefore system morphisms, and evaluating the TWO inverse identities identifies their finite evaluations. This uses no faithfulness of evaluation on morphisms. Exact U_Y and the real derived strict-tower functor give L_Y, not a separately chosen triangulated cone. The source and target comparison maps are those explicitly named by the square-exchange definition, which specifies bounded constructible domains for integral outputs. The displayed inverse conjugates L_Y(e^{-1}) by exactly those comparisons.

Small cases checked: the empty source, zero sheaf/complex/system, the identity point automorphism, Y_0=Spec(k_0), n=1, an integral torsion object, negative cohomology degrees, and unbounded systems with one nonzero level and zero transitions. The last systems are not normalized, but componentwise conservativity still proves the system result. For the identity point map all restriction, insertion and comparison normalizations give identity on complete objects. For an INCOMPLETE integral object kappa is not asserted invertible; the new A and the parent explicitly avoid that false extension. For a ramified coefficient extension only scalar functoriality, not finite-level equality at equal uniformizer exponents, is used. No finite Tor amplitude or Weil structure is added to an input, and no separatedness of X_0,Y_0 individually is assumed in the general exchange lemmas.

Delivery-errors B-E were checked individually: statement-only new leaves and introduced objects (B1-2); actual notion-defining dependencies and once-escaped TeX (B3-4); real source places and honest Mathlib records, without claiming a generic component as an exact match (B5-8); ancestor/via and no finished declaration attachment (B9-10). Every parent non-elementary claim is a cited node and every cited statement supplies its use (C1-4); duplicate/source searches and no new back-edge to the item (C5-6); no replacement of the ancestor's route (C7-8). Three distinct proof constructions replace the long original argument; no circular restatement or one-node relocation (D1-5). Scheme, coefficient, completeness, witnessed-domain and whole-system hypotheses were checked as above (E1-6); the old integral tensor and Karoubi mistakes are repaired rather than reproduced (E7). Parent steps are all below 2000 characters, totaling 2080; the full deferred arguments remain below.

## Extracted arguments for future workers

The original return's nine steps map as follows: 1-3 to A (restriction, insertion, specified comparison); the assembly and scalar passages of 4 to parent step 1; 5-6 to B (finite direct and compact exchange); the integral part of 7 to C, with its scalar passages in parent step 2; 8 to parent step 2; 9 to parent step 3. The previous worker expanded the corrected proof into eleven steps; all eleven are reproduced below. The numbering is archival and references within it refer to that expansion, not to the new parent's three steps. The original proof's false integral tensor and summand passages have explicit corrections, as described above.

### A: restriction, insertion, and specified finite/integral comparison

For the arbitrary g in A, the same site calculation uses its own inverse scheme map, without any Frobenius property. In the inverse-image comma category at U=(U,u), objects are (V,t) with v t=g u. The initial object is ((U,g u),id); it is terminal after taking the opposite category used by the contravariant sheaf in the colimit. The inverse coprojection is the cocone of restrictions along the unique arrows. It is natural in U. Composition of the structure map with g is a covering-preserving site equivalence, so the computed presheaf is already a sheaf: its sheaf equalizer is the corresponding equalizer for N after that equivalence. This identifies the ACTUAL insertion followed by sheafification with identity under evaluation. At the final object, inverse restriction along g^{-1}:U->V is inverse to restriction along g:V->U. Transport of constant scalars through c^{-1} gives linearity, and an inverse of a bijective linear map is linear by applying sigma to a scalar multiple. These equations commute with differentials and roofs, using exact sections/inverse image. At finite coefficients, the inverse tensor map is balanced since (r x) tensor b = x tensor c(r)b. On x tensor b its composites with x->x tensor 1 are identity. At integral coefficients the completed pullback is handled by theta kappa=G(u), including its entire cone coordinate: delta=G(u)^{-1}theta is inverse on complete objects. Composing these inverses in reverse order gives rho Gamma(delta). Inverse naturality follows from the already stated naturality equations after multiplying by those inverse maps. This generalizes the following retained finite-field proof without adding a constructibility or boundedness hypothesis.

Expanded step 1:

*Point transport, first map ($\Lambda\in\{A_{E,n},\mathcal O_E\}$).* By
[lem-weil-frobenius-square-cartesian] (1), in the case $Y_0=\Spec k_0$, $g_s=\Spec(\gamma)$ is an
automorphism of $s$ with inverse $\Spec(\gamma^{-1})$. Hence $(s\xrightarrow{g_s}s)$ is an object of
$s_{\mathrm{proet}}$ [def-weil-pbc-proetale-site] (an isomorphism is weakly etale), and the morphism
$g_s:(s\xrightarrow{g_s}s)\to(s\xrightarrow{\operatorname{id}}s)$ of $s_{\mathrm{proet}}$ used in
[def-weil-frobenius-point-transport] has the inverse
$g_s^{-1}:(s\xrightarrow{\operatorname{id}}s)\to(s\xrightarrow{g_s}s)$ (a morphism over $s$ because
$g_s\circ g_s^{-1}=\operatorname{id}$). A presheaf is a functor, so the restriction
$\operatorname{res}_{g_s}:N^i(s\xrightarrow{\operatorname{id}}s)\to N^i(s\xrightarrow{g_s}s)$ along an
isomorphism is bijective, with inverse the restriction along $g_s^{-1}$, for every term $N^i$ of $N$;
so $\operatorname{res}_{g_s}$ is an isomorphism of complexes.

Expanded step 2:

For a sheaf $\mathcal F$ on $s_{\mathrm{proet}}$, write $\mathcal I_U$ for the index category in [def-weil-proetale-inverse-image]. Its objects are $(V,t)$ with $v t=g_su$, where $u:U\to s$, $v:V\to s$. The object $((U,g_su),\operatorname{id}_U)$ is initial: the unique arrow to $(V,t)$ is $t$. Thus it is terminal in $\mathcal I_U^{\mathrm{op}}$, the category actually indexing the colimit, and the coprojection $\mathcal F(U,g_su)\to(u_{g_s,p}\mathcal F)(U,u)$ is an isomorphism, with inverse induced by restriction along those unique arrows. These maps are natural in $U$. By [lem-weil-proetale-isomorphism-inverse-image] (1), composition of structure maps with $g_s$ is a covering-preserving equivalence of sites, as is its inverse. Consequently $U\mapsto\mathcal F(U,g_su)$ satisfies the same sheaf equalizer condition as $\mathcal F$, so the colimit presheaf is already a sheaf. At $U=(s,\operatorname{id})$ this coprojection, followed by sheafification, is exactly the insertion of [def-weil-frobenius-point-transport]. It is invertible termwise and commutes with differentials, hence is an isomorphism of underlying complexes.

Expanded step 3:

At finite coefficients $A=A_{E,n}$, [lem-weil-proetale-isomorphism-inverse-image] (3) makes $c_A:g_s^{-1}A_s\to A_s$ an isomorphism. By part (a) of [def-weil-inverse-image-pullback-comparison] the specified $\kappa_N$ is represented termwise by $x\mapsto x\otimes1$. Its inverse sends $x\otimes a$ to $c_A^{-1}(a)x$: the tensor relation shows this is well defined, and the two composites are identities. These maps commute with restrictions and differentials, so give inverse maps after sheafification and passage to the derived category. Therefore $\kappa_N:g_s^{-1}N\to Lg_s^*N$ is invertible. The exact sections functor of [lem-weil-point-proetale-sections-exact] induces a derived functor and preserves this isomorphism.

Expanded step 4:

At integral coefficients use the completed pullback, not tensor change of rings on $N$. The object $N\in D^b_c(s,\mathcal O_E)$ is derived complete by [def-weil-derived-complete-integral-detailed]. Apply [lem-weil-isomorphism-derived-pullback-comparison-normalization] to $g=g_s$, an isomorphism by [lem-weil-frobenius-square-cartesian] (1). It concerns precisely the specified map of [def-weil-inverse-image-pullback-comparison] (b): $\theta_{g_s,N}\kappa_N=g_s^{-1}(u_N)$, and on derived-complete objects its inverse is $g_s^{-1}(u_N)^{-1}\theta_{g_s,N}$. Thus this actual $\kappa_N$, including its shifted cone coordinate, is invertible. Applying the derived sections functor [lem-weil-point-proetale-sections-exact] preserves invertibility.

Expanded step 5:

For $\Lambda=A_{E,n}$ or $\mathcal O_E$, the map $\sigma_N$ is the restriction followed by insertion in [def-weil-frobenius-point-transport]. Steps 1-2 make it invertible on underlying complexes; [lem-weil-frobenius-point-transport-natural] (1) makes it $\Lambda$-linear, so its inverse is linear too: if $y=\sigma_N(x)$, then $\sigma_N^{-1}(ay)=ax$. Steps 3-4 make $\Gamma(s,\kappa_N)$ invertible. Hence $\iota_N=\Gamma(s,\kappa_N)\sigma_N$ is invertible. For $\Lambda=E$, the same definition gives $\iota_N^E=\iota_N^{\mathcal O_E}\otimes E$, so its inverse is the image of the integral inverse under scalar extension. Here [def-weil-rationalization-karoubi] has the same objects as the integral category and takes no idempotent completion. For $\Lambda=\Qlb$, [def-weil-algebraically-closed-coefficients] and the point-transport definition represent $\iota_N$ at one finite coefficient field; the inverse at that stage represents its inverse in the common-stage category. This proves part 1.

### B: actual finite mate and proper/open composite

Expanded step 6:

*Direct-image exchange at finite level.* Let $f_0:X_0\to Y_0$ be a separated finite-type morphism of
finite-type $k_0$-schemes, $f:X\to Y$ its base change to $k$, and $A=A_{E,n}$. All schemes involved
are over $k$ of characteristic $p\neq\ell$, so $\ell$ is invertible on them. By
[def-weil-frobenius-square-exchange] (1), $\operatorname{FrEx}_{f,*}$ is the ambient exchange
$\Ex^A_{\square_f}$ of [def-weil-pbc-ambient-ringed-exchange] for the Frobenius square
$\square_f=(f,f,g_Y,g_X,(g_X,f))$, Cartesian [def-weil-pbc-cartesian-square] by
[lem-weil-frobenius-square-cartesian] (3): it is the mate
$Lg_Y^*Rf_*\xrightarrow{\eta Lg_Y^*Rf_*}Rf_*Lf^*Lg_Y^*Rf_*\xrightarrow{Rf_*\theta Rf_*}
Rf_*Lg_X^*Lf^*Rf_*\xrightarrow{Rf_*Lg_X^*\varepsilon}Rf_*Lg_X^*$ of the natural isomorphism
$\theta=\theta_{\square_f}:Lf^*Lg_Y^*\xrightarrow{\sim}Lg_X^*Lf^*$ under the adjunction
$Lf^*\dashv Rf_*$ (unit $\eta$, counit $\varepsilon$) between $D(Y_{\mathrm{proet}},A)$ and
$D(X_{\mathrm{proet}},A)$ [def-weil-derived-pullback-tensor-hom, def-weil-derived-direct-image]. Apply
[lem-weil-mate-iso-along-equivalences] with $\mathcal C=\mathcal C'=D(Y_{\mathrm{proet}},A)$,
$\mathcal D=\mathcal D'=D(X_{\mathrm{proet}},A)$, $L=L'=Lf^*$, $R=R'=Rf_*$, $G=Lg_Y^*$, $G'=Lg_X^*$:
its mate $\alpha:GR\to R'G'$ is exactly the displayed composite. By
[lem-weil-frobenius-square-cartesian] (1), $g_Y$ and $g_X$ are isomorphisms of schemes, so by
[lem-weil-isomorphism-derived-pullback-equivalence] $G=Lg_Y^*$ and $G'=Lg_X^*$ are equivalences of
categories. Hence $\operatorname{FrEx}_{f,*}(K)$ is an isomorphism for every
$K\in D(X_{\mathrm{proet}},A_{E,n})$.

Expanded step 7:

*Compact-support exchange at finite level.* With $f_0$ as in step 6, choose the compactification
$X_0\xrightarrow{j_0}\overline X_0\xrightarrow{p_0}Y_0$ of [def-weil-frobenius-square-exchange] (2)
([def-weil-compactifications-refinements], existing by [prop-compactification-refinement]); $p_0$ is
proper, hence a separated finite-type morphism of finite-type $k_0$-schemes. By definition
$\operatorname{FrEx}_{f,!}(K)=Rp_*(b_{g_{\overline X}}(K))\circ\operatorname{FrEx}_{p,*}(j_!K)$
(composed, if $Rf_!$ was formed with another compactification, with the comparison isomorphisms of
[prop-compactification-coherence-detailed]). The first factor $\operatorname{FrEx}_{p,*}(j_!K)$ is an
isomorphism by step 6 applied to $p_0$. The map $b_{g_{\overline X}}(K):Lg_{\overline X}^*j_!K\to
j_!Lg_X^*K$ is an isomorphism by [lem-trf-open-square-exchange], applicable because the square
$(j,j,g_{\overline X},g_X)$ is Cartesian with $j$ an open immersion by [lem-trf-frobenius-open-square];
so $Rp_*(b_{g_{\overline X}}(K))$ is an isomorphism, $Rp_*$ [def-weil-derived-direct-image] being a
functor. Hence $\operatorname{FrEx}_{f,!}(K)$ is a composite of isomorphisms, an isomorphism, for every
$K$ in the domain of [def-compact-support-direct-image-detailed]. On a different compactification $d$, the specified map is $(C_{d,c}(Lg_X^*K))^{-1}\operatorname{FrEx}_{f,!}^c(K)Lg_Y^*(C_{d,c}(K))$, again a composite of isomorphisms. This comparison is used only on the etale-origin domain declared by [def-compact-support-direct-image-detailed]; on an arbitrary ambient complex retain the chosen compactification $c$.

The compact inverse follows by multiplication, in reverse order: if D=FrEx_{p,*}(j_!K), the forward map is Rp_*(b) D and the inverse is D^{-1} Rp_*(b^{-1}). Both composites cancel using functoriality of Rp_*. For the other model, write C=C_{d,c}(K) and C'=C_{d,c}(Lg_X^*K). The forward map is (C')^{-1} FrEx^c Lg_Y^*(C); its inverse is Lg_Y^*(C^{-1}) (FrEx^c)^{-1} C'. On the witnessed etale-origin domain these C,C' are the stated isomorphisms. This proves the formula without asserting general exchange/refinement independence.

### C: whole-system invertibility and integral realization

For an arbitrary C in D(S_X), simultaneous units, counits and pullback compositors form e_f,C before evaluation. The compact exchange is the same proper mate followed by proper image of the system open mate. Evaluation of these composites is the finite derived mate, respectively proper/open composite, on e_n C. The finite argument above permits unbounded e_n C, not just constructible reductions. Every evaluated map is invertible; joint conservativity therefore makes the whole-system maps invertible. Evaluation of their two inverse identities proves that the evaluations of their inverses are exactly the finite inverses. This is enough; no attempt is made to detect equality of arbitrary derived maps by evaluation. For reduction systems of integral K, realization and the specified alpha/beta give precisely the following retained argument.

Expanded step 8:

For integral $K$, use the strict semilinear system maps $e_f$ and $e_f^c$ specified in [def-weil-frobenius-square-exchange], with the same $k_0$-compactification at every level. For $e_f$, evaluation at $m$ is exactly the finite direct exchange on $K\otimes^L A_{E,m}$; for $e_f^c$, evaluation is the direct exchange for $p$ followed by $Rp_*(b)$ on that reduction. They are isomorphisms by steps 6-7. The evaluations on $D(\mathscr S_Y)$ jointly detect isomorphisms by [lem-coef-semilinear-derived-sections], so $e_f$ and $e_f^c$ themselves are isomorphisms. In the same definition, $U_Y$ is an exact restriction functor on systems, and $\mathcal L_Y=R\varprojlim U_Y$ uses the derived strict-tower functor of [prop-weil-pbc-rlim-functoriality]. Functors preserve inverses, so $\mathcal L_Y(e_f)$ and $\mathcal L_Y(e_f^c)$ are invertible. The specified integral exchanges are $\beta_*\mathcal L_Y(e_f)\alpha_*$ and $\beta_!\mathcal L_Y(e_f^c)\alpha_!$, with the displayed operation comparison isomorphisms $\alpha,\beta$ of the definition. Hence both integral exchanges are invertible. This argument uses a specified morphism in the derived category of systems; it does not infer a map, or equality of maps, from evaluated components.

The inverse of beta L(e) alpha is alpha^{-1} L(e^{-1}) beta^{-1}; the two composites reduce to identities by associativity and L preserving composition. This is an inverse in the correct integral derived category, before any scalar localization. Naturality follows by inverting the system naturality squares and composing with the natural operation comparisons. The same compactification is used at all finite levels, so the finite evaluations in this argument really are those of one system map.

### Parent: scalar passages, structure-map specialization, cohomology and naturality

Expanded step 9:

For rational coefficients the exchange maps of [def-weil-frobenius-square-exchange] are the images of the integral exchanges under the scalar-localization functor [def-weil-rationalization-karoubi], on integral object representatives. Their inverses are the images of the inverses from step 8. For $\Qlb$ they are the morphism classes represented by the rational exchanges at a finite stage [def-weil-algebraically-closed-coefficients]; the inverse at that stage represents the inverse class. No passage to summands occurs.

Expanded step 10:

*Part 2.* Take $f_0=a_{Y_0}:Y_0\to\Spec k_0$ (separated of finite type), so $f=a_Y$, $Y$ of steps 6-9
is $s$, $g_Y$ there is $g_s$ and $g_X$ there is $g_Y$; then $\operatorname{FrEx}_{Y,*}(M)=
\operatorname{FrEx}_{a_Y,*}(M)$ and $\operatorname{FrEx}_{Y,!}(M)=\operatorname{FrEx}_{a_Y,!}(M)$
[def-weil-frobenius-cohomology-transport, def-weil-frobenius-square-exchange], isomorphisms by steps
5-7. Their source and target lie in the full subcategory $D^b_c(s,\Lambda)$ (as in
[def-weil-frobenius-cohomology-transport]), and an isomorphism of the ambient category between objects
of a full subcategory is an isomorphism of the subcategory.

Expanded step 11:

*Part 3.* By [def-weil-frobenius-cohomology-transport],
$\tau_M=\operatorname{Fib}_s(\operatorname{FrEx}_{Y,*}(M))\circ\iota_{Ra_{Y*}M}$ and
$\tau_{c,M}=\operatorname{Fib}_s(\operatorname{FrEx}_{Y,!}(M))\circ\iota_{Ra_{Y!}M}$. The maps
$\iota_{Ra_{Y*}M}$, $\iota_{Ra_{Y!}M}$ are isomorphisms by part 1 (step 5), and
$\operatorname{Fib}_s$ [def-weil-finite-coefficient-point], a functor, carries the isomorphisms of part 2
(step 10) to isomorphisms; so $\tau_M$ and $\tau_{c,M}$ are isomorphisms. They are natural in $M$ by
[def-weil-frobenius-cohomology-transport] (composites of natural transformations), hence natural
isomorphisms. Taking the $i$-th cohomology, a functor, gives isomorphisms
$\mathrm H^i(\tau_M):H^i(Y,M)\to H^i(Y,Lg_Y^*M)$ and $\mathrm H^i(\tau_{c,M}):H^i_c(Y,M)\to
H^i_c(Y,Lg_Y^*M)$ [def-weil-ordinary-compact-cohomology] for every $i$. For naturality the point transformation is natural for derived morphisms and common-stage scalar extensions by [lem-weil-frobenius-point-transport-natural] (2), and both exchange transformations are natural by their specified composites [def-weil-frobenius-square-exchange]. Whiskering these transformations with $Ra_{Y*}$, $Ra_{Y!}$ and $\operatorname{Fib}_s$, then composing them, gives the naturality square of each transport. Applying the functor $\mathrm H^i$ gives the corresponding naturality square on groups.

## Server validation

The required initial dry run was performed before repair and reproduced the returned failure: zero new nodes against the explicit requirement for three. After the repair, server `review_split` passed. The final full `deliver.py Q78 lem-weil-frobenius-cohomology-transport-iso --no-push` exited 0 and printed `OK (not pushed) ... at eb3a1e1968b: preflight passed`, with a durable dry-run receipt. The parent statement remains byte-for-byte unchanged; there are three new unsplit statement nodes, zero Mathlib leaves, and 2080 proof-text characters. Every citations.json quote was checked literally against the current node statement; proof_deps is exactly the union of uses. No delivery invocation remained active when the push was started.
