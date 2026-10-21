# Q68 stage-1 re-split delivery

## Files written

- dag/nodes/sec-six-functors/lem-weil-finite-duality-locally-closed-comparison.json: existing statement unchanged; four-step assembly, 2560 proof-text characters.
- dag/nodes/sec-six-functors/lem-sf-derived-immersion-comparison-normalization.json: statement, unsplit, no Mathlib match. No proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-locally-closed-closure-adjoint-realization.json: statement, unsplit, no Mathlib match. No proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-locally-closed-closure-comparison-square.json: statement, unsplit, no Mathlib match. No proof steps or proof dependencies.
- dag/nodes/sec-six-functors/lem-sf-locally-closed-relative-transpose-normalization.json: statement, unsplit, no Mathlib match. No proof steps or proof dependencies.
- citations.json: verbatim statement excerpts for every parent-step citation.
- report.md: review, source checks, workload allocation and the full retained argument.
- searches.jsonl: genuine msearch.py log; research/ contains the complete returned search outputs and the original item for interruption recovery.

## Attachments

None. The key-notion and blueprint-tag searches in lean/WeilConjectures give no completed project declaration stating this item. I also read lean/Sheaf/AlgebraicGeometry/FiniteDualityLocallyClosedComparison.lean: finiteDuality_locallyClosed_comparison at line 480 has sorry at line 497, and the factorization theorem at line 518 is also sorried. Its helper definitions cover only parts, not the four new statements. This is the explicitly authorized re-split, even though the live node has reviewed metadata. No Lean was changed or compiled.

## WANTED

None. The blueprint and all Stacks component passages used here are present locally.

## What needed repair

The human requested division of the 13783-character proof into independent work. There is no statement dispute. The old proof mixes geometric prerequisites, termwise descent, closed/open mates, closure comparison, and a comparison-class adjunction calculation in one task. The new statements expose the actual intermediate results, rather than moving the theorem unchanged into a new node. They are separately usable and none assumes the parent result or any other new node. The transpose lemma assumes the closure square and the ambient counit equation; it does not assert construction of the comparison gamma. The closure-square lemma does not assert exceptional comparison at all. The normalization lemma concerns individual open and closed ordinary restriction adjunctions. The realization lemma concerns the geometric compactification and etale adjoint, without transporting exceptional inverse image across sites.

Existing metadata, statement, statement dependencies, blueprint provenance and Lean attachments were preserved. Only the parent's proof, proof dependency union, proof origin and split_report were updated. The item is not the statement of its unit, so no unit file is changed.

## Workload allocation

1. lem-sf-derived-immersion-comparison-normalization: old Steps 2, 3, 8, including descent of the literal open unit, the open counit transpose calculation, equality of the named derived closed mate with the termwise sheaf mate, and its restriction normalization. This is an argument about exact models and actual adjunction maps, not merely existence of isomorphic objects.
2. lem-sf-locally-closed-closure-adjoint-realization: old Steps 1 and 7, the bound-preservation part of 5, and the dimension-bound prerequisite of 10. This proves the geometric hypotheses, the normalized extension identifications on unbounded derived categories, adjoint realization, and bounded-below output.
3. lem-sf-locally-closed-closure-comparison-square: old Step 9 and the left-adjoint part of 12. The result is equality of the actual two left-adjoint comparison paths, using the restriction Hom bijection, and the resulting factorization square and cocycle.
4. lem-sf-locally-closed-relative-transpose-normalization: old Steps 10 and 11 and their transported coherence in 12. It computes the two different Hom transposes with the same compactification and the comparison unit, then handles arbitrary witnesses. Its extra hypotheses are precisely the intermediate results established before using it.

The short parent retains old Steps 4--6 as the explicit naturality/pasted-counit assembly, and the remaining right-adjoint part of Step 12 as conjugation and uniqueness. Thus no argument disappears or is replaced by a vague assertion of compatibility. Below, the original twelve steps are preserved verbatim, with their citations, so the future workers can recover every detail. The new node source places also locate these arguments in the current Lean docstring (theorem finiteDuality_locallyClosed_comparison, preceding line 480).

## Sources read

For the item and all four nodes I read the current main-20261015 blueprint proof of lem-weil-finite-duality-site-comparison, especially the second-paragraph sentence asserting locally closed exceptional comparison by the open and closed comparisons. This is an agent-formulated expansion of that sentence, not a claim that the expanded assertions appear verbatim in a Stacks tag. The unsplit nodes therefore retain that blueprint as source and do not pretend to have document-written proofs.

For derived normalization I read Stacks proetale.tex Tag 09AF, label lemma-jshriek-comparison (both functors have the same right adjoint); Tag 09AA, lemma-closed-immersion (closed pushforward is fully faithful and restriction is a left inverse); Tag 09BM, lemma-closed-immersion-complement-retrocompact-exact (the precise retrocompact-complement assumption); Tag 09BN, lemma-open-immersion; and sites-modules.tex Tags 03DI and 03DJ, labels lemma-extension-by-zero and lemma-extension-by-zero-exact. The actual descent is the argument in old Steps 2 and 8 using the existing termwise-adjunction and localization statements. Tag 09AF alone does not assert the derived normalization, and the old sheaf-level unit node is not cited for a derived result it never states.

For closure realization and the closure square I read the full statements of lem-sfb-etale-locally-closed-extension-comparison and lem-sfb-locally-closed-extension-coherence. The former gives the identity-normalized etale closure comparison on sheaves; the latter explicitly gives the unbounded pro-etale restriction Hom bijection and normalized factorization maps. Stacks Tag 0GJ1, etale-cohomology.tex lemma-compatible-shriek-push-finite, is the finite/open interchange supporting the etale comparison. Exactness and the Noetherian complement hypothesis supply the derived passage; properness of the closure immersion is verified directly, not borrowed from a theorem with a different hypothesis. The dimension statement is separately supplied by lem-kun-dimension-finite-type.

For the relative transpose I read categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints, and Tag 0DV0, lemma-compose-counits, with their proofs. I read the complete statements of lem-pur-bounded-site-adjunction-transpose and thm-sf-ambient-adjoint-class. The former, not merely the class-adjoint existence theorem, fixes the exact closure-normalized Hom formula. It requires the same finite coefficient datum, finite-type schemes, separated finite-type s, a compactification and nonnegative dimension bound. Those are all supplied by closure realization. No SGA source is used.

## Not duplicates

lem-sf-derived-immersion-comparison-normalization vs lem-sf-open-comparison-unit-normalization: the existing assertion is on module sheaves; the new assertion identifies the derived mates, descends units and counits and includes closed restriction normalization, which is absent from the existing statement.
lem-sf-derived-immersion-comparison-normalization vs lem-weil-pbc-comparison-direct-image-canonical-mate: the existing assertion specifies a derived mate and its equation, but never identifies it with a termwise sheaf mate or states the open derived-unit equation.
lem-sf-derived-immersion-comparison-normalization vs lem-kun-derived-adjoint-square-comparison: that generic lemma assumes the derived-comparison universal property and an underived square respecting adjuncts; it does not supply the geometric exactness, open normalization or closed left-inverse property needed here.
lem-sf-locally-closed-closure-adjoint-realization vs lem-sfb-etale-locally-closed-extension-comparison: the latter is a sheaf-level extension identification, without unbounded adjoint realization or boundedness of closed exceptional output.
lem-sf-locally-closed-closure-adjoint-realization vs lem-sfb-locally-closed-extension-coherence: the latter is pro-etale extension coherence and full faithfulness, not the etale compact-support adjoint or its geometric and constructible bounds.
lem-sf-locally-closed-closure-comparison-square vs lem-sf-proper-open-comparison-site-normalization: the latter concerns a proper map between two open compactifications, rather than comparison of a closed-then-open factorization with its open-then-closed closure factorization.
lem-sf-locally-closed-closure-comparison-square vs lem-exc-etale-origin-open-restriction-transport: the latter has a qcqs cartesian open restriction square and a derived restriction map, not the closure mixed-extension square and its change-of-factorization maps.
lem-sf-locally-closed-relative-transpose-normalization vs lem-pur-bounded-site-adjunction-transpose: the latter computes a closure compactification's comparison-class transpose; the new assertion compares that transpose with the separately existing ambient closed/open exceptional adjunction, after conjugating by q and computing both formulas.
lem-sf-locally-closed-relative-transpose-normalization vs thm-sf-ambient-adjoint-class: existence and witness independence do not specify which isomorphism identifies its relative Hom bijection with the ambient one; the new assertion fixes that isomorphism as rho gamma inverse and proves its normalization.
lem-sf-locally-closed-relative-transpose-normalization vs lem-sf-etale-proetale-exceptional-transport: the latter is restricted to finite-Tor categories with preservation hypotheses; here the test complexes are arbitrary bounded-below etale-origin complexes and the adjunctions are the ordinary module-derived ones.

I searched the entire DAG by mate-pasting, closure comparison, locally closed adjoint, termwise mate and relative transpose, and used blueprint_refs.py searches for adjunction comparison, locally closed, mate, closed mate, closure comparison and relative transpose. No blueprint node states one of these four intermediate results. The general mate-pasting node is reused as existing calculus rather than duplicated. Source metadata here refers to the expanded blueprint argument, not to a single shared Stacks-tag lemma, so the tag-pair gate has no further pairs.

## Mathlib results

Each new node has its own initial leanfinder, loogle, grep and leansearch query, and a second leanfinder phrasing; all came from the prescribed msearch.py command and are in searches.jsonl. Complete returned hits are retained in research/, and I read them. The initial loogle queries mentioning CategoryTheory.Localization or CategoryTheory.NatIso were rejected as unknown identifiers; these are recorded in results, and the valid additional queries "Adjunction", "counit" and "IsImmersion" were run afterwards and read. No invalid-pattern result is treated as evidence of mathematical absence. Additional grep in AlgebraicGeometry shows the pro-etale site definitions, without these derived comparison assertions. The generic results are useful components, not one-line specializations of the new statements.

In particular, I opened Mathlib/CategoryTheory/Adjunction/Restrict.lean at restrictFullyFaithful_homEquiv_apply and Mathlib/CategoryTheory/Adjunction/Unique.lean at rightAdjointUniq and its counit equations. The former assumes already supplied commuting squares and adjunction structures and does not identify the closure-normalized site Hom formula. The latter compares two adjunctions on the same entire category; it does not construct or compute the bounded etale-origin comparison-class adjunction. The Scheme.Modules.restrictAdjunction hits concern structure-module sheaves on the Zariski site, not the constant finite-ring etale/pro-etale categories. No Mathlib leaf is claimed.

## Review by Q68

For this returned-head repair I re-read every current direct citation, including the changed scheme-theoretic-image definition, and repaired the closure interfaces and the explicit Plus/full transport as detailed in the repair section below. This revalidation is part of my review signature; the parent statement and all four independent tasks are retained.

I checked the four new statements against the actual old argument and the source passages above, with all node statements open. Each introduces the coefficient ring, schemes, sites, functors, maps and boundedness assumptions it uses; its bracketed notion references occur in stmt_deps. None has proof text or proof_deps. There is no new-node chain that merely rephrases the entire parent: the derived normalization and closure realization are independent, the closure square has no exceptional adjoint in its conclusion, and the relative-transpose lemma is conditional on two previously proved map identities.

Parent Step 1 cites closure realization specifically for N in D^b_c, H in D^+, the compactification and the conjugate etale right adjoint, and derived normalization specifically for the actual open/closed comparison maps and their derived equations. Both new statements explicitly provide these. Noetherianity is used to make the open complements quasi-compact and hence retrocompact; it is never omitted in the closed pro-etale exactness assertion. V is open in a finite-type scheme over a field, so quasi-compactness supplies finite type; separatedness is inherited by restricting the closed diagonal. The closure is a closed subscheme of T and hence has finite type and finite dimension. Empty closure uses dimension bound zero.

Parent Step 2 cites the closed sibling exactly for alpha_N and the displayed exceptional counit equation; it does not use a theorem about ordinary closed restriction commuting with internal Hom. Its bounded constructible input is supplied in Step 1. If using the current sibling's Plus/full convention, choose any bounded-below lift of H and insert the canonical inclusion identifications for delta and alpha. The boundedness assertion makes this legitimate. The canonical pullback node explicitly supplies b and its composition coherence. The derived normalization node gives the open counit equation used in the last equality. The composite-adjunction definition gives precisely epsilon=e v_!(k). I recomputed the three equalities: naturality of the closed exceptional counit at b, the closed counit identity, naturality of o at k^e, and then the open counit identity. There is no arbitrary choice of isomorphisms.

Parent Step 3 cites the closure-square node for q_p Delta=B C_T(q_e). Its hypotheses are all already supplied, and B uses exactly the proper closed mate and the specified open comparison in the relative-transpose node. That node explicitly returns the two transpose formulas, theta=rho gamma inverse, witness independence and all defined adjunction maps. I checked its additional assumed counit identity is exactly Step 2, and its H bounded-below hypothesis is exactly Step 1. Full faithfulness is only invoked between D+ objects: F_e preserves the lower bound. The target C_TM is bounded below, the compactification has a nonnegative dimension bound, and s is separated finite type. The equation U_T(a_p B) eta=eta_M a_e has identical objects on both sides; after adjunction conjugation it gives rho C_S(g_0), not an unidentified iso.

Parent Step 4 uses the adjunction-conjugate statement for composition and identity compatibility, and the composite-adjunction statement and right-adjoint-composition lemma for the literal pasted adjunction data. Its left comparison square was proved in Step 3 by the closure-square node. Equality of its right squares follows by uniqueness of a transpose, and equality of the transported square follows by cancelling the invertible gamma in theta gamma=rho. This is a few-line elementary argument from those precise statements, not a hidden geometric comparison. The full old Step 12 is retained below for its explicit formulas.

I tested identity immersion (all normalizations become identities), a pure open immersion (the closed mate is identity), a pure closed immersion (the open map is identity), empty S and empty closure (zero extension and dimension bound zero), first coefficient stage n=1, and a nontrivial open stratum with proper closure. In the pure closed case the closed counit is the ordinary restriction/direct-image counit only in the normalization lemma; it is not confused with the exceptional counit in the parent's calculation. I checked the formula types for q_p Delta=B C_T(q_e), a_p B=C_T(a_e), gamma and theta. Their directions agree.

Against delivery-errors B--E: the new nodes are statement-only; notions and exact coefficient categories are explicit; TeX is singly escaped in the decoded JSON; source statements are read rather than inferred from labels; there are no fabricated searches or claimed Mathlib leaves; blueprint provenance is filled. The new statements are not duplicates of the candidates explained above or clauses moved wholesale from the parent. The parent keeps its explicit construction and counit calculation. Every non-elementary remaining step has node citations saying exactly what it uses; citations.json uses literal substrings. No parent step exceeds 2000 characters. The entire old detailed argument survives below allocated to the new tasks and the assembly. No hypothesis, target, Lean source or source-route change was made. The complete mathematical review is my own, as direct delivery requires.

## What could not be finished

Nothing in the requested stage-1 scope. The four new nodes are deliberately left unsplit, without proof steps, for separate workers. Server validation and delivery results are recorded after the runs.

## Repair of returned delivery 62b928ebdc1 — 2026-10-21

The landing return names one changed dependency: def-nagata-scheme-theoretic-image. I compared the retained delivered files and original.json with the current read-only DAG, re-read the current definition and its blueprint_update, and kept the four-node re-split and the complete twelve-step archive. The delivery tool rebuilds the repaired overlay on current origin/sheaf-dag, preserving current maintainer fields; I ran no git command in the shared read repository.

The current definition says verbatim: “The scheme-theoretic closure of a locally closed
subscheme is the scheme-theoretic image of its immersion.” Its kernel ideal is the largest quasi-coherent subideal of the structure-map kernel, with equality to that kernel only under quasi-compactness. I read Stacks morphisms.tex Tag 01R6, label lemma-scheme-theoretic-image, Tag 01R8, label lemma-quasi-compact-scheme-theoretic-image, and Tag 01RG, label lemma-quasi-compact-immersion. They supply the smallest closed factorization, its kernel description and open restriction under quasi-compactness, and the fact that the canonical factor map of a quasi-compact immersion into its image is open. The current transitive image-interface node lemma-nagata-scheme-image-ideal-qc agrees with that construction and explicitly distinguishes the kernel ideal and its vanishing locus.

I repaired each of the three new statements that cites this definition: closure-adjoint-realization, closure-comparison-square, and relative-transpose-normalization now explicitly set bar S=SIm(s), identify i and u as the canonical image inclusion and factor map, and specify the largest quasi-coherent kernel ideal. They state why the raw kernel is legitimate here: T is Noetherian, so the closed-then-open immersion s is quasi-compact. In the finite-type nodes this follows from T being finite type over the field; the closure-square node assumes T Noetherian directly. For each affine open W in T, s^{-1}(W) is a closed subscheme of an open subscheme of the Noetherian W and is therefore quasi-compact. There is no unrestricted raw-kernel assumption and no replacement of the schematic closure by the reduced topological closure. These are clarifications of the existing closure objects, not changes to the parent statement or its hypotheses; the logged Mathlib search questions and verdicts still apply unchanged.

I re-read all current parent-step citations. Step 1's realization still supplies Noetherianity, the closure compactification, q and H in D+; its normalization citation supplies the actual derived open counit and termwise closed mate. Step 2's current closed-comparison sibling uses a bounded-below lift and the named Plus mate. I made that transport explicit in the parent, with lift independence obtained from equality to the termwise mate in the normalization node; the exceptional counit equation then has exactly the types used in the assembly. The pullback and composite-adjunction citations still supply b and the pasted counit. Step 3's two extracted statements retain exactly the closure square and both transpose formulas. Step 4's conjugation, composition and pasted-adjunction statements retain the identity/composition laws. All literal quotes in citations.json were checked against these current statements. Current statements and their hashes are retained in research/revalidated-cited-statements.json for any later citation-change return.

I also re-read the current definitions and theorems used in the four new statements, including the ordinary etale compact-support candidate, ambient etale adjoint, pro-etale closed support, chosen-compactification relative Hom formula, bounded site comparison, and comparison-class theorem. None changes the finite ordinary module coefficients or the bounded-below domains used here. No appeal to a proof hidden inside a cited node is needed. The source/definition change therefore leaves the normalization, closure square and relative-transpose arguments valid on the same compactification.

For the changed closure construction I tested identity and empty immersions, a closed point of the affine line, and a nonreduced closed immersion Spec(k[epsilon]/epsilon^2) into the affine line. The last image retains the ideal (t^2), so replacing it by the reduced point would be wrong; the revised wording retains the correct scheme. For a pure open immersion the canonical image factor is open by 01RG; for the empty source the image is empty and the existing dimension bound zero remains valid. The earlier B--E review and allocation remain in force: four statement-only nodes, no new proof dependency chains, no parent step above 2000 characters, and 2560 total assembly characters (below 3000). This is a citation-aware mathematical repair, not an unchanged re-push.

## Retained original argument and assignments

### Original Step 1 — assigned to lem-sf-locally-closed-closure-adjoint-realization

Write $C_W=\nu_W^*$, $I_e=Rc_{et}^!$, $I_p=Rc_{proet}^!$, $N=v_{et}^*M$ and $H=I_eN$. The schemes $S,T$ are Noetherian: a field has only the ideals $0,1$, so its spectrum is Noetherian, and finite type over it is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. The open-subscheme theorem gives Noetherian $V$ and quasi-compactness of all the complementary opens. The open $V$ is still finite type over $k$: cover $T$ by finitely many affine finite-type charts, and cover the intersection of $V$ with each chart by finitely many principal opens, possible by this quasi-compactness. Their rings are localizations of finite-type $k$-algebras at one element, hence generated by the original generators and that inverse. Separatedness restricts to an open subscheme by restriction of the closed diagonal. Exact inverse image and [lem-weil-pbc-exact-functor-bounded-below] give $\mathcal H^r(N)=v^*\mathcal H^r(M)$; constructible pullback therefore gives $N\in D^b_c(V_{et},A)$ [prop-constructible-pullback]. Apply [lem-weil-finite-duality-closed-comparison] to $c$ and $N$. Its bounded-below conclusion gives $H=J_{et}M\in D^+(S_{et},A)$, so the named closed direct-image comparison can be evaluated at $H$.

Original cited statements: lem-weil-pbc-finite-type-over-noetherian, prop-weil-pbc-inverse-image-modules-exact, lem-weil-pbc-exact-functor-bounded-below, prop-constructible-pullback, lem-weil-finite-duality-closed-comparison, lem-weil-pbc-noetherian-open-subscheme-noetherian.

### Original Step 2 — assigned to lem-sf-derived-immersion-comparison-normalization

Use $b:C_Vv_{et}^*\xrightarrow{\sim}v_{proet}^*C_T$ for [lem-weil-pbc-comparison-pullback] and $o:C_Tv_{et,!}\xrightarrow{\sim}v_{proet,!}C_V$ for [lem-cbc-proetale-extension-zero-comparison]. Their open unit normalization is [lem-sf-open-comparison-unit-normalization]. These sheaf comparisons and their normalization hold also on ordinary derived categories: the two open extensions are exact [lem-weil-pbc-extension-by-zero-exact, lem-weil-extension-by-zero-exact], and comparison and open restriction are exact inverse images [lem-sf-comparison-pullback-exact, prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact]. Apply the comparisons degreewise. The termwise-adjunction theorem carries the units, counits and triangle identities to complexes; the localization universal property descends these transformations and their equalities, since the exact functors preserve quasi-isomorphisms. Thus, writing $r=v_{et}^*$ and $t=v_{proet}^*$ and the open units as $u^e,u^p$, we have
$$t(o_L)\,b_{v_{et,!}L}\,C_V(u^e_L)=u^p_{C_VL}.$$
This uses the specified $b,o$, rather than choices of isomorphisms with the same endpoints.

Original cited statements: lem-weil-pbc-comparison-pullback, lem-cbc-proetale-extension-zero-comparison, lem-sf-open-comparison-unit-normalization, lem-weil-pbc-extension-by-zero-exact, lem-weil-extension-by-zero-exact, prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact, lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-localization-universal-property, lem-sf-comparison-pullback-exact.

### Original Step 3 — assigned to lem-sf-derived-immersion-comparison-normalization

Let $e^e,e^p$ be the open counits. The preceding unit equation implies
$$e^p_{C_TM}\,v_{proet,!}(b_M)\,o_{rM}=C_T(e^e_M).$$
Indeed, transpose $C_T(e^e_M)o_{rM}^{-1}$ under the pro-etale open adjunction. Its transpose is
$$tC_T(e^e_M)\,t(o_{rM}^{-1})u^p_{C_VrM}
=tC_T(e^e_M)\,b_{v_{et,!}rM}C_V(u^e_{rM})
=b_M C_V\bigl(r(e^e_M)u^e_{rM}\bigr)=b_M.$$
The first equality is the unit normalization, the second naturality of $b$, and the third the etale triangle identity. Inverse transposition gives the displayed counit equation.

Original cited statements: lem-sf-open-comparison-unit-normalization, lem-weil-pbc-termwise-adjunction-homotopy.

### Original Step 4 — assigned to parent assembly Step 2

The closed comparison theorem gives the natural isomorphism
$$\alpha_N:C_S I_eN\xrightarrow{\sim}I_p C_VN$$
and the equation
$$k^p_{C_VN}\,c_{proet,*}(\alpha_N)\,\delta_H=C_V(k^e_N),$$
where $k^e,k^p$ are the closed counits and $\delta:C_Vc_{et,*}\xrightarrow{\sim}c_{proet,*}C_S$ is the specified closed direct-image comparison. Define
$$\gamma_M=I_p(b_M)\,\alpha_N:C_SJ_{et}M\longrightarrow I_pv_{proet}^*C_TM=J_{proet}C_TM.$$
Both factors are natural isomorphisms. The closed theorem applies because Step 1 proved exactly its bounded constructible input hypothesis; no assertion about closed ordinary restriction commuting with internal Hom is used.

Original cited statements: lem-weil-finite-duality-closed-comparison, lem-weil-pbc-comparison-pullback.

### Original Step 5 — assigned to lem-sf-locally-closed-closure-adjoint-realization (bound preservation), parent assembly Step 2 (definition of Delta and pasted counit)

For bounded-below $L$ set
$$\Delta_L=v_{proet,!}(\delta_L)\,o_{c_{et,*}L}.$$
This is exactly the named comparison in the statement: the closed map is [lem-weil-pbc-comparison-direct-image-canonical-mate], and the open map is [lem-cbc-proetale-extension-zero-comparison]. Since $c$ is finite [lem-weil-pbc-closed-immersion-finite], its exact etale direct image preserves the lower bound [lemma-weil-pbc-finite-direct-image-exact], also for constant-$A$ modules by the underlying-sheaf functor. The maps are therefore defined at every such $L$, in particular at $H$. By the composite adjunction formula,
$$\epsilon^\tau_M=e^\tau_M\,v_{\tau,!}(k^\tau_{v_\tau^*M}),$$
and the corresponding unit is the pasted unit. These are the adjunctions fixed in the statement.

Original cited statements: lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-closed-immersion-finite, lemma-weil-pbc-finite-direct-image-exact, def-weil-pbc-composite-adjunction.

### Original Step 6 — assigned to parent assembly Step 2

Expand $\gamma,\Delta$ and the pasted counit in the left side of the required equation. Naturality of $k^p$ at $b_M:C_VN\to v_{proet}^*C_TM$, followed by Step 4, gives
$$\begin{aligned}
\epsilon^p_{C_TM}F_p(\gamma_M)\Delta_H
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,v_{proet,!}\bigl(C_V(k^e_N)\bigr)\,o_{c_{et,*}H}\\
&=e^p_{C_TM}\,v_{proet,!}(b_M)\,o_N\,C_T\bigl(v_{et,!}(k^e_N)\bigr)\\
&=C_T(e^e_M)\,C_T\bigl(v_{et,!}(k^e_N)\bigr)
=C_T(\epsilon^e_M).
\end{aligned}$$
The second equality is naturality of $o$ at $k^e_N:c_{et,*}H\to N$; the third is precisely Step 3. This proves the counit identity for the specified comparisons, not merely existence of an abstract comparison. Transposition in $F_p\dashv J_p$ says equivalently that $\gamma_M$ is the unique transpose of $C_T(\epsilon^e_M)\Delta_H^{-1}$.

Original cited statements: lem-weil-finite-duality-closed-comparison, def-weil-pbc-composite-adjunction.

### Original Step 7 — assigned to lem-sf-locally-closed-closure-adjoint-realization

Identify $F_e$ with ordinary etale compact support for $s$. Let $\bar S$ be the scheme-theoretic closure of $S$ in $T$, with $u:S\hookrightarrow\bar S$ open and $i:\bar S\hookrightarrow T$ closed. Here $i$ is proper directly from the closed-immersion definition: affine base change is quotient by the extended ideal, hence closed; its diagonal is an isomorphism, and the quotient algebra is generated by $1$ as a module. The closure is finite type over $k$, since on the finite-type affine charts of $T$ its rings are quotients. The normalized comparison of [lem-sfb-etale-locally-closed-extension-comparison] is $v_!c_*\cong i_*u_!$ on sheaves. Both sides are exact: open extension is exact and closed direct image is exact by finiteness. Hence the termwise comparison descends to all derived complexes [lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-localization-universal-property]. In the closure compactification, [def-amb-etale-compact-support] gives $Rs_!=Ri_*u_!=i_*u_!$; exactness of $i_*$ means that applying it to a quasi-isomorphism into a K-injective resolution is a quasi-isomorphism, so this equality holds unboundedly as well. The adjoint exists by [thm-amb-etale-exceptional-adjoint]. Right-adjoint uniqueness, with its unit and counit normalization [lem-cat-right-adjoint-composition, def-weil-pbc-adjunction-conjugate], identifies $J_e$ with $s^\times$ compatibly with the chosen identification of left adjoints. On pro-etale categories the corresponding normalized identification $F_p\cong i_*u_!$ and factorization independence are supplied by [lem-sfb-locally-closed-extension-coherence].

Original cited statements: lem-sfb-etale-locally-closed-extension-comparison, lem-weil-pbc-extension-by-zero-exact, lem-weil-pbc-closed-immersion-finite, lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-localization-universal-property, def-amb-etale-compact-support, thm-amb-etale-exceptional-adjoint, lem-cat-right-adjoint-composition, def-weil-pbc-adjunction-conjugate, lem-sfb-locally-closed-extension-coherence, def-weil-closed-immersion, def-weil-proper-morphism.

### Original Step 8 — assigned to lem-sf-derived-immersion-comparison-normalization

First justify the termwise interpretation of the closed comparison. For either closed immersion $h=c$ or $h=i$, both $h_{e,*}$ and $h_{p,*}$ are exact: use closed finiteness and finite etale direct-image exactness, and the pro-etale ringed open/closed theorem. Their complements are quasi-compact by Noetherianity. The pullbacks and $C$ are exact as in Step 2. At the sheaf level form the $h_p^*\dashv h_{p,*}$ transpose $\delta_h^0$ of
$$C(\varepsilon^e_{h,L})a_{h,h_{e,*}L}^{-1}.$$
The module adjunction supplies this transpose. Termwise adjunction and localization carry its defining counit equation to derived categories; exact-functor factorization identifies $Rh_{\tau,*}$ with termwise $h_{\tau,*}$. Consequently the descended $\delta_h^0$ is the unique transpose defining $\delta_h$ in [lem-weil-pbc-comparison-direct-image-canonical-mate]. Thus the named derived comparison equals the termwise sheaf mate on $D^+$. Its sheaf counit equation is
$$\varepsilon^p_{h,C L}\,h_p^*(\delta^0_{h,L})\,a_{h,h_{e,*}L}=C(\varepsilon^e_{h,L}).$$
Both closed restriction counits are invertible by [lem-kun-04ca, lem-weil-pbc-proetale-ringed-open-closed]. The equation therefore says precisely that restriction of $\delta_h$ to the closed source is the identity under those counits and the specified $a_h$. This normalization holds termwise on complexes. The open comparison has the analogous normalization by Step 2.

Original cited statements: lem-weil-pbc-closed-immersion-finite, lemma-weil-pbc-finite-direct-image-exact, lem-weil-pbc-proetale-ringed-open-closed, lem-weil-pbc-noetherian-open-subscheme-noetherian, prop-weil-pbc-inverse-image-modules-exact, prop-weil-pbc-proetale-constant-exact, lem-sf-comparison-pullback-exact, lem-weil-pbc-ringed-topoi-module-adjunction, lem-weil-pbc-termwise-adjunction-homotopy, lem-weil-pbc-localization-universal-property, lem-weil-pbc-exact-functor-derived-factorization, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-kun-04ca, lem-sf-open-comparison-unit-normalization, lem-weil-pbc-comparison-pullback.

### Original Step 9 — assigned to lem-sf-locally-closed-closure-comparison-square

Write $E_\tau=i_{\tau,*}u_{\tau,!}$ for the closure compactification and $q_\tau:F_\tau\xrightarrow{\sim}E_\tau$ for Step 7's identifications, restricting to the identity on $S$. For $L\in D^+(S_{et},A)$ the closure comparison is
$$C_{\bar s,L}=i_{p,*}(o_{u,L})\,\delta_{i,u_{e,!}L}:C_TE_eL\xrightarrow{\sim}E_pC_SL.$$
This is exactly the specified $B_{s,L}$ in [lem-pur-bounded-site-adjunction-transpose], for compactification $(u,i)$: the proper comparison there is the counit-mate comparison for the closed $i$. Exactness identifies its derived direct image with $i_*$. Define
$$D_L=q_{p,C_SL}^{-1}\,C_{\bar s,L}\,C_T(q_{e,L}):C_TF_eL\longrightarrow F_pC_SL.$$
Step 8 and the open unit normalization show that both $D_L$ and $\Delta_L$ restrict to $1_{C_SL}$: each closed factor restricts by its counit, each open factor by its unit, and each $q_\tau$ by its stated identity normalization. The pullback-composition compatibility of [lem-weil-pbc-comparison-pullback] ensures these use the same identification $s_p^*C_T\cong C_Ss_e^*$ for both factorizations. Hence the endomorphism $D_L\Delta_L^{-1}$ of $F_pC_SL$ restricts to the identity. The restriction Hom bijection of [lem-sfb-locally-closed-extension-coherence], with both arguments $C_SL$, makes this endomorphism the identity. We have proved the required equality of named maps:
$$q_{p,C_SL}\,\Delta_L=C_{\bar s,L}\,C_T(q_{e,L}).$$

Original cited statements: lem-sfb-etale-locally-closed-extension-comparison, lem-sfb-locally-closed-extension-coherence, lem-pur-bounded-site-adjunction-transpose, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-sf-open-comparison-unit-normalization, lem-weil-pbc-comparison-pullback, lem-weil-pbc-proetale-ringed-open-closed.

### Original Step 10 — assigned to lem-sf-locally-closed-relative-transpose-normalization; dimension prerequisite in lem-sf-locally-closed-closure-adjoint-realization

Now compute the specified comparison-class transpose. Choose a nonnegative dimension bound for $\bar S$ by [lem-kun-dimension-finite-type], using $0$ if it is empty. Apply [lem-pur-bounded-site-adjunction-transpose] to $f=s$, compactification $(u,i)$ and $K=M$. Its hypotheses hold: these are finite-type $k$-schemes with the same finite coefficient $A$, $s$ is separated finite type, $M\in D^+$, and $s^\times M$ is bounded below by Steps 1 and 7. Put $B=J_eM$ and write
$$\rho_M=C_S\bigl(s^\times(\eta_M)\bigr)$$
under Step 7's counit-compatible $J_e\cong s^\times$. For $L\in D^+(S_{et},A)$ and $h:F_pC_SL\to C_TM$, full faithfulness of $C_T$ gives a unique $h_0:F_eL\to M$ with $h\Delta_L=C_T(h_0)$; $F_eL$ is bounded below by exactness. Let $g_0:L\to B$ be its etale adjoint. Step 6 and naturality of $\Delta$ give
$$\epsilon^p_{C_TM}F_p(\gamma_MC_Sg_0)=C_T(h_0)\Delta_L^{-1}=h.$$
Thus the ambient transpose of $h$ is $\gamma_MC_Sg_0$. For closure left adjoints take $a_e=h_0q_{e,L}^{-1}$ and $a_p=hq_{p,C_SL}^{-1}$. Step 9 gives
$$a_pC_{\bar s,L}=C_T(a_e).$$
Use the current statement's explicit Hom formula with $U_T=R\nu_{T,*}$ and the same closure compactification. Naturality of the comparison unit gives
$$U_T(a_pC_{\bar s,L})\eta_{T,E_eL}=U_TC_T(a_e)\eta_{T,E_eL}=\eta_Ma_e.$$
Its etale transpose is $s^\times(\eta_M)\operatorname{adj}_e(a_e)$. Conjugation by $q_e$ identifies $\operatorname{adj}_e(a_e)$ with $g_0$. Applying $C_S$ in the specified Hom formula therefore gives exactly $\rho_MC_Sg_0$. Thus both the explicit Hom formula and the cited transpose conclusion use the comparison unit and the named $B_{s,L}=C_{\bar s,L}$ of Step 9.

Original cited statements: lem-kun-dimension-finite-type, lem-pur-bounded-site-adjunction-transpose, thm-weil-pbc-site-comparison, def-weil-pbc-adjunction-conjugate, def-weil-pbc-composite-adjunction.

### Original Step 11 — assigned to lem-sf-locally-closed-relative-transpose-normalization

Since $\eta_M:M\xrightarrow{\sim}R\nu_{T,*}C_TM$ is invertible, define
$$\theta_M=C_S\bigl(s^\times(\eta_M)\bigr)\gamma_M^{-1}:J_pC_TM\xrightarrow{\sim}C_Ss^\times R\nu_{T,*}C_TM=G_s(C_TM),$$
with Step 7's adjoint identification understood. Step 10 proves that postcomposition by $\theta_M$ identifies the two Hom bijections. An arbitrary bounded-below etale-origin test object is isomorphic to $C_SL$; precomposing by this witness proves the same assertion for it, independently of the witness, as in [thm-sf-ambient-adjoint-class]. In particular the composite from $C_SJ_eM$ to the transported value is exactly $C_Ss^\times(\eta_M)$ under Step 7, as claimed. The unit is the image of the identity of a left-adjoint value under its Hom bijection, and the counit is the inverse image of an identity of a right-adjoint value wherever that comparison-class map is defined. Equality of the Hom bijections therefore identifies these maps. The ambient $F_\tau\dashv J_\tau$ units and counits are the pasted ones by the composite adjunction formula. This argument does not assert a compact-support adjunction on arbitrary pro-etale objects.

Original cited statements: thm-weil-pbc-site-comparison, thm-sf-ambient-adjoint-class, def-weil-pbc-composite-adjunction, lem-pur-bounded-site-adjunction-transpose.

### Original Step 12 — assigned to lem-sf-locally-closed-closure-comparison-square (left maps), lem-sf-locally-closed-relative-transpose-normalization (transport), parent Step 4 (conjugation and uniqueness)

Finally change the closed-then-open factorization. The normalized etale factorization maps are given by [lem-sfb-etale-locally-closed-extension-comparison], and the pro-etale maps by [lem-sfb-locally-closed-extension-coherence]. For any second factorization repeat Steps 8-9 with the same closure $(u,i)$. Each site's $q_\tau$ restricts to the identity, and its closed/open comparison is termwise with the specified normalization, so the same restriction Hom bijection gives
$$q'_{p}\Delta'=C_{\bar s}C_T(q'_e),\qquad q_p\Delta=C_{\bar s}C_T(q_e).$$
Cancelling the common closure map proves equality of the comparison paths after the canonical factorization identifications. No derived mate is being presumed to be a sheaf map: Step 8 established that equality before using it here. Conjugation of the normalized left-adjoint identifications gives canonical right-adjoint identifications, respecting identities and composition [def-weil-pbc-adjunction-conjugate]. Step 6 uniquely characterizes $\gamma_M$ as a counit transpose, so it respects these identifications. Their units and counits are the pasted ones by [lem-cat-right-adjoint-composition, def-weil-pbc-composite-adjunction]. Step 11's transported identification has the same coherence, since it is the image of the natural comparison unit under the normalized etale right adjoints followed by $C_S$. This proves independence of the factorization for the maps and adjunction data on the stated comparison class.

Original cited statements: lem-sfb-etale-locally-closed-extension-comparison, lem-sfb-locally-closed-extension-coherence, def-weil-pbc-adjunction-conjugate, lem-cat-right-adjoint-composition, def-weil-pbc-composite-adjunction, thm-weil-pbc-site-comparison.


## Historical validation storage failure — 2026-10-21

The required initial dry run and the repaired dry run both exited 1. Both failed exclusively because the server could not materialize its DAG baseline: `Could not verify the DAG baseline: [Errno 28] No space left on device`. The initial temporary baseline was `/tmp/sheaf-dag-base-pgn3dxxb/`; the repaired run was `/tmp/sheaf-dag-base-3033z0_c/`. Both invocations were polled to exit, with only one active at a time. No push was attempted. This is a server storage failure, not a failed mathematical or citation diagnostic. The repaired five node files, current verbatim citations, original argument archive, logged search results and citation revalidation snapshot are retained for the next retry. The next action after server storage is restored is the required deliver.py --no-push, followed by deliver.py only on OK.


## Resumed validation after storage recovery — 2026-10-21

The required first action on this retained repair was the prescribed dry run. It exited 0 and printed `OK (not pushed)` at 8951f5e176b; the earlier server storage failure no longer occurs. This retry retains the mathematical repair above rather than reverting it or replacing it with an unchanged copy of the returned delivery.

I compared all five sandbox node files with the current read-only DAG. The four extracted nodes are still new. The existing parent differs only in proof, proof_deps, proof_origin and split_report; its statement and maintainer-owned fields are unchanged. Every one of the 35 existing direct statement/proof dependencies agrees verbatim with the retained revalidation snapshot; the other four dependency ids are the new sandbox nodes. I re-read the current scheme-theoretic-image statement and its blueprint_update, and Stacks morphisms.tex lemmas 01R6 (lemma-scheme-theoretic-image), 01R8 (lemma-quasi-compact-scheme-theoretic-image) and 01RG (lemma-quasi-compact-immersion). The repaired three closure interfaces use exactly that image, its inclusion and canonical factor map. Quasi-compactness follows from the Noetherian ambient scheme, so identifying its defining ideal with the raw kernel is valid, and the canonical source-to-image map is open. This preserves nonreduced closed images, including the (t^2) example above.

I re-read the four new statements, the parent assembly, the retained twelve-step argument, and the current closed comparison, pullback comparison, extension coherence, composite-adjunction, conjugation, right-adjoint-composition and bounded-transpose statements. The counit calculation still uses the actual Plus mate transported through the bounded-below lift; the closure comparison square has the correct direction; the relative transpose fixes the chosen-compactification Hom formula rather than an arbitrary isomorphism. All eleven step/node entries in citations.json are complete and verbatim current statement excerpts. The parent still has 2560 proof characters, no step over 2000 characters, and four separate unsplit statement-only tasks. No mathematical change or new search question is needed, so the genuine retained search log and results are reused. The final report version is validated again before the push.
