## Files written

- dag/nodes/sec-trace-formula/lem-trf-adjunction-standard-simplicial-homotopy.json: repaired item, split, statement unchanged byte for byte; five assembly steps, 2531 characters in total.
- dag/nodes/sec-trace-formula/lem-trf-adjunction-right-image-extra-degeneracies.json: statement, unsplit, no Mathlib match; unit extra degeneracies on the right-adjoint image.
- dag/nodes/sec-trace-formula/lem-trf-comonad-counit-section-right-degeneracies.json: statement, unsplit, no Mathlib match; arbitrary split comonad counit gives right extra degeneracies.
- dag/nodes/sec-trace-formula/lem-trf-simplicial-reversal-extra-degeneracies-homotopy.json: statement, unsplit, no Mathlib match; conversion of right to left contraction data and reversal of all homotopy prism identities.
- citations.json: one entry for each node used by each assembly step; quotes are literal substrings of the supplied or existing node statements.

## Attachments

None. I searched all lean/WeilConjectures for the item tag and standardSimplicial/extraDegeneracy, and read lean/Sheaf/CategoryTheory/AdjunctionStandardSimplicialHomotopy.lean. CategoryTheory.Adjunction.exists_standardSimplicialHomotopy, line 88, has sorry at line 105. Its four abbreviations do not prove the item. The closed upstream presheaf-Cech extraDegeneracy_exact proves a specialized exactness assertion, not this statement or one of the proposed general auxiliary statements.

## WANTED

None. All source material used is present locally.

## What was wrong and what changed

The return asks to spread a 4316-character proof across at least two genuinely separate statement-only obligations, while retaining the item statement and keeping the assembly under 3000 characters. The sandbox initially held only dispatcher .brief marker files, without the purported retained node/report/searches. I therefore copied the current repository node, which contains the seven returned proof steps and its previous citations/search records. No earlier local report or log existed to reuse. The historical mathlib_searches and all existing audit, Lean, blueprint and import fields of the item are retained; the delivery tool builds against current server main.

The three new obligations have statement lengths 1173, 1027 and 1536 characters. They cover disjoint arguments: left unit identities, right split-counit identities, and index reversal of contraction data and homotopies. They neither reassert a homotopy-equivalence clause nor move the entire theorem into one new node. The right-degeneracy node is stated for an arbitrary section of any comonad counit, which isolates the real argument from the adjunction-specific triangle identity. The elementary triangle/comonad checks and application of the existing construction stay in the assembly. Each new node has proof=[], proof_deps=[], proof_origin=null and status=unsplit; the arguments below are handoff information for future workers, not proofs smuggled into statement-only nodes.

## Unfinished work

No unfinished repair action. The three auxiliary statements are intentionally unproved DAG leaves for subsequent stage-1 workers. No Lean was written and no compiler, Lake or library build was run.

## Review by Q34

I read Stacks simplicial.tex, Situation 08N9 (situation-adjoint-functors), Lemma 08NC (lemma-standard-simplicial), and Lemma 08ND (lemma-standard-simplicial-homotopy), including both proofs. I also read Example 0G5M and Lemma 0G5N (lemma-godement). Stacks calls the left adjoint U and the right adjoint V; our F and U have exactly those respective roles. No products, additivity, existence of limits or faithful-forgetful hypothesis is present or used. The chapter and unit records were read: these are generic ordinary-category inputs beneath the existing local-term branch, not a new trace-formula route. I read the three blueprint levels in SETUP.md and preserved the ancestor/via chain supplied by blueprint_refs.py ancestor.

For the item I retained all of its statement, including the degree-zero unit section, its degeneracy extension and the Set cylinder interpretation. For the left-extra-degeneracy node I checked the unit at every object UG^(n+1)a has exactly the required type, including augmented degree -1, and that all five equations are the arbitrary-category prism node's hypotheses. For the right-extra-degeneracy node I checked the hypothesis is only e_b v=1, not a hidden coalgebra equation: commutation with faces and degeneracies is naturality of the corresponding transformations evaluated at v. Its naturality in (b,v) explicitly supplies naturality on free objects because F eta is natural. For the reversal node I checked r(alpha) is monotone, preserves composition and squares to the identity; r sends faces and degeneracies to the reversed indices and fixes q_n. The conclusion includes conversion of all right contraction equations and the endpoint/face/degeneracy identities for H~_j=H_(n-j), not just an unspecified assertion that homotopy transports. These are the separate arguments the old proof actually needed; the auxiliary source places identify them as the explicit extra-degeneracy replacement of the Godement-two-maps invocation in 08ND, not as verbatim lemmas of Stacks. proof_origin.by remains agent.

Assembly step 1 is the old elementary calculation: the left triangle at Ua and F of the right triangle give the two counit equations; naturality of eta at eta_Ua gives coassociativity. It uses only the item's own hypotheses and so needs no non-elementary cited lemma.

Assembly step 2 uses the full statement of lem-trf-comonad-simplicial-object: its three equations are exactly step 1, and its conclusion gives the augmented object in endofunctors and explicitly gives natural evaluation. def-trf-comonad-standard-resolution defines exactly the supplied powers/operators predicate needed by the new nodes; it is not cited for existence. def-weil-pbc-simplicial-object defines functors and natural transformations, so evaluation uses exactly that notion. I opened and read all three statements.

Assembly step 3 uses lem-trf-adjunction-right-image-extra-degeneracies for the actual equations and their parameter naturality; the supplied resolution was constructed in step 2. I compared these equations one by one with lem-coef-simplicial-extra-degeneracy-prism, whose statement explicitly gives a_n=Z(q_n)h_-1, ea=1 and a homotopy from ae to 1. The Set-only lem-coef-extra-degeneracy-contraction is used only after specializing S=Set, exactly where its statement gives the cylinder interpretation. Neither Set-only hypothesis nor a preadditive contraction theorem is used for arbitrary categories.

Assembly step 4 uses the left triangle at s to verify the sole extra hypothesis e_b v=1 for the right-degeneracy node with T=G, b=Fs, v=F eta_s. Its conclusion states every right equation and naturality. The reversal node explicitly accepts that same list of equations and concludes the left equations for W^r; there is no unproved identification of objects or extra section choice. I checked the equality d_0^r t_n=d_(n+1)t_n, where the face is on degree n+1, and the separate augmented condition d_1^r t_0=d_0 t_0=v e_0.

Assembly step 5 applies the prism node in A to these left equations. Its conclusion gives the section and homotopy in the required direction on W^r. The reversal node explicitly fixes q_n and transports a homotopy from f^r to g^r to one from g to f; taking f=ae and g=1 therefore yields 1_W to ae. The two extra-degeneracy nodes' naturality clauses, the functorial reversal clause and the explicit prism construction make the same proof valid directly in the parameter functor categories. I retained both extra-degeneracy nodes in this step's uses because it explicitly uses their naturality clauses. citations.json gives the actual statements for each of these uses; no step uses information merely found in another node's proof.

Small-case checks: for the identity adjunction/comonad all powers and extra degeneracies are identities and the equations reduce to identities. In degrees 0 and 1 the left equations read U epsilon eta=1 and d_1 eta=eta e_0; the right equations read e_b v=1, d_1 T(v)=1 and d_0 T(v)=v e_b. The last follows from naturality of e and requires no coassociativity of v. Reversal on [0] fixes the only vertex and on [1] interchanges the two face indices. For a degree-zero homotopy, d_0 H~_0=d_1^r H_0=f and d_1 H~_0=d_0^r H_0=g: these are exactly the convention for a homotopy from g to f. For the strict face cases substitute i -> n+1-i and j -> n-j; i<j becomes the opposite strict face inequality, and the middle face identity stays the middle one with the two sides interchanged. For degeneracies the substitution i -> n+1-i swaps i<=j with the other degeneracy case and exchanges their shifted indices. No inverse of a morphism, tensor, zero object or finite-product assumption enters these verifications.

I checked delivery-errors B1-B10: new nodes are statement-only, introduce all objects, cite the standard-resolution/simplicial/homotopy notions, carry single TeX escaping and Stacks tags with their labels, do not use a tag as a definition, carry exact logged searches, have explicit blueprint ancestry and no attachment claim. B6/B8 introduce no new Mathlib leaf. C1-C8: every non-elementary assembly input is a used node, no definition is used for an existence theorem, all cited statements were read, and no new node depends on the item or a downstream result. All new nodes inherit the same chapter/unit; existing off-unit inputs are Mathlib leaves, so no new tool-route exception is needed. D1-D5: the three obligations isolate the actual computations and indexing argument rather than the item's conclusions, with no circular induction or omitted standard comparison. E1-E7: all hypotheses were checked above, especially arbitrary categories, augmented degree -1, naturality and homotopy orientation. I found no false item statement and made no statement correction. No assembly step exceeds 2000 characters.

Mathlib searches: I ran msearch.py for every new obligation using LeanFinder, Loogle, LeanSearch and grep, and read their returned candidates. Two semantic phrasings were tried for each. One free-object LeanSearch query was rate limited and is recorded as unavailable. I read ExtraDegeneracy.lean:72-102,126-174 and Homotopy.lean:48-67: the existing leaf contracts supplied data, but does not construct the unit or split-counit identities. Adjunction.toComonad at Monad/Adjunction.lean:67 only constructs a comonad. RepresentationTheory/Homological/Resolution.lean:141,160 concerns a specific group universal cover; it does not cover arbitrary adjunctions. I read SimplicialObject/Op.lean:36-89: object reversal and its face/degeneracy formulas exist, but the new node also requires right-extra-degeneracy conversion and endpoint-reversing homotopy transport, which are not in that API. Chain-complex Homotopy.symm, ShortComplex.Homotopy.op/unop and topological path symmetry have different domains and hypotheses. Monad/Algebra.lean's coalgebras impose a coassociativity law on v not needed here; Equalizer.lean's topMap/bottomMap do not assert simplicial identities. Thus all three remain unsplit, not Mathlib leaves.

Duplicate search: I searched the whole DAG for 08NC/08ND/08N9, extra degeneracies, comonads, ordinal reversal and opFunctor; blueprint_refs.py search returned no matching blueprint node for extra degeneracy, ordinal reversal, adjunction simplicial or comonad. Its broader reversal search found only two unrelated reciprocal-polynomial statements. I read the ordinary and infinity-category bar candidates, including lem-coef-infinity-free-module-bar and lem-coef-adjunction-free-simplicial-resolution. They assert coherent realizations in different categories and do not give these general ordinary-category right identities or prism reversal. The pairwise tag overlaps are recorded below.

The repair changes the old seven-step proof to five short assembly steps and adds three independent obligations. It leaves no asserted complete proof in any new node. The following lossless mapping records every old argument so a later worker can resume the corresponding computation, rather than recover it from a compressed summary.

## Original arguments and their new locations

### Old step 1

New location: Assembly step 1, retained verbatim (comonad equations).

Preserved argument:

Write composites in functional order. The triangle identities give $\epsilon_{Ga}\delta_a=1_{Ga}$ and $G(\epsilon_a)\delta_a=1_{Ga}$: the first is the left-adjoint triangle at $Ua$, and the second is $F$ applied to $U\epsilon_a\circ\eta_{Ua}=1_{Ua}$. Naturality of $\eta$ at $\eta_{Ua}$ says $UF(\eta_{Ua})\eta_{Ua}=\eta_{UFUa}\eta_{Ua}$; applying $F$ gives $G(\delta_a)\delta_a=\delta_{Ga}\delta_a$. Thus $G,\epsilon,\delta$ satisfy exactly the three equations of the comonad construction.

### Old step 2

New location: Assembly step 2, using the existing construction node (powers, operators, augmentation, evaluation and naturality).

Preserved argument:

Apply [lem-trf-comonad-simplicial-object] with $\mathcal C=\mathcal A$, $T=G$, $e=\epsilon$, $c=\delta$, using the equations just checked. Its faces and degeneracies are exactly those of the item, and its augmentation has degree-zero map $\epsilon_a$. It constructs a simplicial object in endofunctors; evaluation at $a$ therefore gives the desired augmented simplicial object, and evaluation on a morphism $a\to b$ gives naturality, in the functor and natural-transformation sense of [def-weil-pbc-simplicial-object].

### Old step 3

New location: lem-trf-adjunction-right-image-extra-degeneracies: each unit/naturality/augmented-degree identity is part of its statement; assembly step 3 uses it.

Preserved argument:

Put $Z_n=UG^{n+1}a$ and $Z_{-1}=Ua$, and set $h_n=\eta_{UG^{n+1}a}:Z_n\to Z_{n+1}$ for $n\geq-1$ (so $G^0a=a$). The right-adjoint triangle gives $e_0h_{-1}=1$ and $d_0h_n=1$. Every face with index $i+1$ of $Z$ is $UF$ applied to its face with index $i$ one degree lower. Naturality $UF(v)\eta=\eta v$, with $v=U\epsilon_a$, gives $d_1h_0=h_{-1}e_0$; with $v=d_i:Z_{n+1}\to Z_n$, it gives $d_{i+1}h_{n+1}=h_nd_i$. The same naturality with $v=s_i:Z_n\to Z_{n+1}$ gives $s_{i+1}h_n=h_{n+1}s_i$. These are all the extra-degeneracy equations, with $0\leq i\leq n+1$ in the face relation and $0\leq i\leq n$ in the degeneracy relation.

### Old step 4

New location: Assembly step 3, applying the existing prism and Set contraction leaves; no work is deferred here.

Preserved argument:

Apply [lem-coef-simplicial-extra-degeneracy-prism] in $\mathcal S$ to the augmented object $Z$ and the maps of step 3. Every hypothesis is precisely one of the equations established there. It gives a simplicial section $a_n=Z(q_n)\eta_{Ua}$, $q_n:[n]\to[0]$, with $ea=1$ and a homotopy $ae\simeq1_Z$. Thus $UX_\bullet(a)\to\operatorname{const}(Ua)$ is a homotopy equivalence, with the stated degree-zero section and its iterated degeneracies. When $\mathcal S=\mathrm{Set}$, [lem-coef-extra-degeneracy-contraction] applies to the same equations and supplies the equivalent cylinder description $Z\times\Delta^1\to Z$.

### Old step 5

New location: lem-trf-comonad-counit-section-right-degeneracies: generalized to an arbitrary counit section; assembly step 4 keeps the free-object triangle check.

Preserved argument:

For $s\in\mathcal S$ put $b=Fs$, $W_n=G^{n+1}b$, $W_{-1}=b$, and $v=F\eta_s:b\to Gb$. The left-adjoint triangle gives $\epsilon_bv=1_b$. Define $t_{-1}=v$ and $t_n=G^{n+1}(v):W_n\to W_{n+1}$. Then $d_{n+1}t_n=G^{n+1}(\epsilon_bv)=1$. Naturality of the face transformation $G^{n+1}\to G^n$ at $v$ gives $d_it_n=t_{n-1}d_i$ for $0\leq i\leq n$; in degree zero this reads $d_0t_0=t_{-1}e_0$. Naturality of the degeneracy transformation $G^{n+1}\to G^{n+2}$ at $v$ gives $s_it_n=t_{n+1}s_i$ for $0\leq i\leq n$. Together with $e_0t_{-1}=1$ these are the right-hand versions of the extra-degeneracy equations.

### Old step 6

New location: lem-trf-simplicial-reversal-extra-degeneracies-homotopy: first two clauses, including the full conversion of the extra equations.

Preserved argument:

Reverse the ordinal indices: define $r(\alpha):[m]\to[n]$ for $\alpha:[m]\to[n]$ by $r(\alpha)(j)=n-\alpha(m-j)$. It is order preserving, preserves compositions, and $r^2=1$. Precomposing $W$ by $r^{\mathrm{op}}$ gives $W^r_n=W_n$ with $d_i^r=d_{n-i}$ and $s_i^r=s_{n-i}$ on degree $n$. The maps $t_n$ of step 5 are now left extra degeneracies: $d_0^rt_n=d_{n+1}t_n=1$, $d_1^rt_0=d_0t_0=t_{-1}e_0$, and the face and degeneracy commutation relations follow by substituting $i\mapsto n+1-i$ and $i\mapsto n-i$, respectively, in step 5. The augmentation and its degree-zero section are unchanged.

### Old step 7

New location: lem-trf-simplicial-reversal-extra-degeneracies-homotopy: final clause, all endpoint/strict-face/middle-face/degeneracy checks; assembly step 5 uses the existing prism leaf and this transport. Naturality is recorded in all three auxiliary statements.

Preserved argument:

Apply [lem-coef-simplicial-extra-degeneracy-prism] in $\mathcal A$ to $W^r$. It yields a section with $ea=1$ and a homotopy between $ae$ and $1_{W^r}$. Undo ordinal reversal: the section still has components $W(q_n)v$, since $r(q_n)=q_n$. If $H_j^n$ are the homotopy components, use $\widetilde H_j^n=H_{n-j}^n$ for $W$. In the prism identities displayed in the cited node, substituting $d_i^r=d_{n-i}$ and $s_i^r=s_{n-i}$ swaps the two endpoint identities, swaps the two strict face cases and the two degeneracy cases, and preserves the middle face identity. Hence these components give a homotopy between $1_W$ and $ae$. This proves the second homotopy equivalence. The unit, counit and their functorial powers are natural, so the constructions in both assertions are natural in their parameters; no limits, products in the categories, or additivity were assumed.

## Not duplicates

lem-trf-adjunction-right-image-extra-degeneracies vs def-trf-comonad-standard-resolution: the existing node defines a predicate on a supplied resolution; it asserts no extra-degeneracy identity or homotopy transport.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-trf-cotangent-resolution-coherence: the existing node compares cotangent complexes of polynomial algebra resolutions; it does not state the ordinary-category contraction computations.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-trf-adjunction-standard-simplicial-homotopy: the existing item constructs the resolution and concludes both homotopy equivalences; this new node only supplies a strictly smaller, independent identity/transport argument used by its assembly.

lem-trf-adjunction-right-image-extra-degeneracies vs def-trf-endofunctor-powers: the existing node only defines iterative endofunctor powers, without extra-degeneracy or homotopy identities.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-trf-comonad-simplicial-object: the existing node constructs the simplicial object and augmentation; it asserts no contraction data or reversal of homotopies.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-trf-simplicial-operators-reconstruction: the existing node reconstructs a simplicial object from given simplicial identities and tests simplicial morphisms; it neither constructs these extra identities nor transports prism homotopies.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-per-etale-godement-supported-exact-model: the existing node is a sheaf-theoretic cosimplicial supported exact model with cohomology/tensor conclusions, not an ordinary-category simplicial extra-degeneracy/reversal statement.

lem-trf-comonad-counit-section-right-degeneracies vs def-trf-comonad-standard-resolution: the existing node defines a predicate on a supplied resolution; it asserts no extra-degeneracy identity or homotopy transport.

lem-trf-comonad-counit-section-right-degeneracies vs lem-trf-cotangent-resolution-coherence: the existing node compares cotangent complexes of polynomial algebra resolutions; it does not state the ordinary-category contraction computations.

lem-trf-comonad-counit-section-right-degeneracies vs lem-trf-adjunction-standard-simplicial-homotopy: the existing item constructs the resolution and concludes both homotopy equivalences; this new node only supplies a strictly smaller, independent identity/transport argument used by its assembly.

lem-trf-comonad-counit-section-right-degeneracies vs def-trf-endofunctor-powers: the existing node only defines iterative endofunctor powers, without extra-degeneracy or homotopy identities.

lem-trf-comonad-counit-section-right-degeneracies vs lem-trf-comonad-simplicial-object: the existing node constructs the simplicial object and augmentation; it asserts no contraction data or reversal of homotopies.

lem-trf-comonad-counit-section-right-degeneracies vs lem-trf-simplicial-operators-reconstruction: the existing node reconstructs a simplicial object from given simplicial identities and tests simplicial morphisms; it neither constructs these extra identities nor transports prism homotopies.

lem-trf-comonad-counit-section-right-degeneracies vs lem-per-etale-godement-supported-exact-model: the existing node is a sheaf-theoretic cosimplicial supported exact model with cohomology/tensor conclusions, not an ordinary-category simplicial extra-degeneracy/reversal statement.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs def-trf-comonad-standard-resolution: the existing node defines a predicate on a supplied resolution; it asserts no extra-degeneracy identity or homotopy transport.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-trf-cotangent-resolution-coherence: the existing node compares cotangent complexes of polynomial algebra resolutions; it does not state the ordinary-category contraction computations.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-trf-adjunction-standard-simplicial-homotopy: the existing item constructs the resolution and concludes both homotopy equivalences; this new node only supplies a strictly smaller, independent identity/transport argument used by its assembly.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs def-trf-endofunctor-powers: the existing node only defines iterative endofunctor powers, without extra-degeneracy or homotopy identities.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-trf-comonad-simplicial-object: the existing node constructs the simplicial object and augmentation; it asserts no contraction data or reversal of homotopies.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-trf-simplicial-operators-reconstruction: the existing node reconstructs a simplicial object from given simplicial identities and tests simplicial morphisms; it neither constructs these extra identities nor transports prism homotopies.

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-per-etale-godement-supported-exact-model: the existing node is a sheaf-theoretic cosimplicial supported exact model with cohomology/tensor conclusions, not an ordinary-category simplicial extra-degeneracy/reversal statement.

lem-trf-adjunction-right-image-extra-degeneracies vs lem-trf-polynomial-augmentation-boundary: the latter concerns only polynomial algebras over a commutative ring and concludes an underlying-set homotopy equivalence, quasi-isomorphism and boundary lifting; it does not state the unit extra-degeneracy equations for an arbitrary adjunction or their naturality in the parameter.

lem-trf-comonad-counit-section-right-degeneracies vs lem-trf-polynomial-augmentation-boundary: the latter treats the polynomial-algebra adjunction and its augmentation, not an arbitrary comonad with an arbitrary counit section; it states none of the right extra-degeneracy equations or naturality for pairs (b,v).

lem-trf-simplicial-reversal-extra-degeneracies-homotopy vs lem-trf-polynomial-augmentation-boundary: the latter asserts polynomial-resolution homotopy equivalence and boundary lifting, not ordinal reversal, conversion of right contraction data, or endpoint-reversing transport of a homotopy in an arbitrary category.

## Validation

Server dry run passed: deliver.py --no-push exited 0 and printed OK (not pushed), preflight passed, at 9b0e66459b5. This includes the server DAG and split checks. All item statement text is byte-identical to current main; only proof, proof_deps and split_report changed. Only one deliver.py invocation was active, and it exited before the push invocation.


## Promotion-return repair, 2026-10-22

This section addresses the current return, branch head 12c5ffff247: the independent reader approved the split, but landing refused the side completion because it had not been promoted into the live DAG. The earlier report sections describe the preceding mathematical re-split and are retained as history and handoff material, not as a claim that the present return requested further auxiliary nodes.

I resumed the retained sandbox, including its three new nodes, citations, report and searches.jsonl. No interrupted delivery process was still active. I ran the required dry run before edits; it exited 0 with OK (not pushed), preflight passed, at 3b1388587dc. deliver.py fetches current origin/sheaf-dag and reconstructs the delivery on that base rather than re-pushing the returned commit. The original-item.json snapshot and current read-clone item agree in every field. Only the item's proof, proof_deps and split_report differ in this sandbox. The three auxiliary ids remain absent from the current read-clone DAG.

I re-read all five existing cited statements: def-trf-comonad-standard-resolution, def-weil-pbc-simplicial-object, lem-trf-comonad-simplicial-object, lem-coef-simplicial-extra-degeneracy-prism and lem-coef-extra-degeneracy-contraction, as well as all three supplied auxiliary statements. No citation now points at a merged node; the three existing Mathlib leaves retain that status. All 12 citations.json entries still quote literal substrings of the current statements. The comonad construction explicitly includes natural evaluation, the resolution definition only defines the supplied-operators predicate, the arbitrary-category prism leaf gives exactly the needed section and homotopy orientation, and the Set contraction leaf is used only for Set. No hypothesis or dependency replacement is required by the current statements.

I also re-read the source passages in simplicial.tex for 08NC, 08ND and 0G5N, and the relevant Mathlib ExtraDegeneracy, Homotopy, Op and Adjunction source excerpts already identified by the retained search results. I reused the recorded searches, without inventing or repeating queries. There is still no project attachment: the only general exists_standardSimplicialHomotopy declaration is in Sheaf and ends in sorry; the WeilConjectures hits concern specialized presheaf-Cech exactness. The small-case and reversal-index checks in Review by Q34 above still apply to these unchanged auxiliary statements.

To make the section clause explicit in the rebased assembly, step 3 now states that q_0 is the identity and every q_n is a composite of codegeneracies. Consequently its degree-zero section is exactly eta at Ua, and its higher sections are its degeneracy extension; this uses only the cited section formula and the definition of the simplex category. The statement, three new obligations and all other accepted arguments are preserved. The assembly remains below 3000 characters and no step exceeds 2000. The promotion itself belongs to L; this delivery supplies the requested current-base split for that landing. Final validation below records the rerun after these report and assembly updates.


## Current-base retry after the promotion return

The required initial dry run for this retry exited 1 before building the delivery: since the retained report was written, Q18 added lem-trf-polynomial-augmentation-boundary, which shares Tag 08ND with all three auxiliary sources. I opened its complete node, including its statement and dependency lists. Its conclusion concerns the polynomial-algebra resolution and the relation between quasi-isomorphisms and boundary lifting; none of its clauses supplies the unit equations, arbitrary split-counit equations, or ordinal-reversal transport required here. I added the three specific comparisons under Not duplicates. This is a current-DAG repair to the report, not an unchanged re-push of the returned branch.

For this retry I compared original-item.json with the current read-clone item: they agree in every field. The retained sandbox item differs from that baseline only in proof, proof_deps and split_report. I re-read all five existing cited statements and all three auxiliary statements in full, rechecked all 12 literal citation quotes, and verified the statement is unchanged. No cited statement requires a mathematical adjustment; the newly detected shared-tag node requires only the duplicate analysis just supplied. I also re-read Stacks 08NC, 08ND and the comonad construction 0G5N, as well as the recorded Mathlib candidate excerpts in ExtraDegeneracy.lean, SimplicialObject/Op.lean, SimplicialObject/Homotopy.lean and Monad/Adjunction.lean. The only general adjunction theorem still ends in sorry in Sheaf; the whole WeilConjectures search finds only specialized presheaf-Cech results. The retained search log was read and reused without adding unrun searches. The degree-zero and degree-one, identity-comonad and reversal endpoint checks in Review by Q34 remain valid.

The three retained new obligations remain statement-only and absent from the read-clone DAG. The assembly is 2411 characters with no step over 2000 characters. The current delivery tool constructs a fresh commit on current origin/sheaf-dag, preserving current maintainer-owned fields; L remains responsible for promotion into the live queue DAG. The earlier validation commit ids above are historical; the following final validation applies to this retry.


## Final validation of the current-base retry

The dry run completed successfully at 2467919863a, as recorded by the durable .stage1-ready.json receipt written only after server preflight passes. After the provider interruption I checked that no delivery invocation remained active and verified every receipt input hash against the retained sandbox. All inputs matched; no second dry run was launched while the first was active. The new polynomial-boundary duplicate comparisons were included in this successful validation. This report records that result before the final push, whose command also runs server preflight.


## Promotion-return repair, 2026-10-23

I resumed the retained delivery rather than recreating it. The required initial dry run exited 0 with `OK (not pushed)` at e5231a29a2f. It reconstructed the delivery on the current server base and passed server preflight. Comparing the retained original-item.json with the current read-clone item found no field changes; comparing the sandbox item with that current item found only proof, proof_deps and split_report changes. The three auxiliary ids remain absent from the current read-clone DAG. The earlier returned-head narrative above is retained as history; the present report and assembly changes require a fresh dry run before pushing.

I re-read the complete statements of def-trf-comonad-standard-resolution, def-weil-pbc-simplicial-object, lem-trf-comonad-simplicial-object, lem-coef-simplicial-extra-degeneracy-prism, lem-coef-extra-degeneracy-contraction and all three auxiliary nodes. The present citation file has all 12 step/node pairs, each quoting a literal substring of the corresponding current statement. Construction and evaluation in step 2 still follow the comonad node's explicit conclusion; the three hypotheses of that node are established by step 1. Step 3 still matches the left-extra-degeneracy list exactly and restricts the cylinder interpretation to sets. Step 4 verifies the sole split-counit hypothesis by the left triangle, and the reversal statement explicitly converts exactly these right equations. Step 5 uses its endpoint-reversing homotopy conclusion with f=ae and g=1. No cited node is merged.

I found and repaired a C4 issue in assembly step 5: its naturality justification referred to explicit prism formulas, but lem-coef-simplicial-extra-degeneracy-prism's statement asserts existence of a homotopy and does not state these formulas or a naturality theorem for a chosen pointwise homotopy. The revised assembly applies that same arbitrary-category theorem directly in Fun(A,S) and Fun(S,A). The first extra-degeneracy statement already asserts its identities in Fun(A,S). For the free-object parameter, naturality of eta gives GF(f) F(eta_s) = F(eta_t) F(f) for f:s→t, by applying F to UF(f) eta_s = eta_t f. Thus s↦(Fs,F eta_s) is a functor of the split-counit pairs of the second auxiliary statement, so its naturality clause gives the right-extra-degeneracy data in Fun(S,A). The reversal node explicitly commutes with evaluation in a parameter functor category. Applying the prism theorem there produces a section and homotopy whose components are natural transformations, and evaluation gives the desired parameterwise constructions. This uses the cited statements alone; it adds no new lemma, hypothesis, or source route and changes none of the new obligations.

The source review for this retry covered simplicial.tex Situation 08N9, 08NC and 08ND and the comonad equations of 0G5N, and the recorded Mathlib candidates in ExtraDegeneracy.lean, SimplicialObject/Op.lean, SimplicialObject/Homotopy.lean and Monad/Adjunction.lean. The retained searches.jsonl was read in full and reused: no query or result was fabricated or repeated. The upstream project search still supplies no attachment, and the general declaration in Sheaf still ends in sorry. The existing same-tag polynomial-augmentation-boundary node remains a specialized ring-theoretic conclusion, as recorded by the three Not duplicates comparisons.

I rechecked delivery-errors B–E against this change and the unchanged auxiliary statements. The ordinary-category setting allows both parameter functor categories without a small-colimit or product hypothesis. The identity adjunction, degrees 0 and 1, split counit without a coalgebra equation, and reversal of the two degree-zero endpoints still pass the checks recorded in Review by Q34. The three new nodes remain statement-only, no new statement is needed for the elementary naturality calculation, the target statement is unchanged, and all original proof arguments remain available above. The assembly is 2531 characters and each step is below 2000 characters. Promotion into the live queue DAG remains the maintainer's landing action; this delivery supplies the repaired assembly and the current-base validation for it.


## Current promotion-return repair and review, 2026-10-23

This retry addresses L's current refusal to land a side completion not yet promoted to the live queue DAG. I retained the supplied split, report, three statement-only nodes, citations and complete searches.jsonl; the required initial dry run exited 0 at 42564e7eef8. The current original-item.json and read-clone item agree in every field; the retained sandbox differs only in proof, proof_deps and split_report. The delivery tool fetches origin/sheaf-dag again immediately before constructing the delivery and preserves its maintainer-owned fields, so this is a rebuilt current-base delivery rather than a re-push of the returned commit. Promotion remains L's action, as the return explicitly says.

I opened all five existing cited statements and all three retained auxiliary statements again. The citation audit verifies exactly the 12 step/node pairs and literal quotes; no cited node is merged. Step 1 proves the three comonad identities directly from the stated triangles and unit naturality. Step 2 uses the construction node's explicit simplicial-object, augmentation and natural-evaluation conclusions, while the standard-resolution definition supplies only the predicate. Step 3 uses the unit-equation node and the arbitrary-category prism statement, with the Set-only cylinder statement confined to sets. Step 4 checks epsilon_b v = 1 at b=Fs by the left triangle before using the split-counit node, and reversal converts its precise right-equation list to the prism hypotheses. Step 5 uses the reversal node's endpoint-swapping conclusion.

I revised step 5 to include the precise parameter equation GF(f) F(eta_s) = F(eta_t) F(f). It is F applied to unit naturality, so it needs no new lemma. This shows that the parameters form a diagram of the very split-counit pairs whose naturality the auxiliary statement supplies. The prism applications take place in the two ordinary functor categories; evaluation then supplies the desired natural families. Thus this retry changes the mathematical assembly explicitly, without relying on an unstated naturality theorem for a pointwise choice. All other retained arguments and all three new statements are preserved. The assembly has 2635 characters and its largest step has 818, below both limits.

Sources re-read: simplicial.tex 0G5M/0G5N, 08N9, 08NC and 08ND, and the retained Mathlib candidates ExtraDegeneracy.lean, SimplicialObject/Op.lean and SimplicialObject/Homotopy.lean. The recorded searches were read and reused without adding or repeating a query. The whole WeilConjectures attachment search still finds only specialized presheaf-Cech exactness; the general Sheaf declaration still contains sorry. The current polynomial-augmentation-boundary statement uses this item as an input and supplies none of the three auxiliary identity statements; the existing Not duplicates comparisons remain valid.

I checked B--E again: statement-only self-contained auxiliaries, unchanged hypotheses and target statement, no duplicate clauses, complete literal citations, no hidden non-elementary transport, and no long step. For the identity adjunction every displayed map is an identity; in degree zero the two counit equations give the asserted sections and the two reversal endpoints exchange; the right-degeneracy statement requires no coalgebra equation. Ordinary functor categories need no limit, product or small-index assumption here. No Lean or compiler was used. The next dry run validates these actual assembly and report edits before delivery.
