# Stage-1 repair: lem-pur-etale-coefficient-system-adjoint

1. Files written:

- dag/nodes/sec-smooth-purity/lem-pur-etale-coefficient-system-adjoint.json — unchanged statement; short assembly of extracted arguments.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-brown-construction.json — statement; status unsplit; Mathlib searches found no full match: Construction and Brown adjunction for the strict etale compact-support functor.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-coefficient-projection.json — statement; status unsplit; Mathlib searches found no full match: Constant coefficient projection maps for ordinary etale system compact supports.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-cofinal-mate.json — statement; status unsplit; Mathlib searches found no full match: Cofinal restriction and the compact-support adjunction mate.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-evaluation-bound.json — statement; status unsplit; Mathlib searches found no full match: Evaluation mates and a uniform lower bound for a system right adjoint.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-quotient-normalization.json — statement; status unsplit; Mathlib searches found no full match: Nonflat coefficient mates and normalization for ordinary etale adjoints.
- dag/nodes/sec-smooth-purity/lem-pur-etale-system-scalar-mate-coherence.json — statement; status unsplit; Mathlib searches found no full match: Coherent scalar mates on ordinary derived etale coefficient systems.
- citations.json — verbatim statement excerpts for every citation in each assembly step.
- report.md — this report, including the preserved returned proof.

2. Attachments: none. The upstream WeilConjectures search by the exact blueprint tag and by coefficient-system/exceptional-adjoint concepts did not find a closed declaration stating the item. The actual Sheaf.Paper.EtaleCoefficientSystemAdjoint theorem at line 1191 ends in sorry at 1208; scalar, cofinal, identity and composition companions also contain sorry. Arithmetic helper proofs cover only part of the item.

3. WANTED: none. Zheng arXiv:1006.3810 and the current main-20261015 blueprint sources were available locally.

4. What was wrong: the returned proof had nine substantial arguments (11551 characters) instead of independently claimable work units. I retained its statement and all arguments, extracted six new self-contained statements and reused the existing arithmetic theorem. The sandbox initially held only dispatcher marker files; the starting node was copied from the read-only live repository, including the later stage-3 edit to step 7, its citations, searches and all metadata. No previous report or searches.jsonl existed in the sandbox. The first required dry run consequently exited with "no node files"; it was fully exited before work proceeded. A second existing-node search found lem-pur-local-field-coefficient-stages, so creating an arithmetic duplicate was avoided.

5. What is not finished: proofs of the six new statement-only nodes are deliberately left to future independent workers, as the return explicitly requests. No mathematical clause of the parent remains unassigned. No Lean was edited, no compiler/Lake/build command was run, no repository git command was run and only the authorized sandbox was written.

## Repair allocation and work preservation

The six new nodes have proof=[], proof_deps=[], proof_origin=null and status=unsplit. Their statements introduce their objects, hypotheses, actual functors, natural transformations and defining transpose equations. They do not contain proof sketches. The argument plans below are in this report, not in the statement-only nodes. The old source, step citations and complete text are preserved verbatim after the review. The arithmetic work is assigned to an existing node instead of making a duplicate; the original integral-closure/basis argument is also retained verbatim below.

- Old steps 1 and 3 -> lem-pur-etale-system-brown-construction: coefficient finiteness/completeness, Noetherian schemes, actual F, evaluation, derived left extensions, coproducts, Brown, linear and shift structure, exactness.
- Old step 2 -> lem-pur-etale-system-coefficient-projection: derived scalar adjunction, restriction square, D-linear projection, nonflat coefficients, actual system maps and scalar-unit/tensor-associator coherence.
- Old steps 4 and 5 -> lem-pur-etale-system-evaluation-bound: six Hom bijections, inverse natural comparisons, units/counits, actual transition mates and three-index compatibility, amplitude and truncation orthogonality.
- Old step 6 -> lem-pur-etale-system-quotient-normalization: restriction-of-scalars comparison of finite right adjoints, identification of the specified b with the constant-tensor map, nonflat quotient invertibility and normalization.
- Old step 7 -> existing lem-pur-local-field-coefficient-stages: finite freeness, positive ramification, ideal equality and cofinal stages; the legacy integral-closure/basis implementation remains recorded below.
- Old step 8 -> lem-pur-etale-system-scalar-mate-coherence: actual system scalar mate, agreement of evaluation with finite b, invertibility, counit-normalized identity/composition and mixed quotient equations before evaluation.
- Old step 9 -> lem-pur-etale-system-cofinal-mate: actual F L_r comparison using t(m), transition coherence, Hom-induced counit-preserving cofinal comparison and composition of restrictions, ramified identification and resolution independence.

The parent assembly is 1935 characters, below the 3000-character limit. Its longest step is 425 characters, so it contains no non-elementary step above 2000 characters. The work was not compressed into one replacement theorem. Projection needs no adjoint; Brown asserts neither normalization nor scalar/cofinal transport; evaluation is conditional on an adjunction; normalization isolates the nonflat finite-ring argument; scalar coherence and cofinal transport have different index categories and defining Hom constructions.

## Not duplicates

lem-pur-etale-system-coefficient-projection vs lem-pur-ringed-coefficient-projection-cocycle: the existing node gives coherence for ringed-topos direct-image projection maps, with no invertibility. The new node adds the ordinary etale compact-support coefficient restriction identification and proves invertibility for arbitrary finite constant maps, with the open factor and system realization.
lem-pur-etale-system-coefficient-projection vs lem-amb-proper-coproducts-projection: the existing node gives the proper tensor projection at one coefficient ring. The new node compares different target coefficient categories, including scalar restriction and the open factor, and gives actual system maps.
lem-pur-etale-system-coefficient-projection vs lem-fix-compact-support-coefficient-change: the existing node is finite-Tor constructible and only quotient changes. The new statement is on all unbounded ordinary etale inputs and arbitrary maps of finite coefficient towers.
lem-pur-etale-system-brown-construction vs lem-grothendieck-derived-brown-right-adjoint: the existing generic Brown theorem assumes exactness and coproduct preservation. The new node verifies these for the specified strict-system geometric functor, along with coefficient hypotheses and linear/shift structures.
lem-pur-etale-system-brown-construction vs thm-amb-etale-exceptional-adjoint: the existing result is an ordinary single-ring adjoint, with no varying-ring system category or F L_n comparison.
lem-pur-etale-system-brown-construction vs det-prop-int-brown-construction: that blueprint node concerns integral/condensed localizing hulls. The new one concerns unbounded ordinary etale strict finite-coefficient systems and allows a nonseparated target.
lem-pur-etale-system-evaluation-bound vs lem-pur-coefficient-evaluation-derived-left-adjoint: the existing result supplies L_n adjoint to evaluation and the transition test. It does not identify e_nG with the finite exceptional adjoint or establish a lower bound for G.
lem-pur-etale-system-evaluation-bound vs lem-pur-system-derived-evaluation: the existing result detects bounds and isomorphisms by evaluation. It does not identify the system right adjoint, its counit/transition mates, or infer the uniform bound by adjunction.
lem-pur-etale-system-evaluation-bound vs lem-pur-etale-exceptional-constant-tensor: the existing result supplies the finite-level amplitude and constant-tensor isomorphism. It has no system right adjoint evaluation or truncation argument.
lem-pur-etale-system-quotient-normalization vs lem-pur-finite-coefficient-adjoint-comparisons: the existing comparison is for finite-Tor constructible ordinary/pro-etale realizations and separated schemes; the new lemma is unbounded ordinary etale, arbitrary finite coefficient ring maps, and uses a conditional system adjunction to infer normalization.
lem-pur-etale-system-quotient-normalization vs lem-coef-cartesian-section-adjoint-mates: the existing node concerns normalized constructible finite-Tor pro-etale systems. The new one isolates the ambient finite-ring restriction/tensor argument without constructibility or Tor hypotheses.
lem-pur-etale-system-scalar-mate-coherence vs lem-pur-ringed-coefficient-projection-cocycle: the existing cocycle is for direct-image projection, with no claim about the exceptional right-adjoint mate being an isomorphism. The new node transports specified compact-support q through F/G adjunction, identifies its finite evaluations and proves the exceptional coefficient comparison invertible.
lem-pur-etale-system-scalar-mate-coherence vs lem-pur-compact-support-strict-scalar-composition: the existing node compares compact-support functors and completed integral constructible outputs. The new node compares their ambient ordinary-etale system right adjoints, including nonflat finite coefficient maps.
lem-pur-etale-system-scalar-mate-coherence vs lem-pur-ordinary-adjunction-scalar-compatibility: the existing node concerns completed ordinary pullback/direct-image adjunctions, rather than F=Rp_*j_! and its strict-system exceptional right adjoint.
lem-pur-etale-system-cofinal-mate vs lem-pur-system-level-left-extension: the existing node gives L_r adjoint to restriction for semilinear systems. It does not give the geometric F L_r comparison or the induced right-adjoint cofinal isomorphism.
lem-pur-etale-system-cofinal-mate vs lem-pur-system-ordinary-selected-extension: the existing node is the underived selected-extension tensor/transpose calculation. The new result concerns the unbounded geometric compact-support functor and its right adjoint.
lem-pur-etale-system-cofinal-mate vs lem-weil-ramified-pullback-tower-identification: the existing node identifies finite pullback towers under ramification, not ordinary etale exceptional adjoints on whole derived system categories.

The arithmetic candidate was not created: lem-pur-local-field-coefficient-stages already states finite freeness and t^nS=v^{en}S. Its statement has no scheme hypothesis, so it can be used with Y nonseparated. lem-coef-finite-free-extension also has arithmetic clauses but its geometric statement is constructible and its dependency chain passes through exceptional constructions; it was not used for this foundational arithmetic input.

Before writing the new nodes I searched all dag/nodes by coefficient projection, normalized systems, scalar coherence, Brown, cofinal adjoints and exact proposed ids, and ran blueprint_refs.py ancestor and whole-blueprint searches for coefficient system, cofinal, constant tensor, coefficient change, right adjoint, Brown, subsequence, coefficient projection, projection square, normalized systems and normalization. I read the relevant candidate statements listed above. The blueprint matches give definitions, condensed/constructible/localizing-hull assertions or reconstruction after limit, not these six ambient strict-etale arguments. The blueprint.from.node is def-weil-exceptional-inverse-image and via=[lem-pur-etale-coefficient-system-adjoint] for every new node; from.place identifies its original argument and the ancestor's adic-stage paragraph. same_as=[] records no exact blueprint duplicate.

## Review by Q116

I read the current main-20261015 def-weil-exceptional-inverse-image source (sec-six-functors-basics/sk-prop-a1-kummer), the recorded sk-def-sf-operations unit, and the unchanged parent statement. Its purpose is to produce the coherent finite-stage adjoint before any inverse limit. The six extracted statements stay on that route; no completed integral, rational, constructible or pro-etale exceptional adjoint was substituted. The parent retains every quantifier, including nonseparated Y, all unbounded system inputs, actual map action, bounded-below normalization and ramified finite-free transport.

For the item and each new node I opened the local Zheng PDF through pdftotext. I read Construction 4.1 (printed p. 21), Lemma 4.13 (p. 24), Constructions 5.14–5.15 and Lemma 5.16 with the following Brown paragraph (pp. 34–35), Lemma 5.22 and Proposition 5.24 (pp. 36–37), and Proposition 2.29(2) (p. 16). Projection uses the constant-complex tensor assertion, not a tensor assertion for arbitrary sheaves. Brown follows the small-direct-sum paragraph; evaluation follows the adjunction from left extension; normalization uses finite nonflat coefficient mates; scalar and subsequence coherences are agent-written extractions of the old transpose argument, not a claim that Zheng prints every such diagram. No prohibited source is cited.

For the projection node I checked the finite ring, invertible ell and Noetherian hypotheses of the old inputs. Finite-type k-schemes are Noetherian even if not separated over k. The proper part is proper of finite type and j is open. The actual restriction square follows by ringed-topos derived pushforward composition and open extension, and the finite constant projection gives its tensor comparison in the D-linear derived category. The new statement retains the exact scalar-unit normalization and the tensor associator equation, so it does not replace a proof of map coherence by a comparison of objects. The generic ringed-coefficient projection cocycle was read and distinguished as above.

For the Brown node I checked that allowing any nonzero nonunit t, rather than only a uniformizer, is necessary for O' with the image of varpi. Writing t=u*pi^e with e>0 identifies its powers with a cofinal uniformizer sequence; the same finite coefficient and completeness arguments apply. The closed valuation subring of a complete finite local field is complete. Grothendieckness and componentwise coproducts come from the system left-extension statement, not from finite coefficient flatness. The coproduct argument uses the finite-ring proper coproduct theorem, then evaluation detection. The right-adjoint exactness statement explicitly specifies the adjunction-induced shift structure and compatibility of its unit and counit; this hypothesis cannot be omitted.

For the evaluation-bound node I checked every Hom domain and codomain in the six adjunctions. L_n is the derived left adjoint to evaluation on strict semilinear systems, not extension in a fixed-ring functor category. F L_n is the specified coefficient projection comparison, not an arbitrary isomorphism. The transition is the mate b followed by g_n of the input transition; the inverse q occurs because it is the F_n-adjunct of a map with domain F_n T_X g_m. For the lower bound, if H is at most a-N-1, then F H is at most a-1, hence has no map to M at least a; use the canonical truncation of GM to force vanishing. This keeps the sign a-N and the level-independent N.

For the quotient-normalization node I read the statement of lem-pur-etale-exceptional-constant-tensor: it allows an arbitrary constant complex V with no perfectness or boundedness. Thus V=D is allowed even for a nonflat quotient C->D. The restriction comparison U g_D = g_C U is obtained using T adjoint to U and q, and the specified transpose b restricts to this precise constant-tensor map. Conservativity of scalar restriction proves invertibility. The final normalization conclusion assumes the evaluation/transition mate identification, so no separate output transition is guessed.

For scalar-mate coherence I checked that both adjunctions are fixed and that q is an actual transformation on derived systems. Equality of the two composite maps is to be proved by equality of their counit transposes, using the composition equation for q and naturality; evaluation only detects invertibility, never equality of arbitrary morphisms. For cofinal restriction I checked t(m) exists by unboundedness, that it can jump or remain constant, and that the selected-level transition is the one in lem-pur-system-level-left-extension. The level of h_r is inverse q (the old step did not specify its orientation). The five Hom bijections then fix rho_r, including its map action and counit. The ramified example now explicitly specifies O'=O_{E'} for a finite local-field extension, so it satisfies the finite-ring hypotheses rather than quantifying over arbitrary valuation rings.

I opened the existing local-field coefficient-stage node and its main-20261015 source sk-lem-sp-field-extension-towers.proof.md Part (1). Its statement gives exactly the finite-free quotient maps, unit-times-uniformizer factorization, ideal identities and cofinal positive indices used in assembly steps 4 and 6. It is used only as an arithmetic tool; its source's stronger assertions about completed scalar extension are not used. The earlier stage-3 arithmetic proof is preserved below rather than erased.

Assembly citation audit (the statements were opened, and citations.json contains literal excerpts):

1. lem-pur-etale-system-brown-construction supplies F, exact linear G, and the specified F L_n isomorphism; lem-pur-etale-system-coefficient-projection supplies the actual coefficient projection maps from which that isomorphism is normalized. The step merely applies those results to t=varpi.
2. lem-pur-etale-system-evaluation-bound supplies theta_n, evaluated units/counits and transition mates, and converts a uniform upper bound for F_n to the lower bound for G. lem-pur-etale-exceptional-constant-tensor states precisely that uniform upper bound for finite ell-primary coefficients; all rings here have that property.
3. lem-pur-etale-system-quotient-normalization states the finite quotient mate is invertible and its consequence for a system with the transition identification from step 2. Invertibility of the composite g_n(t_M)b is immediate; boundedness is the previously proved lower bound.
4. lem-pur-local-field-coefficient-stages states the finite-free maps and the equality of ideals; the Brown construction covers O' and t=varpi without needing t to be its chosen uniformizer. Exactness of a finite-free tensor is the module-basis calculation.
5. lem-pur-etale-system-scalar-mate-coherence supplies the actual b_a isomorphism and the identity/composition/mixed quotient/associator equations. It is applied to the two adjunctions already constructed; no new Brown argument or faithfulness assertion is hidden.
6. lem-pur-etale-system-cofinal-mate gives h_r and rho_r with counit and composed-subsequence coherence. Step 4 identifies the ring sequence; this last application does not take an inverse limit. Its statement explicitly includes map action and resolution independence.

Small cases checked: f=id and j=id give the identity adjunction and tensor-unit comparisons; empty source gives the zero functor/right adjoint and all comparison maps between zero objects. n=1 and m=n give the residue-ring or identity coefficient map; C=Z/ell^2 -> D=Z/ell is deliberately nonflat and is handled by derived tensor. The uniform cohomological bound for f=id is N=0, so the sign gives preservation of a lower bound. Identity coefficient extension gives b=1; for a ramified extension e>1 the retained rings are at en, not n, and for e=1 the cofinal restriction is identity. r with gaps tests the jump t(m+1)>t(m), while r(n)=n tests the equal-index associator. Zero normalized systems stay normalized. Non-normalized inputs are allowed for existence/evaluation/scalar/cofinal comparisons, but are not declared normalized.

The Mathlib queries were run only through the required msearch.py command, two semantic phrasings per node plus Loogle and grep, with full outputs retained in search-results.json and supplement-search-results.json and exact queries in each node. LeanSearch rate limits for two queries are recorded as unavailable. Invalid short-name Loogle queries are recorded as rejected rather than as evidence of absence, and corrected queries were run. I read Mathlib CategoryTheory/Adjunction/Mates.lean lines 53–152, Triangulated/Adjunction.lean lines 40–74, Adjunction/Evaluation.lean lines 45–69, Functor/KanExtension/Basic.lean lines 166–198 and ModuleCat/ChangeOfRings.lean lines 976–1043 after search hits. mateEquiv constructs general mates but explicitly does not imply they are invertible. isTriangulated_rightAdjoint assumes a compatible shift adjunction and does not establish Brown existence or the system model. evaluationIsRightAdjoint is a fixed-target functor-category result. The scalar associators are ordinary ModuleCat maps. These are useful ingredients, not a full match or a one-line specialization of a new node; therefore there are zero new Mathlib leaves.

Corrections in this repair: extracted all the substantial arguments instead of shortening them in place; left the new nodes statement-only; reused the arithmetic lemma found in the live DAG; specified a nonuniformizer generator t for the ramified target construction; made the cofinal example's coefficient-field hypothesis explicit; fixed the orientation of its inverse projection; retained inherited item metadata and searches; recorded exact citation excerpts. I checked B1–B10, C1–C8, D1–D5 and E1–E7 against these files: no new hollow definition, no per-degree substitute for a derived isomorphism, no clause asserted just by renaming the entire parent, no quotient-flatness claim, no equality-of-morphisms inference from evaluation, and no off-route exceptional construction. The return specifically authorizes moving these genuine subarguments into independent statement-only nodes.

Preliminary server checks: srvcheck check_dag returned OK, and srvcheck review_split returned PASS. The full required deliver.py --no-push exited successfully: OK (not pushed), commit 313c2816d3c, preflight passed. After recording this receipt in the report, the final files are dry-run again before the authorized push.

## Preserved returned proof and searches

The following is the entire returned proof verbatim, not a summary. The responsible new/existing node is listed for every argument above. All original node citations and source places are retained for the future workers.

### Returned step 1

Prepare the coefficient and site hypotheses. The valuation-ring theorem gives a DVR $O$ with finite residue field and factorization $x=u\varpi^v$. Its finite-quotient theorem gives finite rings $A_n$ and the surjective coefficient transitions. The absolute value extending that of $\mathbf Q_\ell$ has $|\ell|<1$, so a power of $\ell$ lies in $(\varpi^n)$; thus each $A_n$ is annihilated by an integer invertible on $k$. Completeness of $E$ makes its closed valuation subring complete: a $\varpi$-adic Cauchy sequence is Cauchy in $E$ and its limit still has absolute value at most one. Hence $O=\varprojlim O/\varpi^n$. Finite-type schemes over $k$, including $\overline X$, are Noetherian by the finite-type-over-Noetherian theorem (a field is Noetherian). The system comparison theorem therefore supplies the unbounded derived direct image and its evaluated comparisons. Extension by zero for $j$ is exact and left adjoint to restriction; its termwise version acts on strict systems and on the enhanced section models. Consequently $F=Rp_{A,*}j_{!,A}$ is a well-defined exact functor, and $e_nF\cong F_{f,A_n}e_n$, with actual units, counits, and coefficient transition maps. The left-extension lemma supplies Grothendieckness, levelwise coproducts and detection by evaluation.

Uses: lem-weil-l-adic-extension-integers-dvr, lem-weil-valued-dvr-finite-quotients, lem-weil-l-adic-extension-absolute-value, lem-weil-l-adic-extension-complete, lem-weil-pbc-finite-type-over-noetherian, lem-pur-coefficient-system-derived-comparison, lem-amb-etale-adjoint-locality, lem-coef-semilinear-derived-sections, lem-pur-system-level-left-extension

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Constructions 4.1 and 5.14–5.15; Lemma 4.10."}

### Returned step 2

First construct the coefficient projection square at an ordinary finite level. For any homomorphism of finite $\ell$-primary rings $C\to D$, let $T=-\otimes_C^LD$ and let $U$ be exact restriction of scalars. The module tensor/restriction adjunction derives to $T\dashv U$: restriction is exact and derived tensor is computed by K-flat resolutions. Composition for unbounded derived direct images, applied to the square of identity-topos ring-change morphisms and the geometric proper map, gives $URp_{*,D}\cong Rp_{*,C}U$. It also gives $UF_{f,D}\cong F_{f,C}U$, since extension by zero commutes with restriction. Form the $D$-linear map $q:T_YF_{f,C}\to F_{f,D}T_X$ by tensor/restriction adjunction from $F_{f,C}$ applied to the scalar unit. After forgetting $D$, this is exactly the constant-coefficient projection map for $V=D$, hence is invertible by the finite-level tensor lemma (equivalently use the proper projection formula and the exact open extension). Restriction detects isomorphisms, so $q$ is invertible as a $D$-linear map. This argument applies to non-flat quotient maps as well as finite-free extensions. On the enhanced section models the same counit-transpose construction supplies an actual map, not a choice of componentwise lifts. Evaluation of that map is the map just constructed. Its identity and composite-extension squares agree: on K-flat representatives the scalar units send $x$ to $x\otimes1$, and the associator sends $(x\otimes d)\otimes d'$ to $x\otimes dd'$; these give the same transpose for either composite.

Uses: lem-weil-pbc-ringed-topoi-module-adjunction, lem-pc-pre-derived-adjoint-functors-general, lem-pur-derived-change-of-rings, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-pur-etale-exceptional-constant-tensor, lem-amb-proper-coproducts-projection, lem-coef-semilinear-derived-sections

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Theorem 2.18(2); Construction 2.26; Construction 5.15 and Lemma 5.16."}

### Returned step 3

The preceding squares, with $C=A_n,D=A_m$ for $m\le n$, give $FL_n\cong L_nF_{f,A_n}$: at $m\le n$ it is precisely $q$, and at $m>n$ both evaluations are zero. The section-model construction and the transition formulas for $L_n$ identify the maps and their coherences, so this is an isomorphism of functors on derived systems. Also $F$ preserves arbitrary set-indexed coproducts. Indeed $j_!$ preserves them as a left adjoint, proper $Rp_*$ preserves them for each finite ring by the proper-coproduct theorem, and evaluation computes coproducts and detects isomorphisms. Apply the Grothendieck-derived Brown theorem to this exact coproduct-preserving functor, obtaining an actual right adjoint $G$. Its additive and $O$-linear structure is specified by the adjunction: the map induced by $a\in O$ is the unique transpose of multiplication by $a$ on $F$; the identities for sums and products follow from the Hom bijection. Similarly $G(M[t])\cong(GM)[t]$ is the unique adjunction-induced shift isomorphism. The shift cocycle and compatibility of the unit and counit follow by transposition from those for $F$. The triangulated-right-adjoint lemma then proves $G$ exact.

Uses: lem-pur-system-level-left-extension, lem-coef-semilinear-derived-sections, lem-amb-etale-adjoint-locality, lem-amb-proper-coproducts, lem-grothendieck-derived-brown-right-adjoint, lem-sf-triangulated-right-adjoint

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Lemma 5.16 and the Brown right adjoint following it."}

### Returned step 4

For $P\in D(X_{\mathrm{et}},A_n)$ and $M\in D(\mathsf S_A(Y_{\mathrm{et}}))$, use the following natural Hom bijections:
$$\operatorname{Hom}(P,e_nGM)=\operatorname{Hom}(L_nP,GM)=\operatorname{Hom}(FL_nP,M)=\operatorname{Hom}(L_nF_{f,A_n}P,M)=\operatorname{Hom}(F_{f,A_n}P,e_nM)=\operatorname{Hom}(P,f_n^\times e_nM).$$
Taking the images of identity morphisms in the two directions produces inverse natural maps $e_nG\cong f_n^\times e_n$; their inverse equations follow immediately by composing the displayed bijections. This is the Yoneda argument written out, not an appeal to full faithfulness of a representable embedding. The adjunction formulas define the comparison to preserve the evaluated counits and units. For $m\ge n$, the structure map is the mate of the transition together with the coefficient square $q$ of step 2: its adjoint transition is the scalar comparison $T_{A_n/A_m}f_m^\times(M_m)\to f_n^\times(T_{A_n/A_m}M_m)$ followed by $f_n^\times$ of the adjoint input transition. This equation follows by transposing both maps, which yields the input transition composed with the same evaluated counit and $q^{-1}$. It therefore identifies transitions as maps, including composition for three indices.

Uses: lem-pur-system-level-left-extension, thm-amb-etale-exceptional-adjoint, lem-coef-semilinear-derived-sections

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Lemma 5.22, including its proof by the two adjunctions in Lemma 5.16."}

### Returned step 5

Choose the uniform integer $N_f$ from the finite-level amplitude lemma. If $H\in D^{\le b}(\mathsf S_A(X_{\mathrm{et}}))$, its evaluations satisfy the same bound; therefore $FH\in D^{\le b+N_f}$ by that lemma and evaluation detection. If $M\in D^{\ge a}$ and $H\in D^{\le a-N_f-1}$, then
$$\operatorname{Hom}(H,GM)=\operatorname{Hom}(FH,M)=0.$$
The orthogonality characterization of the standard cohomological truncations gives $GM\in D^{\ge a-N_f}$. To spell out the characterization used here, take $H=\tau_{\le a-N_f-1}GM$; its canonical map to $GM$ must vanish, whereas it induces the identity on all cohomology in those degrees, so those groups vanish. Thus $c_f=N_f$ works independently of the level.

Uses: lem-pur-etale-exceptional-constant-tensor, lem-pur-system-level-left-extension, def-sbc-standard-tstructure-derived-category

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 5.15, amplitude [0,2d], and its right adjoint after Lemma 5.16."}

### Returned step 6

Show that the finite-level right adjoints commute with every constant finite change of coefficients, including non-flat quotients. With $T,U,q$ as in step 2, adjunction gives
$$\operatorname{Hom}(K,UG_{f,D}N)=\operatorname{Hom}(T_XK,G_{f,D}N)=\operatorname{Hom}(F_{f,D}T_XK,N)=\operatorname{Hom}(T_YF_{f,C}K,N)=\operatorname{Hom}(K,G_{f,C}U N).$$
Identity morphisms again give $UG_{f,D}\cong G_{f,C}U$. Define $b:T_XG_{f,C}M\to G_{f,D}T_YM$ as the transpose of
$$F_{f,D}T_XG_{f,C}M\xrightarrow{q^{-1}}T_YF_{f,C}G_{f,C}M\xrightarrow{T_Y\epsilon_C}T_YM.$$
Under the preceding restriction identification, $Ub$ is exactly $D\otimes_C^LG_{f,C}M\to G_{f,C}(D\otimes_C^LM)$, the constant-tensor map of the finite-level lemma with $V=D$. That lemma makes it invertible; exact restriction is conservative, hence $b$ is invertible. For a normalized system $M$, step 4 identifies its output's adjoint transition as
$$A_n\otimes^L_{A_m}G_{f,A_m}M_m\xrightarrow{b}G_{f,A_n}(A_n\otimes^L_{A_m}M_m)\xrightarrow{G_{f,A_n}(\alpha_{m,n})}G_{f,A_n}M_n.$$
Both arrows are isomorphisms. Thus $GM$ is normalized, and step 5 supplies boundedness below when $M$ is bounded below. This uses only the explicitly stated derived-transition definition of normalization; no unbounded equivalence with completion is presumed.

Uses: lem-pur-etale-exceptional-constant-tensor, thm-amb-etale-exceptional-adjoint, lem-pur-derived-change-of-rings, lem-weil-pbc-ringed-topoi-module-adjunction, lem-pc-pre-derived-adjoint-functors-general, lem-pur-coefficient-system-derived-comparison

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Proposition 2.29(2); Lemma 5.22 and its observation on weak normalization; Proposition 5.24. The normalization convention is the transition condition of the item."}

### Returned step 7

For the arithmetic coefficient input, identify O prime with the integral closure of O in E prime using lem-sfb-padic-integers-integral-closure. The DVR theorem supplies the fraction field E and the PID structure on O. E prime is finite over E by restriction of scalars and separable because E has characteristic zero. The finite-integral-closure theorem therefore gives a finite O-module O prime, and IsIntegralClosure.module_free gives freeness over the PID O. Take its finite basis, base change it to O/(varpi^(n+1)), and use Algebra.TensorProduct.quotIdealMapEquivQuotTensor. Ideal.map_pow and Ideal.map_span identify the extended ideal with the ideal generated by the image uniformizer power. Transport the resulting basis to the actual ModuleCat.restrictScalars quotient module, with its scalar action explicitly Module.compHom of strictCoefficientRingMap. This proves strictEtaleScalarLevelModule_finiteFree without a completeness or residue-quotient argument. Separately, strictEtaleIntegerMap_mem follows by identifying the spectral norms under an injective algebra map using minpoly.algHom_eq, then applying the unit-ball descriptions from the DVR theorem. The remaining ramification and cofinal-construction assertions are still the unproved plan of step 9.

Uses: lem-weil-l-adic-extension-integers-dvr, lem-sfb-padic-integers-integral-closure, lem-weil-pbc-noetherian-normal-separable-integral-closure-finite, lem-sc-dvr-fg-torsionfree-free

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 4.1, allowing any principal non-zero-divisor with complete adic topology; coefficient change used in Proposition 2.29(2)."}

### Returned step 8

On derived systems let $U$ be exact restriction of scalars for $B_\bullet/A_\bullet$. Tensor/restriction adjunction derives to $T\dashv U$, with evaluations and units computed termwise; here finite freeness also makes $T$ exact. The enhanced section models supply the actual projection square $q:T_YF_A\xrightarrow{\sim}F_BT_X$ constructed in step 2; its evaluations are those finite-level isomorphisms, so it is invertible. Define the actual system transformation $b:T_XG_A\to G_BT_Y$ by the identical transpose formula $T\epsilon_A\circ q^{-1}$ used in step 6. Step 4 and the compatibility of transposition with the specified section models identify its evaluations with the finite-level $b$ of step 6. They are all invertible, so $b$ is an isomorphism of derived-system functors. For an identity coefficient extension its transpose is the counit and $b$ is the identity. For two extensions, transpose the composite of their $b$ maps and use the defining equations $\epsilon_D\circ F_Db=T\epsilon_C\circ q^{-1}$ twice. Naturality of the counits reduces the result to $T'T\epsilon_C$ preceded by the composite inverse projection square. The associativity equation for $q$ in step 2 identifies this with the transpose defining $b$ for the composite extension. The Hom bijection is injective, so the two actual system maps agree. This argument also applies to diagrams containing quotient maps, using derived tensor for their non-flat edges. It proves the requested coherences with identities, composition, quotients and the canonical tensor associators; it does not use faithfulness of evaluation on morphisms.

Uses: lem-coef-semilinear-derived-sections, lem-pur-derived-change-of-rings, lem-weil-pbc-ringed-topoi-module-adjunction, lem-pc-pre-derived-adjoint-functors-general, lem-pur-system-level-left-extension

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Constructions 2.26 and 5.15; Proposition 2.29(2)."}

### Returned step 9

Finally consider any strictly increasing unbounded subsequence $r$. Its restriction $U_r$ has left adjoint $L_r$ by the left-extension lemma. The explicit formula for $L_r$ and the coefficient projection squares of step 2 give $F_{\mathrm{full}}L_r\cong L_rF_r$ as actual functors: at level $m$ use $q$ for $B_{r(t(m))}\to B_m$; the transition formulas and the scalar-unit calculation in step 2 give the required compatible maps. For any $N$ in the subsequence source category and $M$ in the full target category, the bijections
$$\operatorname{Hom}(N,U_rG_{\mathrm{full}}M)=\operatorname{Hom}(L_rN,G_{\mathrm{full}}M)=\operatorname{Hom}(F_{\mathrm{full}}L_rN,M)=\operatorname{Hom}(L_rF_rN,M)=\operatorname{Hom}(N,G_rU_rM)$$
give the canonical counit-preserving isomorphism $U_rG_{\mathrm{full}}\cong G_rU_r$. It is natural on maps and coherent under composed subsequences by composition of these Hom bijections, or equivalently by equality of their counit transposes. Apply it to the $O'$ tower indexed by $\varpi'$ and $r(n)=en$. The coefficient ideals identified in step 7 identify its restricted ring system with $B_n=O'/\varpi^nO'$, so this is exactly the required comparison with the construction using $\varpi$. Every comparison above was defined by derived operations and an adjunction transpose, which are independent of resolutions by the change-of-rings, system comparison and enhanced-model lemmas; no inverse limit or integral output was introduced.

Uses: lem-pur-system-level-left-extension, lem-coef-semilinear-derived-sections, lem-pur-derived-change-of-rings, lem-pur-coefficient-system-derived-comparison

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 4.1 and the adjunction argument of Lemma 5.22; restriction to the cofinal powers (varpi prime)^(en)."}

### Inherited Mathlib searches of the item

```json
[
 {
  "tool": "leanfinder",
  "query": "Right adjoint of compact support pushforward on the derived category of coefficient towers of etale sheaves",
  "results": "AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPushforward; SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPushforwardContinuous; SheafOfModules.pushforwardPushforwardAdj; SheafOfModules.instIsRightAdjointPushforward; AlgebraicGeometry.Scheme.Modules.restrictAdjunction; SheafOfModules.pullbackPushforwardAdjunction; AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor; AlgebraicGeometry.Scheme.Modules.pseudofunctor_map_adj",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "loogle",
  "query": "\"CategoryTheory.Adjunction\", \"DerivedCategory\"",
  "results": "",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "grep",
  "query": "upperShriek|UpperShriek|exceptional.*tower|tower.*adjoint",
  "results": "",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "leansearch",
  "query": "Exceptional pullback on ringed topos of projective coefficient systems preserves normalization",
  "results": "SheafOfModules.pullback; AlgebraicGeometry.Scheme.Hom.instIsAffineHomToNormalization; AlgebraicGeometry.Scheme.Hom.toNormalization_app_preimage; AlgebraicGeometry.Scheme.Hom.instIsIsoToNormalizationOfIsIntegralHom; AlgebraicGeometry.Scheme.Hom.toNormalization; AlgebraicGeometry.Scheme.Hom.normalizationDesc; AlgebraicGeometry.Scheme.Hom.preservesLocalization_normalizationDiagramMap; SheafOfModules.pullbackPushforwardAdjunction",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "leanfinder",
  "query": "Coherent extraordinary pullback of projective systems of torsion sheaves compatible with reduction of coefficients",
  "results": "CategoryTheory.Presheaf.isSheaf_coherent_of_projective_comp; LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition'; LightCondMod.ofSheafLightProfinite; LightCondAb.ofSheafLightProfinite; CondensedMod.ofSheafProfinite; LightCondensed.free_lightProfinite_internallyProjective_iff_tensor_condition; LightCondensed.free_internallyProjective_iff_tensor_condition'; LightCondensed.free_internallyProjective_iff_tensor_condition",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "leanfinder",
  "query": "Adjoint of derived direct image with compact support for adic sheaf systems",
  "results": "localCohomology; AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointRestrictFunctor; AlgebraicGeometry.Scheme.Modules.restrictAdjunction; localCohomology.ofDiagram; localCohomology.diagram; AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPresheafOfModulesToPresheafOfModules; SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPushforwardContinuous; AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPushforward",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "grep",
  "query": "projectiveSystem|inverseSystem|coefficientSystem|evaluation.*derived",
  "results": "Mathlib/FieldTheory/CardinalEmb.lean; Mathlib/FieldTheory/CardinalEmb.lean; Mathlib/FieldTheory/CardinalEmb.lean; Mathlib/FieldTheory/CardinalEmb.lean; Mathlib/Algebra/Colimit/DirectLimit.lean; Mathlib/ModelTheory/DirectLimit.lean; Mathlib/Order/DirectedInverseSystem.lean; Mathlib/Order/DirectedInverseSystem.lean",
  "date": "2026-10-16",
  "verdict": "no match: read the hits; generic derived functors, ordinary sheaf adjunctions, root systems or scheme normalization do not state this varying-coefficient-system theorem"
 },
 {
  "tool": "leanfinder",
  "query": "Extraordinary inverse image of sheaves on ringed topoi of inverse diagrams and scalar extension",
  "results": "SheafOfModules.pushforwardNatIso_inv; SheafOfModules.pullback; AlgebraicGeometry.Scheme.Modules.restrictFunctor; SheafOfModules.pushforwardComp_inv_app_val_app; SheafOfModules.conjugateEquiv_pullbackComp_inv; SheafOfModules.pushforwardSections; SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom; SheafOfModules.pushforwardCongr_symm",
  "date": "2026-10-16",
  "verdict": "no match: inspected returned signatures; ordinary sheaf pullback, generic derived linearity/evaluation, local cohomology and normalized Moore complexes do not state the derived varying-ring-system comparison or exceptional adjoint"
 },
 {
  "tool": "grep",
  "query": "evaluation.*(derived|Derived)|RightDerived.*eval|eval.*RightDerived|normalized.*complex",
  "results": "Mathlib/NumberTheory/ModularForms/Derivative.lean; Mathlib/NumberTheory/ModularForms/Derivative.lean; Mathlib/NumberTheory/ModularForms/Derivative.lean; Mathlib/NumberTheory/ModularForms/Derivative.lean; Mathlib/NumberTheory/ModularForms/Derivative.lean; Mathlib/AlgebraicTopology/MooreComplex.lean; Mathlib/AlgebraicTopology/MooreComplex.lean; Mathlib/AlgebraicTopology/MooreComplex.lean",
  "date": "2026-10-16",
  "verdict": "no match: inspected returned signatures; ordinary sheaf pullback, generic derived linearity/evaluation, local cohomology and normalized Moore complexes do not state the derived varying-ring-system comparison or exceptional adjoint"
 },
 {
  "tool": "loogle",
  "query": "\"DerivedCategory\", \"evaluation\"",
  "results": "",
  "date": "2026-10-16",
  "verdict": "no match: inspected returned signatures; ordinary sheaf pullback, generic derived linearity/evaluation, local cohomology and normalized Moore complexes do not state the derived varying-ring-system comparison or exceptional adjoint"
 },
 {
  "tool": "grep",
  "query": "upperShriek|exceptional.*system|coefficientSystem",
  "results": "[]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 },
 {
  "tool": "loogle",
  "query": "\"CategoryTheory.Adjunction\", \"DerivedCategory\"",
  "results": "[]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 },
 {
  "tool": "leanfinder",
  "query": "Right adjoint to derived compact support on inverse systems of etale sheaves compatible with coefficient reduction",
  "results": "[\"Condensed.profiniteSolidification\", \"Condensed.profiniteSolidCounit\", \"LightCondSet.topCatAdjunctionUnit\", \"LightCondMod.LocallyConstant.adjunction\", \"LightCondSet.LocallyConstant.adjunction\", \"LightCondensed.lanLightCondSet\", \"CompHausLike.LocallyConstant.adjunction\", \"Condensed.lanSheafProfinite\"]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 },
 {
  "tool": "leansearch",
  "query": "Extraordinary inverse image on derived projective systems of torsion coefficient sheaves",
  "results": "[\"CategoryTheory.Equivalence.sheafCongr.inverse_map_val_app\", \"InverseSystem.invLimEquiv_symm_apply_coe\", \"CategoryTheory.Equivalence.sheafCongrPrecoherent_inverse_map_val_app\", \"CategoryTheory.Equivalence.sheafCongr.inverse_obj_val_map\", \"CategoryTheory.ProjectiveResolution.isoLeftDerivedObj_inv_naturality\", \"CategoryTheory.Equivalence.sheafCongrPrecoherent_inverse_obj_val_obj\", \"CategoryTheory.Equivalence.sheafCongr.inverse_obj_val_obj\", \"SheafOfModules.pushforwardNatIso_inv\"]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 },
 {
  "tool": "grep",
  "query": "projectiveSystem|inverseSystem|coefficient.*system",
  "results": "[\"Mathlib/Algebra/Colimit/DirectLimit.lean\", \"Mathlib/FieldTheory/CardinalEmb.lean\", \"Mathlib/FieldTheory/CardinalEmb.lean\", \"Mathlib/FieldTheory/CardinalEmb.lean\", \"Mathlib/FieldTheory/CardinalEmb.lean\", \"Mathlib/ModelTheory/DirectLimit.lean\", \"Mathlib/Order/DirectedInverseSystem.lean\", \"Mathlib/Order/DirectedInverseSystem.lean\"]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 },
 {
  "tool": "leanfinder",
  "query": "Brown representability for exceptional inverse image on a ringed topos of inverse coefficient towers",
  "results": "[\"AlgebraicGeometry.Scheme.Modules.pseudofunctor\", \"PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy\", \"AlgebraicGeometry.Scheme.Modules.pseudofunctor_map_adj\", \"AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPushforward\", \"PresheafOfModules.instIsRightAdjointPushforward\", \"AlgebraicGeometry.Scheme.Modules.instIsLeftAdjointPullback\", \"PresheafOfModules.pullback\", \"SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPushforwardContinuous\"]",
  "date": "2026-10-16",
  "verdict": "no match: read hits; ordinary sheaf adjunctions, generic functor-category evaluation, root/inverse systems and local cohomology do not state the strict varying-coefficient-system exceptional adjoint theorem."
 }
]
```
