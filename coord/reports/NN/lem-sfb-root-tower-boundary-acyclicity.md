# Stage-1 repair: lem-sfb-root-tower-boundary-acyclicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-boundary-acyclicity.json: unchanged statement and statement dependencies; split proof assembled in 2529 characters (five steps).
- dag/nodes/sec-six-functors-basics/lem-sfb-parameter-root-integral-nil-fibre.json: statement-only, status unsplit, no Mathlib match. This is the algebraic geometry work package, for arbitrary rings without normal crossings assumptions.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-fibre-section-specialization.json: statement-only, status unsplit, no Mathlib match. This is the normalized derived specialization work package, for arbitrary integral fibre-section diagrams without a puncture or constant boundary model.
- citations.json: actual statements quoted verbatim for every citation of every assembly step.
- searches.jsonl and the search-output text files: real searches and their returned hits, retained for reuse. Helper scripts and search output remain sandbox-only.

## Attachments

None. Searched lean/WeilConjectures for the item tag, rootTower, root-tower, Kummer and integral/nil-fibre notions. The item itself is in lean/Sheaf/Paper/RootTowerBoundaryAcyclicity.lean:76 and its proof is sorry. Its full docstring reproduces the returned six-step argument. No project declaration found states the entire item with a finished proof; Mathlib integral-morphism and individual-root lemmas do not prove these new intermediate packages in one line.

## WANTED

WANTED: exact all-continuous reference for the normalized integral-fibre-section specialization, including incomplete Omega, profinite-family diagrams and directional coefficient restriction, for lem-sfb-integral-fibre-section-specialization. This is an agent-extracted intermediate argument from the returned proof, conditional on the existing lem-sfb-integral-lisse-closed-base-change and topological-invariance inputs. The blueprint paragraph is not represented as stating this lemma.

The earlier report's three WANTED lines remain below. The purely algebraic lem-sfb-parameter-root-integral-nil-fibre has an explicit elementary-algebra route using the existing monic quotient and finite-integrality nodes, detailed below; it has no additional continuous-coefficient assumption.

## What was wrong and the repair

The maintainer requested a genuine work split of the 6838-character argument into at least two comparable, independently actionable statement-only nodes, keeping the parent statement and reducing its assembly to at most 3000 characters. This repair creates two such nodes. It does not merely compress the old text: the original six steps are preserved verbatim in the argument inventory below and assigned to exact inputs. The original NI delivery report is retained at the end with its citations, searches, and unresolved reference requests. No Lean, target, definition, chapter or unit record is changed.

The sandbox initially held only .brief2 through .brief5, with no node, report or search log. Thus there was no retained split/report on which to perform an initial dry run. I copied the current read-only repository item, which has the returned six steps and Lean module named in the return. The original node's statement, stmt_deps, source, pointers, metadata and Lean record are preserved. The delivery tool overlays permitted split fields on current main and preserves maintainer metadata.

The current blueprint direct-images proof paragraph (3) invokes open-image coefficient preservation, not these expanded root arguments. Accordingly the proof remains agent-origin, with precise places in that paragraph. The chapter record and current unit _section.md were read. The dag/units record still describes the older sec-six-functors unit; no attempt was made to edit that mismatch. blueprint_refs.py ancestor reports inherited null; the exact existing via chain is retained and extended by this item's id for both children. Whole-blueprint searches for root tower, root algebra, nilpotent, integral, specialization, closed specialization, profinite.*integral and closed.*fibre.*section found no imported equivalent.

The existing lem-sfb-root-tower-puncture-invariance now states and splits the original first-step induction, including the actual unit and Q-family naturality. Creating a third copy would violate C5 and D1. It is reused directly, not silently removed. The original support-vanishing/triangle/finite-induction argument remains in that existing split and is preserved verbatim in the inventory here. Neither new node repeats the punctured-tower result: the first has no sheaf, and the second has no roots, open complement, internal function object or constant boundary identification.

## Work allocation and retained arguments

**Geometry package, lem-sfb-parameter-root-integral-nil-fibre (original step 2).** A future worker can start independently of all coefficient work. Successively apply lem-weil-pbc-monic-quotient-free to x^n-t to obtain the finite monomial bases, then lem-weil-pbc-finite-algebra-is-integral at each stage. An element of the root colimit, or of its parameter ring, lies in one finite root stage and one finite partition stage; the latter ring is a finite product, finite as a base module. This proves integrality of q_P. Quotienting the closed fibre by all roots leaves exactly the parameter ring of R/I. Every root has nth power zero on that fibre; any element of the generated ideal involves finitely many such nilpotents, and their finitely generated ideal is nilpotent. Consequently the quotient has nil kernel and is surjective on spectra. This is not an equality of schemes and does not require a uniform nilpotence exponent. The quotient formulas give the two factorization equalities and all base and parameter compatibility, since they hold on the coefficient ring and every root generator. Finite products and filtered root algebras commute with the displayed base changes. These are the entire original algebra argument, not a proof smuggled into a new node's statement.

**Specialization package, lem-sfb-integral-fibre-section-specialization (original step 3 and the full-source part of step 5).** This worker assumes the geometric hypotheses rather than redoing root geometry. Apply lem-sfb-integral-lisse-closed-base-change to integral q_P, the closed s and the pulled lisse module. Use new-lem-weil-pbc-condensed-surjective-closed-equivalence for a_P. Its inverse-image equivalence is exact and its right adjoint is the inverse equivalence, so that right adjoint is exact; its actual unit therefore induces an invertible derived unit. Compose with R(q_Z,P)_* and use q_Z,P a_P = rho_P and h_P a_P = i_P. The derived composition normalization lemma identifies the result with the adjunct of the pulled actual counit in the new statement. This identification, not mere existence of an isomorphism, is the work that must also be proved. It gives H^0 restriction and the one-point normalization. Naturality of the exchange mate, actual unit and composition identifications must be proved on the whole Q-test squares and on simultaneous Q x P' -> P parameter maps, rather than pointwise. For coefficients, the adjunct exists for arbitrary degree-zero modules even when its invertibility is unavailable. Apply its naturality to L_E -> Res L_Omega and then the canonical directional direct-image/restriction comparisons. The middle restricted module need not be finite-rank lisse over E; only the two original L_F need this property for their own isomorphisms. Thus no invalid lisse assumption is imposed on Res L_Omega and no directional comparison is inverted. This retains the original full-source normalization, family action and scalar arguments as one substantial independent work item.

**Existing puncture package (original step 1 and the open-unit part of step 5).** lem-sfb-root-tower-puncture-invariance already contains one-coordinate supported vanishing, the closed-support triangle on principal opens, induction over the coordinates and actual composite unit normalization. For the parent, pull a finite-free trivialization to T[P] and observe directly that its defining root equations are base changed from U to U[P]; these two checks remain explicit in assembly step 1. The existing lemma includes the Q-family equality. Applying s^*Rq_P and normalized composition yields lambda. Scalar naturality of the actual unit is the usual adjunction naturality for the actual tensor-unit module map, before any isomorphism is cancelled.

**Existing function package and final assembly (original step 4 and remaining step 5).** The supplied boundary model is pulled back along rho_P with the canonical point-pullback coherence. Since S is affine, lem-sfb-profinite-constant-derived-functions applies to the exact finite-dimensional continuous model M_F. Compose its specified exponential-law comparison with theta to obtain gamma; alpha = gamma lambda^{-1}. At P=* the function comparison is identity and theta is normalized actual restriction, giving the specified inverse-open-unit interpretation. All family and coefficient equalities now follow by substitution of the input squares and cancellation of invertible lambda; neither scalar-extension/direct-image commutation nor detection at points of Q is needed. This cancellation is assembly, not a hidden extra comparison lemma.

**Degenerate cases (original step 6).** Retained explicitly in assembly step 5: r=0 reduces to the function comparison; P empty and rank zero give zero; an empty stratum gives the zero object on the empty site; finite P gives the finite product of the one-point models. No finite-to-profinite cohomology/limit interchange is introduced.

## Not duplicates

lem-sfb-parameter-root-integral-nil-fibre vs lem-sfb-root-tower-coordinate-face: the existing statement is a derived lisse-module face exchange under regular-SNC hypotheses and mentions its surjective closed face, but does not state finite monomial bases or integrality of arbitrary-ring parameter root projections; the new statement is coefficient-free algebra over any ring, with arbitrary ring base change and the nil kernel calculated explicitly.

lem-sfb-parameter-root-integral-nil-fibre vs lem-weil-pbc-monic-quotient-free: one monic quotient is the finite-stage input, not the full compatible multi-root colimit with profinite parameters and nil closed fibre.

lem-sfb-parameter-root-integral-nil-fibre vs lem-weil-pbc-finite-algebra-is-integral: the existing finite-module implication does not supply the root or parameter presentation, the infinite colimit or its fibre quotient.

lem-sfb-parameter-root-integral-nil-fibre vs def-sfb-full-parameter-root-tower: the existing node defines root and deck-character data; it is not a theorem of integrality or a nil-fibre calculation.

lem-sfb-integral-fibre-section-specialization vs lem-sfb-root-tower-coordinate-face: the existing statement is restricted to regular-SNC compatible-root towers and coordinate subsets, and has no E-to-Omega directional restriction cospan; the new input allows arbitrary affine fibre-section diagrams and identifies the actual specialization adjunct with the derived nil-fibre unit, including that cospan. It is not a special case of the existing node.

lem-sfb-integral-fibre-section-specialization vs lem-sfb-integral-lisse-closed-base-change: cartesian exchange ends on B_P, whereas the new assertion ends on Z[P] through a supplied surjective closed fibre section, identifies the composed adjunction, and states its full family and coefficient diagrams. This normalized noncartesian restriction is the extracted argument, not a restatement of cartesian exchange.

lem-sfb-integral-fibre-section-specialization vs new-lem-weil-pbc-condensed-surjective-closed-equivalence: the existing assertion is only an inverse-image equivalence; it does not identify a noncartesian derived specialization adjunct or its canonical scalar cospan.

lem-sfb-integral-fibre-section-specialization vs lem-sfb-closed-test-derived-exchange-model: the existing statement is an evaluation formula on w-contractible ind-etale tests for cartesian exchange; it neither assumes the fibre section nor asserts its noncartesian derived restriction is invertible.

lem-sfb-integral-fibre-section-specialization vs lem-sfb-root-tower-boundary-acyclicity: the new assertion is entirely unpunctured and has no constant model or internal derived functions; the item still needs puncture removal, evaluation and normalized assembly. Neither new node restates the item or one of its numbered conclusions.

## Review by NN

I read delivery-errors B through E in both copies, the current item and all six original steps, its Lean statement/docstring and sorry, the original NI report, the current chapter/unit blueprint text and the direct-images proof paragraph (3). For the new geometry statement I checked its algebra against the opened statements of monic-quotient-free and finite-algebra-is-integral and the integral and closed-immersion definitions. For the new specialization statement I read the entire integral-lisse-closed-base-change statement, the exact Lean-statement node for condensed surjective-closed equivalence, and the complete normalized derived-composition theorem. I also read Stacks etale-cohomology.tex lemma-integral-pushforward-commutes-with-base-change (Tag 0EYP) and proetale.tex lemma-closed-immersion/lemma-thickening (Tags 09AA/09AB). The former is only a discrete-etale analogue, not a source for all-continuous derived coefficients; the latter supplies the topological route, without a bounded nilpotence requirement. No SGA source is used.

In assembly step 1 I checked that puncture invariance has precisely the same primes, topology, regular chart, SNC branches, root transition maps, lisse extension and actual profinite test schemes, and that it asserts the actual unit for all coordinates and its Q-family naturality. The composition theorem states that units are exactly the composite units, which is the normalization taken here. Pullback of a trivialization establishes the lisse hypothesis rather than assuming a geometric stalk argument.

In step 2 I checked that the new geometry lemma supplies every hypothesis of specialization: integral q_P for every P, the closed s, and the actual a_P with both commuting equations. Specialization requires neither a finite-type tower nor a uniform nil exponent. It states the exact displayed derived theta and its adjunct normalization, so the step does not borrow anything from its future proof. The root fibre is not identified with S[P] as a scheme.

In step 3 I opened profinite-point-pullback: it states composition coherence for modules and termwise derived functors. I opened profinite-constant-derived-functions: its affine-X hypothesis holds because S is closed in affine U; it allows the actual finite-dimensional M_F with incomplete Omega and states a derived isomorphism, not just H^q identities. This gives exactly gamma. Composition with inverse lambda is elementary categorical assembly.

In step 4 I checked the normalization and naturality clauses of both comparison statements and the puncture unit. All uses are in those statements and are quoted in citations.json, including family and scalar clauses. In particular the new specialization statement explicitly allows defining the adjunct on the restricted Omega module without asserting that this restricted module is finite-rank lisse over E. Its scalar assertion uses a cospan of directional maps; the item only cancels its own invertible puncture units. The function statement supplies the actual E-to-Omega map and whole-Q naturality. This checks both C4 and the subtle coefficient hypotheses in C1. The composite diagram is evaluated over U[Q], not inferred by equality at points.

For step 5 and the new statements I tested r=0, r=1 with t=0 or t invertible, P empty, P a point, finite P, empty stratum, zero ring and rank zero. The algebra fibre when t=0 has nilpotent roots but a generally unbounded nil ideal; when t is a unit its common-zero fibre is empty. The specialization hypotheses hold for the identity diagram and surjective closed nil thickenings and the comparison becomes their actual unit/counit. These tests exclude the false scheme-equality or uniform-nilpotence claims. All notions are introduced in each new statement; their definition nodes are cited. No new proof steps or proof dependencies are placed in statement-only nodes.

All new-node Mathlib queries were actually run with msearch.py; full returned output was read and retained. Each node has LeanSearch, LeanFinder (two phrasings), Loogle and source grep; geometry has an additional targeted RingTheory grep. The geometry hits include integral-morphism SpecMap_iff and stability, finite/integral proper-morphism facts, nilradical, IsAdjoinRoot.ker_map, and AdjoinRoot.isIntegral_root': these are individual inputs, not one-line statements of the whole parameter-root fibre theorem. The specialization hits are ordinary restriction/stalk maps, scheme-module restriction adjunction, and normalization or closed-map facts, not derived pro-etale continuous-module specialization. All services succeeded; no unavailable result was labelled a negative match. No new statement has a Stacks source tag requiring a mechanically generated tag-pair distinction; the substantive overlaps are distinguished above.

I checked every assembly step for hidden arguments and retained all old arguments in the inventory. The longest new assembly step is under 1000 characters and the complete assembly is 2529, below the requested 3000. The two new obligations divide different arguments of similar practical size: a finite-stage/colimit/nil-fibre algebra construction, and derived mate identification with family and scalar coherence. The reuse of existing puncture invariance is explicitly documented rather than creating a forbidden duplicate. Each new node has no dependency path to the item; the server dry run checks cycles and the live overlay.

## Unfinished obligations and validation

The two new statements are intentionally unsplit and ready for independent workers. The all-continuous source requests remain open as explicitly recorded. No part of this one-level repair is deliberately omitted. No compiler, Lake or build tool was run and no repository or launcher file was written. The required deliver.py --no-push and final push perform the server preflight; their result is reported by the tool and final delivery line.

## Returned proof, preserved verbatim

### Original step 1

Write $q:T\to U$ for the full root morphism, $\pi_P:T[P]\to T$, and $q_P=q\pi_P$. The full parameter extension is $\mathcal N_P=\pi_P^*\mathcal N$. It is lisse, since pullback of a finite free trivialization remains finite free. The root equations commute with base change from $U$ to the affine pro-etale test object $U[P]$; thus $T[P]$ is the same full root construction over $U[P]$. For $J_d=\{1,\ldots,d\}$ put $e_d:T[P]_{J_d}\hookrightarrow T[P]_{J_{d-1}}$. Apply [lem-sfb-root-coordinate-supported-vanishing] to $\mathcal N_P$, with $J=J_{d-1}$ and $a=d$. The support term in the distinguished triangle of [det-lem-formal-closed-support-adjunction] is zero, so its second arrow, the actual unit, is an isomorphism $\mathcal N_P|_{T[P]_{J_{d-1}}}[0]\to R(e_d)_*(\mathcal N_P|_{T[P]_{J_d}}[0])$. Start with $d=1$ and compose these isomorphisms for $d=1,\ldots,r$. The normalized derived composition of [lem-sfb-derived-composition-adjunction-normalization] identifies the composite with the actual unit $\eta_P:\mathcal N_P[0]\to R(j_P)_*j_P^*\mathcal N_P[0]$, where $j_P:T^\circ[P]\hookrightarrow T[P]$. For $r=0$, the composite and unit are identities. Applying $s^*Rq_{P,*}$ and derived composition gives an isomorphism
$$\lambda_P:s^*Rq_{P,*}\mathcal N_P[0]\xrightarrow{\sim}s^*R(v_P)_*j_P^*\mathcal N_P[0].$$

Cited nodes: lem-sfb-root-coordinate-supported-vanishing, det-lem-formal-closed-support-adjunction, lem-sfb-derived-composition-adjunction-normalization.

### Original step 2

The morphism $q_P$ is integral [def-weil-finite-integral-morphism]: by [lem-weil-pbc-monic-quotient-free] every finite root algebra is generated by elements satisfying the displayed monic equations and is finite free with basis the monomials of exponents less than $n$; adjoining finitely many such elements gives a finite module by successive division by their monic equations. [lem-weil-pbc-finite-algebra-is-integral] makes every such finite stage integral. Every element in the filtered root algebra lies at one finite stage and is therefore integral. Each finite test projection is a finite product of copies of its base ring, also integral; every element of its filtered colimit again lies in a finite stage. These observations apply after base change and prove integrality for their composite $q_P$. Put $B_P=T[P]\times_U S$, with projections $h_P:B_P\to T[P]$ and $q_{S,P}:B_P\to S$. There is a closed immersion $a_P:S[P]\hookrightarrow B_P$ setting all roots to zero. It is surjective on underlying spectra: in the fibre every $x_{a,n}$ is nilpotent since $x_{a,n}^n=0$, so every prime contains every root. Conversely quotienting by all these roots is precisely the ring of $S[P]$. The kernel consists of nilpotents: each element involves finitely many nilpotent roots and an ideal generated by finitely many nilpotents is nilpotent. A common nilpotence exponent for the whole infinite kernel is neither claimed nor needed. The parameter projection satisfies $q_{S,P}a_P=\rho_P:S[P]\to S$.

Cited nodes: def-weil-finite-integral-morphism, lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-algebra-is-integral.

### Original step 3

Apply [lem-sfb-integral-lisse-closed-base-change] with $q=q_P$, the closed immersion $s:S\hookrightarrow U$, and the lisse module $\mathcal N_P$. The hypotheses established in steps 1 and 2 give the specified exchange isomorphism
$$s^*Rq_{P,*}\mathcal N_P[0]\xrightarrow{\sim}R(q_{S,P})_*h_P^*\mathcal N_P[0].$$
By [new-lem-weil-pbc-condensed-surjective-closed-equivalence], $a_P^*$ is an equivalence for the actual pulled-back ring $C_F$; hence its actual unit is an isomorphism, not just a comparison of geometric stalks. Its inverse image is exact; the inverse equivalence $a_{P,*}$ is therefore exact too, and its derived functor is its degreewise application. Thus $h_P^*\mathcal N_P[0]\to R(a_P)_*a_P^*h_P^*\mathcal N_P[0]$ is an isomorphism. Derived composition [lem-sfb-derived-composition-adjunction-normalization] and $q_{S,P}a_P=\rho_P$ identify the last direct image with $R(\rho_P)_*(\rho_P^*i^*\mathcal N[0])$. This uses the nilpotent-fibre equivalence; it does not assert $B_P=S[P]$ as schemes.

Cited nodes: lem-sfb-integral-lisse-closed-base-change, new-lem-weil-pbc-condensed-surjective-closed-equivalence, lem-sfb-derived-composition-adjunction-normalization.

### Original step 4

Pull the supplied identification $i^*\mathcal N\cong p_S^*M_F$ back along $\rho_P$. Pullbacks of coefficients compose canonically by [lem-weil-pbc-profinite-point-pullback], so $\rho_P^*i^*\mathcal N\cong p_{S[P]}^*M_F$. Now apply [lem-sfb-profinite-constant-derived-functions] with $X=S$ (affine since $S$ is closed in the affine $U$) and the given $M$. Together with step 3 this defines an isomorphism
$$\gamma_P:s^*Rq_{P,*}\mathcal N_P[0]\xrightarrow{\sim}p_S^*R\underline{\operatorname{Hom}}_{C_F}(C_F[P],M_F).$$
The required map is $\alpha_P=\gamma_P\lambda_P^{-1}$. This produces an isomorphism in the derived module category itself, rather than a family of per-degree identifications.

Cited nodes: lem-sfb-profinite-constant-derived-functions, lem-weil-pbc-profinite-point-pullback.

### Original step 5

All arrows in $\gamma_P$ are the exchange adjunct, the topological-invariance unit, pullback of the supplied boundary identification, and the normalized exponential-law map. Hence in degree zero $\gamma_P$ restricts full-tower sections to $S[P]$ and then regards them as functions of $P$. The arrow $\lambda_P$ is induced by $\mathcal N_P\to R(j_P)_*j_P^*\mathcal N_P$. For $P=*$ the function comparison is the identity, and $\gamma_*$ is the canonical identification with $i^*\mathcal N$: its inverse is induced by the full-tower pullback adjunction and is checked by the triangle identities. Consequently $\alpha_*$ is the inverse of the map induced by that open unit, under this identification. Naturality of units, the normalized composition comparison [lem-sfb-derived-composition-adjunction-normalization], and the naturalities explicitly in [lem-sfb-integral-lisse-closed-base-change] and [lem-sfb-profinite-constant-derived-functions] make $\alpha_P$ natural in parameter maps, maps of supplied extensions, and pro-etale base change. For a continuous family of root automorphisms indexed by $Q$, apply the same diagrams after base change $U[Q]\to U$; their action on $\mathcal N$ supplies the module arrow over that base. The parameter naturality of the function comparison gives equality on these $Q$-parametrized diagrams. Inverting $\lambda$ preserves the equality, so this is the required family-level equivariance. Finally the two input comparisons commute after scalar restriction with $x\mapsto1\otimes x$, while the units and restriction of sections commute with that same map. The two commuting squares for $\lambda_E,\lambda_\Omega$ and $\gamma_E,\gamma_\Omega$ imply the square for $\gamma\lambda^{-1}$ by cancellation. No scalar-extension/direct-image isomorphism is inferred.

Cited nodes: lem-sfb-integral-lisse-closed-base-change, lem-sfb-profinite-constant-derived-functions, lem-sfb-derived-composition-adjunction-normalization.

### Original step 6

For $r=0$, $T=T^\circ=U$, $S=U$, $\lambda_P$ is the identity, and the construction is exactly the parameter-functions comparison. For $P=\varnothing$, the source is the direct image from the empty scheme and the target is derived Hom from the zero free module, so both are zero. Rank zero and the empty stratum give zero on both sides. For finite $P$, the parameter formula gives the finite product of the $P=*$ models; no passage from finite sets to profinite sets by an unjustified cohomology/limit interchange has been used.

Cited nodes: .

## Retained original delivery report (NI, 2026-10-21)

# Stage-1 delivery: lem-sfb-root-tower-boundary-acyclicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-boundary-acyclicity.json — statement, split, no Mathlib match; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-root-coordinate-supported-vanishing.json — statement-only, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-integral-lisse-closed-base-change.json — statement-only, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-profinite-constant-derived-functions.json — statement-only, unsplit, no Mathlib match.
- citations.json — a verbatim statement excerpt for every step/node pair.

## Attachments

None. Searched the live WeilConjectures source by the blueprint tag and root-tower/boundary/Kummer/continuous-coefficient notions. KummerCover.lean constructs punctured root covers; SixFunctors/Integral/BaseChange.lean supplies discrete small-etale integral base change, not this internal continuous-coefficient assertion. Neither is an attachment of the item or a new node. Project declarations containing sorry do not close a node.

## WANTED

WANTED: a proof of one-coordinate local-cohomology vanishing on the full prime-to-p root tower, for arbitrary affine pro-etale charts and lisse modules over all norm-continuous E and incomplete Omega coefficients, including after inverting other branches, for lem-sfb-root-coordinate-supported-vanishing.

WANTED: a proof of the specified closed derived base-change map for integral affine morphisms and lisse internal norm-continuous E and Omega modules on small pro-etale sites, with the given parameter and coefficient naturalities, for lem-sfb-integral-lisse-closed-base-change. Stacks 0EYP is its discrete-etale analogue only.

WANTED: a proof that relative profinite-test projection realizes derived internal functions of the actual all-continuous finite-dimensional coefficient model, including base change and maps over profinite families, for lem-sfb-profinite-constant-derived-functions.

## Audit and changes

The imported item has no proof and its own source explicitly asks for an exact all-continuous reference. I retained every hypothesis and conclusion. The actual source paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md states open direct-image preservation using sk-prop-open-coefficients. It does not state this expanded root-tower calculation. The proof is therefore marked agent, and each genuinely missing input is a statement-only node with an explicit WANTED, rather than misattributing the stronger result to a finite-coefficient theorem or to Bhatt–Scholze.

Read the current chapter record and current blueprint unit section; dag/units/sk-thm-sf-ctf-stability.json is still the older sec-six-functors unit, whereas the source of this item is the current sec-six-functors-basics expansion. This item is not the unit key and no unit record was changed. The existing created.item chain stops at lem-sfb-admissible-direct-image, so blueprint_refs.py ancestor prints None. Retained the inherited null ancestor and exact via chain, and extended it for children; each place identifies the actual current blueprint paragraph. The whole blueprint was searched for Kummer, root, acyclic, closed support, parameter, integral pushforward, profinite projection, and supported vanishing. Existing finite-coefficient strict-local Kummer nodes and root extension/support nodes were opened. None states the three proposed missing inputs. In particular lem-per-strict-local-snc-kummer-cohomology is about F_ell on a Noetherian strictly henselian regular local scheme; it does not justify all-continuous derived support vanishing.

The key fibre calculation needed care: the fibre of T over S still has nilpotent roots. It is not S as a scheme. The proof constructs the surjective closed immersion setting all roots to zero and uses the existing condensed topological-invariance equivalence, which does not require a uniform nilpotence exponent. This is a correction of a possible invalid proof inference, not a change to the item's statement.

Every new node has two phrasings and all four requested search methods, recorded directly from searches.jsonl. The semantic hits on BDeRham and Noebeling constructions do not state these sheaf results. The nearest parameter hit, LightCondensed.ihomPoints, was read in Mathlib/Condensed/Light/InternallyProjective.lean:52 onwards: it is an underived adjunction over a discrete ordinary ring on light profinite sets, with no scheme pullback or K-injective derived comparison. It is not a one-line specialization of the new node. Mathlib's integral base-change hits in Morphisms/Integral.lean:35–80 are about integral scheme morphisms themselves, not cohomological exchange. No false negative from an unavailable service was recorded; all searches used here succeeded.

## Not duplicates

lem-sfb-root-coordinate-supported-vanishing vs lem-per-strict-local-snc-kummer-cohomology: the latter computes ordinary finite F_ell etale cohomology of a Noetherian strict-local complement; the former asserts vanishing of a supported derived object on the infinite root scheme with internal all-continuous coefficients.

lem-sfb-root-coordinate-supported-vanishing vs lem-sfb-root-tower-inner-support: the latter is an outer direct-image/inner closed-unit comparison and uses the assigned item; it cannot be used to prove the item. The new input is one-coordinate local support before any direct image or nerve.

lem-sfb-profinite-constant-derived-functions vs lem-sfb-root-tower-boundary-acyclicity: the new statement involves an arbitrary affine base and a constant model with only its relative profinite test projection; it has no puncture, root construction, lisse extension across a boundary or inertia. The item's steps still perform the geometric support induction, integral exchange, nilpotent-fibre identification and normalization.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-underived-exchange: existing statement is underived exchange for modules over an ordinary discrete ring on the small etale site; new statement is derived pro-etale exchange for lisse internal modules over a pulled-back norm-continuous condensed ring, with no general exactness assertion.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-geometric-point-exchange: existing statement is underived small-etale exchange at one geometric point with discrete coefficients; new statement concerns the actual derived object over a closed scheme and condensed coefficients, including profinite families.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-geometric-fibre-sections: existing statement identifies an ordinary geometric stalk with ordinary sections, whereas new statement is a derived module-object comparison over the entire closed scheme.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-strict-local-fibre-comparison: existing statement compares small-etale sections after strict henselization with geometric-fibre sections for a discrete ring; new statement is not an ordinary section or geometric-point claim.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-fibre-section-local-lift: existing statement lifts a discrete-etale fibre section to one pointed neighbourhood; it says nothing about the derived pro-etale coefficient comparison.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-integral-fibre-section-local-zero: existing statement kills a discrete-etale neighbourhood section whose fibre restriction vanishes; it is not a statement about the new derived internal-module exchange.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-geometric-fibre-exchange-germs: existing statement is a formula on pointed small-etale germs, with no integrality or isomorphism conclusion; new statement asserts invertibility of a particular derived closed exchange.

lem-sfb-integral-lisse-closed-base-change vs lem-sbc-strict-local-fibre-restriction-compatibility: existing statement identifies actual small-etale section restriction maps using strict-local legs; new statement is invertibility over a closed scheme in the continuous-coefficient derived category.

## Review by NI

I read delivery-errors B–E in full and checked these files against their mathematical failure modes. The new statements introduce their own objects and have no proof or proof_deps. Their definitions of lisse, coefficients, support and test schemes point to the exact existing definitions. The ordinary unbounded derived categories and coefficient universes are retained. I did not introduce any SGA route, any completed Omega, a finite-subextension interpretation of its functions, or an unjustified scalar/direct-image isomorphism.

For step 1 I opened the statements of the one-coordinate vanishing input, det-lem-formal-closed-support-adjunction and derived-composition-adjunction-normalization. Vanishing is supplied for every remaining coordinate after inverting the preceding ones. Each complement is a principal affine open, so the support triangle's quasi-compactness hypothesis holds even though the full root scheme need not be Noetherian. Its first term is zero and the second arrow is its actual unit. Finite induction on d=1,...,r is explicit; the composition theorem says its unit is the composite unit. Pullback and right derived direct image carry these isomorphisms to isomorphisms. The module over T[P] is pulled back from T and hence is again lisse; U[P] is an affine pro-etale base change, so the geometric input's chart hypothesis still holds.

For step 2 I read the monic-quotient-free node and finite-algebra-is-integral node, and their source calculations in algebra.tex (Tag 04GG, lemma-characterize-henselian; Tag 00GK, lemma-finite-is-integral). Their statements give the successive finite monomial bases and finite-to-integral implication used here. I corrected my initial version to cite them explicitly rather than hiding that algebra in an elementary label. The remaining filtered-colimit and nilradical arguments are written out. Every root in the closed fibre has a power equal to zero. A prime contains all such elements and the quotient is exactly the S[P] algebra, including when the base has its own nilpotents. No global nilpotence bound was inserted.

For step 3 I opened the complete statements of the integral base-change input, new-lem-weil-pbc-condensed-surjective-closed-equivalence and the derived composition normalization. The input is applied only to an integral affine morphism and a lisse degree-zero module; both hypotheses were established. The existing topological-invariance node asserts precisely that the actual condensed upperStar is an equivalence for a surjective closed immersion. Read Stacks proetale.tex Tags 09AA/09AB (lemma-closed-immersion and lemma-thickening) as its source: 09AB permits integral universally injective surjective maps, so in particular our nil closed immersion. The inverse equivalence is the specified direct image; this justifies its exactness and its degreewise derived form. I did not silently identify the nonreduced fibre with the stratum as schemes.

For step 4 I checked the full profinite-functions statement and the profinite-point-pullback composition statement. The latter explicitly includes module and derived-category pullback coherence, which is what the step uses, not a theorem asserted only in a definition's proof. S is affine, the supplied M is finite-dimensional, and its finite-dimensional norm topology is exactly the one required by the function input. This step composes actual derived isomorphisms; it does not infer a derived comparison merely from cohomology-group coincidences.

For step 5 I re-read the naturality clauses of both new comparison inputs and the normalization clause of the derived composition node. The left inverse of the open unit is gamma times lambda inverse; all units and exchanges are the specified adjunction maps. At P=* the full-fibre comparison is the canonical boundary restriction, and the pullback unit/counit triangle identities identify its inverse. Family equivariance is tested after the pro-etale base change U[Q], where it is a commuting diagram of maps over Q, using the profinite-functions input's family clause. This avoids detecting a condensed morphism solely at individual points. Ordinary E-to-Omega insertion is a map after scalar restriction; cancellation of the two natural squares proves the final square without assuming scalar extension commutes with pushforward. None of these naturalities is attributed to the mere existence of an arbitrary isomorphism.

Step 6 tests r=0, P=empty, finite P, rank zero, the empty chart and the empty stratum. The r=0 case reduces to the independent parameter-function input, and the others have zero or finite-product models as appropriate. Tested the geometric input at r=1, J=empty and after a parameter becomes invertible: empty support gives zero, while genuine support is exactly the new unsplit one-coordinate obligation. Tested integral exchange for identity and closed immersions (trivial or closed-support base change) and for the root morphism (not finite type, so its statement explicitly allows integral affine morphisms). The parameter statement at P=* has free module C_F and identity internal Hom; at empty P its free module is zero.

The three inputs are strictly distinct from clauses of the item: local support vanishing is before direct image and uses no boundary model; integral exchange is a general closed base-change comparison without a root tower; the parameter-function lemma is independent of roots and punctures. Their combination requires the full six-step argument. None depends on the item, and no circular use of root-tower-inner-support or tame-stratum descent is made. All node citations have verbatim excerpts in citations.json. Each non-elementary step is shorter than 2000 characters. I checked the larger step 5 particularly for a hidden geometric lemma; its non-formal comparison/naturality assertions are exactly clauses of the cited inputs.

## Unfinished obligations

No part of the one-level split is left unwritten. The three new inputs remain unsplit for future workers; their all-continuous assertions are not claimed proved by the present delivery. The split is an agent proof conditional on those explicit dependency nodes, as stage 1 requires. The exact references above remain wanted. No Lean was written and no compiler, Lake or build tool was run.

## Validation

Server-only preliminary review_split and check_dag invocations exited successfully. The required full deliver.py dry run and push are the final validation; their results are recorded by the delivery tool.
