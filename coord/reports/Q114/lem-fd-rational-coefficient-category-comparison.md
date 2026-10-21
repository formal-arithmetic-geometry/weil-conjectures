# Stage-1 repair: lem-fd-rational-coefficient-category-comparison

## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-rational-coefficient-category-comparison.json`: unchanged statement and Lean binding; five-step assembly of five smaller arguments, 2161 proof-text characters.
- `dag/nodes/sec-fourier-transform/lem-fd-integral-identity-rational-equivalence.json`: statement; `unsplit`; Mathlib verdict no match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep. No proof steps or proof dependencies.
- `dag/nodes/sec-fourier-transform/lem-fd-completion-inverse-scalar-coherence.json`: statement; `unsplit`; Mathlib verdict no match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep. No proof steps or proof dependencies.
- `dag/nodes/sec-fourier-transform/lem-fd-whole-tower-integral-pullback-comparison.json`: statement; `unsplit`; Mathlib verdict no match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep. No proof steps or proof dependencies.
- `dag/nodes/sec-fourier-transform/lem-fd-common-stage-comparison-descent.json`: statement; `unsplit`; Mathlib verdict no match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep. No proof steps or proof dependencies.
- `dag/nodes/sec-fourier-transform/lem-fd-frobenius-fixed-pair-comparison.json`: statement; `unsplit`; Mathlib verdict no match after LeanFinder (two phrasings), Loogle, LeanSearch and source grep. No proof steps or proof dependencies.
- `citations.json`: five parent-step citations, quoting the child statements verbatim.
- `report.md`: this review and the complete retained original argument, with the allocation of every old step to its new worker item.

There are **5 new nodes, 0 Mathlib leaves**. No Lean or project/launcher source was written, and no compiler, Lake or local DAG-check command was run. The only writes are in the item sandbox. `baseline.json`, `prior-Q05-report.md` and `prior-Q19-report.md` retain the previous delivered node and its reports. `searches.jsonl` and the five `*.search-results.json` files retain the searches actually performed on this repair; inherited item searches remain unchanged. The original sandbox contained only .brief2–.brief5, so it had no completed split/report or previous search log on which to run an initial dry run. I copied the live returned node as the baseline. The live node's earlier reviewed/split state is the explicit subject of the human's new re-split request, not a reason to skip the repair.

## Attachments

None. The blueprint-tag and conceptual searches in the live `lean/WeilConjectures/` find no exact completed declaration of the item. The recorded `WeilConjectures.rationalCoefficientCategoryComparison`, `lean/Sheaf/Paper/RationalCoefficientCategoryComparison.lean:213`, ends with `sorry` at line 218. I read its definition/data interfaces and full docstring: the eleven old mathematical arguments match its pins and the declaration. Its already-written structures do not prove existence. The upstream IsoAlgebra files supply general fixed-pair transport and full faithfulness, but not the geometric-fibre hypotheses, these normalized coefficient/pullback systems, or the specified finite/common-stage identification together. No new node duplicates a closed project declaration.

## WANTED

None. The blueprint and relevant Bhatt–Scholze and Stacks sources are available locally. The blueprint's final sentence fixes the interface to be compared and does not itself prove the comparison. The retained mathematical argument is agent-written; no fabricated theorem attribution is made for it. The new nodes are statement-only tasks and their `proof_origin` is null.

## Return repaired

The human's 2026-10-21 return demanded work distribution, at least three comparable statement-only child arguments, and an assembly of at most 3000 characters, preserving the statement and every argument. I added five child tasks, each with its own introduced objects, hypotheses, source place, blueprint ancestry, actual three-kind Mathlib search records, and empty proof/proof_deps. The parent uses all five, and its complete proof text has 2161 characters. The unchanged statement still demands the actual tensor/quotient completion maps, shifts, finite-stage inclusions, Hom colimits, all scalar and scheme coherence, and the fixed-pair comparison. Nothing has been replaced by an unspecified equivalence.

The partition is: old steps 1–2 (1319 characters) go to integral identity/raw rationalization; 3–4 (1959) to completion-inverse scalar coherence; 7–8 (2791) to whole-tower integral pullback; 5–6 and 9 (2555) to exact linear common-stage descent with pullback transformations; 10–11 (1696) to geometric-fibre hypotheses and fixed-pair transport. These are separate construction/verification arguments of comparable scale, and no child is the whole comparison. Their total is exactly the old 10320 characters. All old text is reproduced below without abbreviation. The child statements record what future proofs must establish; the old proof hints, old dependencies, and mathematical calculations stay in this report rather than being hidden in an unsplit statement.

The finite and integral children assume the other inputs they use, with explicit pins. In particular the scalar child assumes the identity equivalences rather than proving them again; the common-stage child assumes finite equivalences and their coherent maps; the integral pullback child assumes only those finite inputs; and the Frobenius child assumes a given simultaneous comparison system. None assumes the existence assertion of the parent, and none cites it. Thus the five proof obligations can be worked independently using the hypotheses in their statements. The parent obtains their inputs in order. This is the specific human-authorized re-split of the old argument, not an attempt to make a new node out of a two-line calculation in an ordinary first split.

## Searches and existing material

I read all original parent statement/proof dependency statements, including the complete specified-map clauses of the integral realization, finite-free completion, integral well-definedness and coefficient-datum nodes. Whole-DAG title/statement searches covered rational coefficient equivalences, scalar/completion inverses, quotient-tower comparisons, common-stage equivalence/descent and fixed-pair transport. Whole-blueprint searches included `rational coefficient`, `scalar comparison`, `common-stage equivalence`, `pullback comparison`, `fixed pair`, `integral identity`, `raw rationalization equivalence`, `completion inverse`, `quotient tower` and `Frobenius fixed pair`. They found definitions and different comparisons, not an imported node with any new statement. `blueprint_refs.py ancestor` gives `def-fd-trace-function`; each child has via=[the parent], and its precise old argument allocation is recorded in `from.place`. The parent already has that ancestor, a precise place and same_as=[]; these are retained. This auxiliary is not the trace unit's key node, so no unit realization or chapter route was changed.

Each of the five new ids was checked absent before creation. Mathlib searches were run only through the authorized msearch command and their exact queries/results are generated from the saved outputs. Every service answered successfully. Loogle's unknown identifier for the project-only IsoAlgebra name is recorded as a successful zero-hit search with that diagnostic, not as a claim that the project declaration is absent. I read the hits' types: generic localization uniqueness and triangulated localization do not supply the actual constructible identity/pins; ordinary adic completion and monoidal associator naturality do not prove the quotient-map completion cocycle; generic IsEquivalence does not establish the exact linear equivalence on these common-stage Hom colimits; ordinary limit uniqueness and categorical pullback comparisons do not identify the derived whole-tower realizations and counits; isocrystal/field-Frobenius facts do not give the actual geometric-Frobenius fixed-pair comparison. The source greps confirm the project-specific machinery is absent from Mathlib. Therefore all five are unsplit rather than Mathlib leaves. No search that did not run is added.

## Not duplicates

lem-fd-integral-identity-rational-equivalence vs lem-weil-pbc-integral-stratified-perfect-characterization: The existing statement characterizes one common full integral subcategory and its closure properties. The child constructs the presentation identity equivalences and their exact raw Hom-tensor rationalizations with explicit coefficient-transport, reduction and shift pins.

lem-fd-integral-identity-rational-equivalence vs lem-weil-linear-scalar-localization-triangulated: The existing theorem gives triangulation of one scalar localization; the child compares the two concrete integral/rational presentations with all identity formulas. Its old argument uses this theorem as a tool.

lem-fd-integral-identity-rational-equivalence vs def-fd-coefficient-comparison-datum: The existing node defines comparison data and asserts no existence. The child proves existence of its integral/finite equivalence part only.

lem-fd-completion-inverse-scalar-coherence vs lem-weil-finite-free-completed-scalar-comparison: The existing theorem specifies one completion isomorphism chi and its identity case. The child verifies that all inverses form an exact scalar-system comparison with the specified associators, shifts, cocycle and four-field normalization.

lem-fd-completion-inverse-scalar-coherence vs lem-trf-integral-pullback-comparison-realization: The existing result normalizes the framework tower and scalar associator. The child compares that associator to the ordinary PBC one under the chi-inverse maps on raw rationalizations.

lem-fd-whole-tower-integral-pullback-comparison vs lem-trf-integral-pullback-comparison-realization: The existing statement constructs framework iterated pullback/scalar realizations eta/lambda/mu. The child compares framework versus actual PBC pullback realizations and their two unit/composition structures with the ambient chain pins; neither node states that comparison of presentations.

lem-fd-whole-tower-integral-pullback-comparison vs lem-weil-isomorphism-comparison-scalar-extension: The existing statement compares inverse image g^{-1} to the framework pullback via kappa and alpha. The child compares the actual PBC completed pullback, modeled by its whole derived strict tower, to the framework product-cone model with simultaneous scheme and scalar coherence.

lem-fd-whole-tower-integral-pullback-comparison vs def-fd-finite-pullback-comparison-datum: That node defines a normalized ambient integral/rational lift and asserts no existence. The child constructs it together with the scheme and coefficient equations.

lem-fd-common-stage-comparison-descent vs lem-sbc-coherent-pair-functor-descent: The existing generic result proves additive functor/transformation descent. The child additionally proves equivalence by inverse Hom bijections and same-stage essential surjectivity, Omega-linearity, exactness in both directions for common-stage triangles, and matches the actual rational/completed-pullback datum fields. The old Hom cancellation/triangulated/linearity arguments remain separate work.

lem-fd-common-stage-comparison-descent vs def-fd-pullback-comparison-datum: That node packages data, with no existence assertion. The child constructs the common-stage data conditional on finite coherent inputs and proves their exact linear and transformation properties.

lem-fd-frobenius-fixed-pair-comparison vs def-sf-projection-weil-coefficient-comparison: That node defines the geometric-Frobenius comparison structure. The child proves its geometric-fibre hypotheses and existence from a supplied simultaneous system, including the underlying intertwining Hom bijection.

lem-fd-frobenius-fixed-pair-comparison vs lem-sf-fixed-pair-adjunction-lift: The existing generic result concerns lifting an adjunction whose exchange is an invertible mate. The child uses an equivalence plus natural isomorphism and also establishes geometric-fibre hypotheses and finite/common coefficient compatibility; it does not assert a new derived/triangulated structure on fixed pairs.

lem-fd-frobenius-fixed-pair-comparison vs def-weil-weil-sheaf-complex: This is the definition of Weil pairs and their intertwining arrows, not the proof of comparison from a normalized coefficient system.

All five new nodes vs lem-fd-rational-coefficient-category-comparison: the parent proves existence of the complete system and its geometry. Each child is only one construction layer, with the other required finite/system inputs explicitly assumed. No child restates the entire result. The long-proof return explicitly authorizes splitting these separate old arguments.

## Review by Q114

I read the stage-1 brief, delivery-errors B–E in full, the three-level rule in SETUP, GOAL, the Fourier chapter and sk-def-trace unit, and the current main-20261015 trace definition and unit. Its final sentence requires the PBC Qbar coefficient category while its Weil inputs use the framework system. The new children serve exactly this interface. I checked the live Lean module's theorem is sorried and its data pins are genuine definitions, not completed proofs. The parent statement is unchanged character for character; the protected imported/reviewed/Lean fields are retained and no other project's file is edited.

For parent step 1 I opened the integral-identity/raw-rationalization child's entire statement. It asserts identity of the integral full-category presentations, preserved finite reductions, the formulas K->K and u tensor x->u tensor x, exactness and the shift pin. These are precisely the conclusions this step uses. Its hypotheses have the same noetherian, finite-dimensional, invertibility and finite-field assumptions as the parent. I checked the underlying source inputs against Bhatt–Scholze 6.6.11, 6.8.2(1), 6.8.11(3) and against the actual integral-characterization statement; the latter explicitly adds the equality of these full subcategories and closure under cones and shifts. The comparison is about the completed ring sheaf with its quotient projections, not merely an abstract equivalence of object lists. The original two-step proof and localization-triangulation citation are retained below.

For parent step 2 I read the completion-inverse scalar child's full statement. The assumed identity equivalences are exactly those from step 1. It asserts the integral tensor-generator/completion chain lift, the correct direction j:J_L S -> P J_E, the shift compatibility and the exact cocycle that is used. I type-checked the cocycle: both sides start at J_M S_(M/L) S_(L/E) K and end at P_(M/E) J_E K. The given chi goes from ordinary extension to strict-tower completion, so j is its inverse. The framework associator's conjugation normalization is actually in the statement of lem-trf-integral-pullback-comparison-realization, not borrowed from the weaker scalar-composition theorem's proof. Quotient maps and zero shifted coordinate fix the unit/shift conventions; the four-field equation is not replaced by an arbitrary choice of associator. I checked repeated fields and a torsion object, which becomes zero rationally.

For parent step 3 I read the whole-tower child's full statement and checked that it asserts exactly the normalized integral comparison, ambient lift, simultaneous realization, unit/composition and mixed scalar equations the parent uses. The input is the chosen identity equivalences and specified chi inverses, not a given pullback comparison. Both schemes are allowed, so the integral characterization applies at source and target. I read Stacks proetale.tex, Tag 099N, lemma-pushforward-Noetherian-case (2),(5), for completed pullback as ordinary pullback followed by derived completion; the constant/completed coefficient transport remains explicit in the existing PBC definition. I read derived.tex, Tag 070M, lemma-difficulty-K-injectives, and the complete stronger DAG Roos statement, rather than attributing its arbitrary-tower generalization verbatim to that tag. I read lem-pc-kflat-resolution, integral-operations-well-defined, integral-operations-preserve-constructible, exact pro-etale products and K-injective existence: the sites used are small tower/ringed sites, and the replacements need not have constructible individual terms. Exact products carry the levelwise quasi-isomorphism Q->I to a quasi-isomorphism of product cones. The natural Roos arrow is specifically (0,inclusion). Thus the requested isomorphism is of realizations of the entire strict quotient diagram, with counit, not inferred from equality of separate reductions. I checked the unit and scheme-composition equations have the stated directions. In the mixed square both sides start at J_(U,L) S_U F_s K and end at F_(h,L)^p P_T J_(T,E)K. No finite Tor-amplitude assumption on reductions is inserted. The full original arguments 7 and 8, including the cancellation and diagram normalizations, remain below.

For parent step 4 I opened the common-stage child's statement and the existing lem-sbc-coherent-pair-functor-descent. The latter covers only additive descent and equations of compatible transformations; it does not give the new child's complete exact linear equivalence conclusion. I retained the explicit Hom inverse, essential surjectivity, scalar-at-one-common-stage and common-cone arguments as this child's work. Its assumptions are exactly the finite J/j and mixed square now established. In the common-stage formula j at the target is on the left and j inverse at the source is on the right, so the source/target objects match. I checked the actual common-stage definitions, including the inverse shift comparison in the third cone arrow, and both directions of exactness. The transformation part asserts that the finite b classes form the actual common-stage natural isomorphism and preserve all finite coherence equations. Its conclusion explicitly supplies the common-stage datum fields; the integral lifts and finite maps supplied by the earlier steps complete the datum. The original step-9 mixed-square substitution is preserved below, not abbreviated to the word 'transports'.

For parent step 5 I opened the entire geometric-fibre/fixed-pair child's statement and the Weil-pair definition. This child assumes a supplied simultaneous system, which is precisely what steps 1–4 construct, and does not prove that complete system again. I read Stacks morphisms.tex, Tag 01T6, lemma-finite-type-noetherian, and the statement of lem-kun-dimension-finite-type. A finite affine cover with tensor-extended algebra generators proves X finite type over k; Spec k is noetherian because the field has only two ideals; ell is a unit since its nonzero image in k is invertible. I checked the Frobenius definition gives the scheme automorphism with its inverse, and the comparison never requires it to be a k-morphism. The fixed-pair functor's structure map has the correct direction J(theta) b inverse. Naturality of b converts the actual intertwining equation in both directions, and the original full-faithfulness and inverse-lifting argument is retained for the child's proof. For an underlying target merely isomorphic to JK, its structure is first transported along that isomorphism; one then applies the displayed Hom bijection. No identification of a pair category with a derived category is made.

For B1–B9 I checked that every child is an independently readable statement with explicit objects, scheme hypotheses, coefficient fields, map directions and normalization data, cites existing notion nodes, and has no proof steps/proof_deps or proof sketch in its statement. Sources and blueprint places identify the precise original argument. All ids are new; the substantive nearby results are distinguished above and are available as future proof tools rather than duplicated. The new nodes have no back-edge to the parent; in particular the Frobenius child does not assume the parent's scheme-coherence theorem, and it does not cite the separate projection comparison definition, which might obscure a back-edge. The parent statement/Lean record remains fixed. The new tasks have actual recorded searches; none is declared absent from one grep alone. I checked the original proof's long-step concern by distributing all old arguments rather than compressing them. No parent step exceeds 2000 characters, and the whole parent assembly is below 3000.

Small cases checked: T or X empty; Spec k0; zero and torsion integral objects; E=L=M and repeated fields in the cocycle; zero morphisms and two representatives of one arrow at different fields; a scalar defined only after enlarging the common stage; a Weil structure whose inverse must also lift; and an underlying PBC object isomorphic, rather than equal, to one in the image of J. The hypotheses suffice in each case, and no nonempty, regular, reduced, finite-Tor, or k-linear-Frobenius assumption has slipped in. I found no statement dispute. The corrected fault is solely granularity: five explicit work items now replace the old monolithic eleven-step proof, with every calculation retained for their future workers.

## Unfinished work

The five new nodes intentionally remain statement-only unsplit tasks for other workers, as the human requested. The parent is now a complete one-level assembly conditional on them. No proof of a new child is claimed, and no new Lean declaration is introduced.

## Retained original argument and allocation

The following eleven paragraphs are copied verbatim from the returned live node, with their original uses. They are proof guidance for the new unsplit nodes, not proof steps in those nodes. The original Q05 and Q19 reports are retained separately in the sandbox. Every argument must be implemented by the child assigned here.

### Original step 1 → lem-fd-integral-identity-rational-equivalence

For each finite $E$, apply the integral characterization to $T$: its noetherian, finite-dimensional and invertibility hypotheses are exactly those assumed here. Both integral categories are the same full subcategory of $D(\widehat{\mathcal O}_{E,T})$, with the same reduction functors, not merely categories with equivalent lists of objects. The identity therefore gives mutually inverse $\mathcal O_E$-linear functors on objects and all ambient derived morphisms. Shifts and distinguished triangles are inherited from that ambient derived category; the characterization's closure under shifts and cones makes this identification exact in both directions.

Original cited nodes: lem-weil-pbc-integral-stratified-perfect-characterization.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf; Proposition 6.6.11 and Proposition 6.8.11(3); applied through the stated integral characterization.

### Original step 2 → lem-fd-integral-identity-rational-equivalence

Use the raw Hom descriptions in the two rationalization definitions. Set $J_{T,E}K=K$ and $J_{T,E}(u\otimes e)=u\otimes e$. The balancing relation $(au)\otimes e=u\otimes ae$ is the same on both sides. Composition is $(v\otimes b)(u\otimes e)=(vu)\otimes be$, so this assignment preserves composition and identities and is $E$-linear. Its inverse has exactly the same formulas. Both shifts come from the common integral shift. By the scalar-localization triangulation theorem, both sets of distinguished triangles consist of triangles isomorphic to images of the same integral distinguished triangles. Thus $J_{T,E}$ and its inverse are exact; no retract is added.

Original cited nodes: def-weil-rationalization-karoubi, def-weil-pbc-rational-category, lem-weil-linear-scalar-localization-triangulated.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 3 → lem-fd-completion-inverse-scalar-coherence

Put $R_F=\widehat{\mathcal O}_{F,T}$. Framework scalar extension is the strict quotient-tower completion of $K\otimes^L_{R_E}R_L$, whereas PBC scalar extension is ordinary completed-ring change of coefficients. The common integral objects are derived complete by step 1, so the specified map $\chi_{L/E,K}$ is invertible. Define $j_{T,L/E,K}$ as its inverse, followed by rationalization. Naturality of $\chi$ gives naturality on every integral derived arrow. Tensoring the naturality equation with $e\in E$ and adding proves it for every rational arrow. The quotient-map definition of $\chi$ commutes with shifts: shifting the quotient complexes and the product-cone map shifts both its quotient component and its zero component. Hence $j$ respects the exact-functor shift comparisons. For $L=E$, $\chi$ is the completeness unit, so its inverse followed by the multiplication identification gives precisely the normalized identity transition.

Original cited nodes: def-weil-rationalization-karoubi, prop-weil-pbc-scalar-extension, lem-weil-finite-free-completed-scalar-comparison.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 4 → lem-fd-completion-inverse-scalar-coherence

Write $S_{L/E}$ and $P_{L/E}$ for the framework and PBC transitions. The specified framework associator is the ordinary tensor associator conjugated by the completion maps $\chi$; this normalization is explicitly part of the pullback-realization lemma, while PBC uses tensor balancing. Consequently, for $E\subset L\subset M$, their components obey
$$a^p_{M,L,E}\,P_{M/L}(j_{L/E})\,j_{M/L,S_{L/E}K}=j_{M/E}\,J_{T,M}(a^s_{M,L,E}).$$
Indeed substitute $j=\chi^{-1}$ and the conjugated formula for $a^s$: every adjacent $\chi\chi^{-1}$ cancels, using naturality to move a coefficient-change arrow across $\chi$. The remaining map on an ordinary tensor representative is $((x\otimes b)\otimes c)\mapsto x\otimes bc$ on either side. The two unit cases give $x\otimes1\mapsto x$; for four fields both composites give $(((x\otimes b)\otimes c)\otimes d)\mapsto x\otimes bcd$. This proves the unit, three-field cocycle and further associativity equations for the specified maps, and rationalization preserves these equations.

Original cited nodes: lem-weil-scalar-extension-composition, prop-weil-pbc-scalar-extension, lem-weil-finite-free-completed-scalar-comparison, lem-trf-integral-pullback-comparison-realization.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 5 → lem-fd-common-stage-comparison-descent

For objects $(E,K),(F,H)$ and a common field $L$, send $u:S_{L/E}K\to S_{L/F}H$ to
$$\Phi_L(u)=j_{L/F,H}\,J_{T,L}(u)\,j_{L/E,K}^{-1}.$$
This is a bijection of Hom groups, with inverse obtained by applying $J_{T,L}^{-1}$ to $j_{L/F,H}^{-1}v j_{L/E,K}$. For $L\subset M$, transition in either pair category is $u\mapsto a_{M,L,F}\,T_{M/L}(u)\,a_{M,L,E}^{-1}$. Substitution of the equation in step 4 at the source and target, followed by naturality of $j_{M/L}$, gives $\Phi_M(u_M)=(\Phi_Lu)_M$. Thus $\Phi$ and its inverse preserve eventual equality of representatives and define inverse maps on the displayed Hom colimits. They preserve sums. At one common stage the middle factors $j^{-1}j$ cancel in $\Phi(v)\Phi(u)$, giving $\Phi(vu)$, and $\Phi(1)=1$. This defines $J_T$ on arrows and proves it fully faithful.

Original cited nodes: def-weil-algebraically-closed-coefficients, def-weil-pbc-finite-stage-pair-category.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 6 → lem-fd-common-stage-comparison-descent

Every PBC pair $(E,H)$ is the image of $(E,J_{T,E}^{-1}H)$, so $J_T$ is an equivalence. It commutes with finite-stage inclusions by the unit case of step 4. If $\alpha\in\Qlb$, choose a common finite stage containing $\alpha$ and the arrow's stage. The map $\Phi$ is linear over that field, so $\Phi(\alpha u)=\alpha\Phi(u)$; hence $J_T$ is $\Qlb$-linear. The shift compatibility of $j$ identifies the shifted common-stage arrow formulas. A common-stage distinguished triangle is sent, by the conjugating isomorphisms $j$ at its vertices, to the image of its $J_{T,L}$-triangle. Step 2 makes that triangle distinguished. The inverse has the same property. The definition of distinguished triangles therefore makes $J_T$ exact in both directions, with the prescribed shifts and common-stage cones. All constructions used only the objects $(E,K)$ already present.

Original cited nodes: def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category, def-weil-pbc-common-stage-cones.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 7 → lem-fd-whole-tower-integral-pullback-comparison

For a scheme isomorphism $h:U\to T$ choose one flat-term K-flat representative $P$ of a common integral object $K$. In both definitions of completed pullback the strict tower is
$$Q_n=\operatorname{Res}_n h_n^*(P\otimes_{R_E}(A_{E,n})_T),$$
with the actual quotient transition maps. The framework realizes this tower by its product cone, while PBC realizes it by derived inverse limit. Use the realization identification in the integral comparison lemma to identify these models. More explicitly, for a K-injective tower replacement $Q\to I$, the Roos comparison is $\lim I\to\operatorname{Cone}(1-s_I)[-1]$, $z\mapsto(0,z)$. Exact countable products make the cone map from $Q$ to $I$ a quasi-isomorphism. Their zigzag identifies the two realizations of the identity map of the entire tower, naturally for tower arrows; it does not infer equality from equality of individual reductions. The K-injective existence theorem applies to the small ringed tower site, and supplies enough injectives also on the underlying site. The integral well-definedness theorem identifies this construction independently of the K-flat representative, so the natural tower comparison descends to derived morphisms. This constructs an integral comparison $b_{h,E}:J_{U,E}F^s_{h,E}\to F^p_{h,E}J_{T,E}$. The framework preservation theorem and step 1 show both objects lie in the common integral constructible subcategory, so the comparison restricts there.

Original cited nodes: def-weil-derived-pullback-tensor-hom, def-weil-pbc-completed-pullback, lem-trf-integral-pullback-comparison-realization, lem-weil-derived-limit-roos-complex, lem-weil-proetale-countable-products-exact, prop-pur-kinjective-resolutions-exist, lem-pur-integral-operations-preserve-constructible, lem-pc-kflat-resolution, lem-pur-integral-operations-well-defined.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 8 → lem-fd-whole-tower-integral-pullback-comparison

For identity and composable scheme isomorphisms use the simultaneous quotient diagrams and their tower counits specified in the integral realization lemma. On the common finite tower the comparison $b$ is the identity. Thus the two routes around the composition square apply the same termwise module-pullback composition map and the same counit of the whole strict tower. Realizing this equality gives the composition equation for $b$; the identity case uses the identity tower map. For coefficient extension $E\subset L$, the same lemma specifies both iterated identifications by the tower counit, coefficient quotient actions and tensor associators. The map $\chi$ used in step 3 is its specified quotient-map completion unit (zero shifted-product component). PBC uses ordinary tensor balancing and the same quotient actions. Inserting $\chi^{-1}$ on the framework scalar side therefore cancels its completion unit, and both resulting diagrams use the same coefficient action and pullback map on each simultaneous quotient complex. This is an equality of whole derived quotient diagrams, including their counits, before realization. The realization lemma's composition/scalar and successive-extension equations, together with the PBC scalar comparison, give the corresponding mixed squares for $b$ and $j$, as well as their unit and shift compatibilities.

Original cited nodes: lem-trf-integral-pullback-comparison-realization, lem-weil-finite-free-completed-scalar-comparison, prop-weil-pbc-scalar-extension.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 9 → lem-fd-common-stage-comparison-descent

Rationalize $b_{h,E}$: its integral naturality equation remains true after tensoring by $e\in E$ and adding, exactly as in step 3. For a common-stage arrow $u$, both composites in the naturality square for the induced $b_h:J_UF^s_h\to F^p_hJ_T$ are the class of $F^p_{h,L}(\Phi_Lu)$ with the scalar comparison at the source and its inverse at the target. To see this, substitute the pullback arrow formula from the framework definition and $\Phi_L$ from step 5; apply the mixed square of step 8 to move $b$ past each scalar comparison. The adjacent inverse comparison factors then cancel. Eventual equality is respected by step 5, so this gives a natural isomorphism on the common-stage categories. The identity, composition and scalar equations from step 8 survive rationalization and passage to classes. This proves the asserted compatibility at every finite stage and on $\Qlb$.

Original cited nodes: def-weil-derived-pullback-tensor-hom, prop-weil-pbc-scalar-extension, def-weil-algebraically-closed-coefficients, def-weil-pbc-qbar-category.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 10 → lem-fd-frobenius-fixed-pair-comparison

For the final specialization $X=X_0\times_{k_0}k$, a finite affine finite-type cover of $X_0$ base changes to a finite affine cover whose algebras are finite type over $k$: the images of the original generators still generate after tensoring with $k$. Thus $X$ is finite type over the field $k$. A field has only the ideals $0$ and the unit ideal, so $\operatorname{Spec}k$ is Noetherian; the finite-type-over-Noetherian lemma makes $X$ Noetherian, and the finite-type dimension lemma gives finite dimension. The image of the nonzero element $\ell$ of $k$ is a unit in every local ring, since $\ell\ne p$. Finally $g_X$ is the scheme automorphism of the Frobenius definition, with the displayed inverse. Apply step 9 to this isomorphism. Nothing requires it to be a $k$-morphism.

Original cited nodes: def-weil-finite-type-morphism, lem-weil-pbc-finite-type-over-noetherian, lem-kun-dimension-finite-type, def-weil-frobenius-detailed.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

### Original step 11 → lem-fd-frobenius-fixed-pair-comparison

Write $F_s=Lg_X^{*,s}$, $F_p=Lg_X^{*,p}$ and $b:J_XF_s\to F_pJ_X$ for the comparison. Send a Weil pair $(K,\theta:F_sK\xrightarrow{\sim}K)$ to $(J_XK,J_X(\theta)b_K^{-1})$ and an arrow $u$ to $J_X(u)$. Naturality says $F_p(J_Xu)b_K=b_HJ_X(F_su)$. It follows by multiplication by $b_K^{-1}$ that the intertwining equation $u\theta=\theta'F_su$ is equivalent, by full faithfulness of $J_X$, to the intertwining equation for its image. Hence the pair functor is fully faithful. Given a PBC pair $(J_XK,\psi)$, the unique preimage of $\psi b_K$ under the Hom bijection is an isomorphism $\theta:F_sK\to K$ (lift its inverse as well); its image pair is the given pair. Every PBC underlying object has this form by step 6. Thus the functor is essentially surjective too. The construction at a finite stage uses $b_{g_X,E}$, and step 9 identifies it with the common-stage construction, proving the last compatibility clause.

Original cited nodes: def-weil-weil-sheaf-complex.

Source: literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md; Final sentence; explicit comparison of the two coefficient conventions.

The retained proof's step 11 writes a target pair with underlying object JK. For arbitrary underlying H, choose an isomorphism v:JK->H by essential surjectivity, replace psi by v inverse composed with psi composed with F_p(v), then apply that paragraph; v gives the isomorphism back. This is an explicit elaboration of its original final essential-surjectivity sentence, not an added hypothesis.

For the common-stage child, the existing additive descent node may be used directly for functor/compatible-transformation well-definedness. With its comparison b=j inverse it gives exactly the retained step-5 conjugation formula. The remaining Hom bijectivity, exactness, field-linearity and the identification with the actual common-stage pullback are this child's proof obligation; the full calculations above are retained so the specialization is not just a new label for the existing additive statement.

## Validation

The required server delivery dry run passed preflight on the first repaired snapshot (afe2af12869). After correcting the Lean sorry line reference in this report, I run the final dry run again before the push. The checked parent has five proof steps totaling 2161 characters, and all eleven original paragraphs occur verbatim in this report. All five new nodes have empty proof and proof_deps and status unsplit.
