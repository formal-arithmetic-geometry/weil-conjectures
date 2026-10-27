# Q12 stage-1 repair: lem-sfb-root-tower-lisse-morphism-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-lisse-morphism-extension.json`: item, unchanged statement, four assembly steps (2182 characters).
- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-principal-open-continuous-sections.json`: new statement, status unsplit, no Mathlib match after LeanFinder, Loogle, LeanSearch and source grep, including a second phrasing.
- `dag/nodes/sec-six-functors-basics/lem-sfb-sectionwise-open-lisse-hom-descent.json`: new statement, status unsplit, no Mathlib match after the same four search methods and a second phrasing.
- `citations.json`: exact verbatim statement excerpts for every citation in each of the four parent steps.
- `report.md`, `searches.jsonl`, and sandbox-only preparation scripts. No Lean or library file was written, and no compiler or Lake tool was run.

## Attachments

None. I searched `lean/WeilConjectures/` for the blueprint id and for root-tower/lisse-restriction and normal-principal-open terminology. No exact project declaration was found. I also read the supplied project module `lean/Sheaf/Paper/RootTowerLisseMorphismExtension.lean`: `AlgebraicGeometry.ProEtale.rootTower_lisse_restriction_bijective` at line 107 ends in `sorry` and has the eight returned proof steps in its docstring, so it is not an attachment. Its current signature includes the base-change Hom bijection and comparison square. No claim of a finished proof is made.

## WANTED

WANTED: a literature reference for the combined root-limit full-faithfulness statement, beyond the agent expansion of direct-images paragraph (3). The current blueprint paragraph itself only discusses constructible direct images, not root towers. This inherited source limitation is retained; the assembly proof remains `proof_origin.by = agent`.

The new normal-principal-open lemma is an agent consequence of the precise cited Stacks, Bhatt–Scholze and Hemo–Richarz–Scholbach statements, rather than a quotation of a single theorem. The new sectionwise Hom lemma is an agent ringed-site argument, with the full intended argument retained below. No unavailable source is represented as having been read.

## What was wrong and how this repairs the return

The human's batch5 return asks for at least two comparable independent tasks and a parent proof of at most 3000 characters, without losing any of the old argument. The old eight steps contained 5700 characters. The sandbox initially contained only dispatcher marker files, no node files, report or search log; I therefore copied the current repository node as the returned base, retaining its complete statement, original searches, sources, Lean record, review metadata and blueprint ancestry. There was no retained split/report requiring a preliminary dry run. The repository's current proof is exactly the eight-step argument quoted in the return.

The two new tasks separate the algebra/topology/coefficient argument from the ringed-site matrix/descent argument. The first has no lisse modules or Hom conclusion, and does not assume a root tower. The second has no normality, divisor or root-tower hypothesis and instead assumes coefficient-section bijections. Neither can be substituted for the parent without establishing the other one's input. Both are statement-only with empty proof and proof_deps, null proof_origin, status unsplit, and recorded searches. Their statements give usable conclusions, including normalization and naturality, rather than burying proof sketches in statements.

Work allocation: old step 1 applies the already separate geometric task `lem-sfb-snc-root-limit-normal-charts` and computes a localization in the parent assembly. Old steps 2–5 (2572 characters) are the new normal-principal-open task. Old steps 6–7 plus the coefficient/pullback-uniqueness part of step 8 (2495 characters) are the new Hom-descent task. The root-presentation base-change identity and the zero-parameter/empty cases remain short assembly checks in the parent. Every original argument is retained verbatim below, including the actual extension formula, matrix entries, overlap agreement, coefficient identification and comparison of pullbacks. Nothing was shortened away from the work assigned to future workers.

## What could not be finished

The requested stage-1 repair is complete in the sandbox; the two new nodes intentionally remain unsplit for independent workers. The inherited missing nearest blueprint ancestor remains a recorded upstream metadata issue: `python3 tools/blueprint_refs.py ancestor lem-sfb-root-tower-lisse-morphism-extension` prints `None`. I retain it, record the intended anchor `det-thm-sf-ctf-stability-direct-images` paragraph (3) explicitly, and extend the inherited via chain by the item id in both new nodes. I do not alter unrelated ancestors.

## Not duplicates

lem-sfb-normal-principal-open-continuous-sections vs lem-weil-pbc-normal-ring-integrally-closed-total: shared source Tag 034M; the existing lemma only puts integral total fractions back in a normal ring, while the new statement asserts principal-open clopen/component comparison and actual continuous coefficient-section restriction, with its inverse formula and naturality.

lem-sfb-normal-principal-open-continuous-sections vs lem-sfb-normal-generic-continuous-sections: the existing result requires a nonempty integral locally Noetherian base and restriction to its generic fibre; the new result uses an arbitrary normal ring, possibly non-Noetherian, disconnected or zero, and localization at one nonzerodivisor. Neither its hypotheses nor its restricted subscheme are the generic-fibre theorem's.

lem-sfb-normal-principal-open-continuous-sections vs lem-sfb-spectral-clopen-component-homeomorphism: the existing theorem assumes the clopen bijection and only concludes the component homeomorphism. The new theorem must establish its clopen premise from normality and a regular element and then prove the continuous coefficient assertion.

lem-sfb-normal-principal-open-continuous-sections vs lem-sfb-root-tower-lisse-morphism-extension: the new node has no Hom assertion and no root-tower geometry; it supplies the ring sections needed to start matrix descent.

lem-sfb-sectionwise-open-lisse-hom-descent vs lem-sfb-root-tower-lisse-morphism-extension: the new node assumes the affine coefficient-section bijection, whose proof is the parent's main geometric/coefficient input. It applies to arbitrary open immersions and commutative condensed rings; it proves only the formal matrix/descent and conditional pullback part of the parent.

lem-sfb-sectionwise-open-lisse-hom-descent vs lem-sfb-proetale-open-restriction-counit: the existing theorem is open base change for direct image with its counit equation; it gives no extension of lisse morphisms across an open under a coefficient-section hypothesis.

I searched the entire DAG by source Tag 034M and by normal/principal-open/continuous-section and lisse/Hom/restriction concepts, and read the closest candidates above. Blueprint searches were `normal continuous`, `locally free morphism`, `continuous functions`, `lisse restriction`, `principal open continuous`, and `finite locally free restriction`. The generic hits (finite locally free morphisms of schemes, point coefficients and continuous-ring definitions) do not state either new lemma. Both new `blueprint.same_as` fields are therefore empty. The item keeps the same empty same_as.

## Sources and Mathlib evidence

I read the current chapter record `sec-six-functors-basics` and unit record `sk-thm-sf-ctf-stability`, the three permitted blueprint levels in SETUP, and the current main-20261015 direct-images proof. This repair is below the unit level and preserves its constructible-direct-image route. It does not change a chapter, a unit, a target or a Lean statement.

For the first new task I opened Stacks `algebra.tex` at Tag 034M, label `lemma-normal-ring-integrally-closed`, including its proof, and Tag 00EE, label `lemma-disjoint-decomposition`. I read `topology.tex` Tag 0906, label `lemma-spectral-pi0`, and the existing component-homeomorphism node, which supplies the additional clopen criterion (0906 alone does not state that criterion). I read Bhatt–Scholze Lemma 4.2.12, including the continuous-function/component factorization, and Hemo–Richarz–Scholbach Example 3.1 (printed page 6), which explicitly identifies the pulled-back condensed ring with continuous functions on arbitrary scheme objects. The first task's source field identifies 034M and its label and expressly marks the composite result as an agent consequence, not a quotation.

For the second new task I read the blueprint source paragraph (3), the actual lisse and internal-module definitions, the localized-ringed-site definition, and the original parent steps 6–8. Its source is honestly marked as the agent matrix-and-gluing extraction. No claim that the blueprint itself states this general ringed-site theorem is made. No SGA source is used.

All new-node searches were run through the required msearch.py command under Q12 and this item; `searches.jsonl` contains their exact queries, availability, hit counts and digests. The item’s prior searches were preserved. I read all returned hits. The normal-principal-open searches instead returned discrete spectra/localization equivalences, topologically normal Tietze extension and structure-sheaf localization. Those do not give the continuous condensed coefficient assertion on a normal spectrum. The Hom searches instead returned fully faithful forgetful functors, scalar restriction and full pushforward along an open. I opened Mathlib `Algebra/Category/ModuleCat/Sheaf.lean`, including `fullyFaithfulForget`; it is the identity-on-morphism forgetful functor to presheaves, not restriction to the open. It supplies no one-line specialization proving the new hypothesis-dependent full faithfulness. Both new nodes are correctly unsplit, with zero Mathlib leaves, and the search records give these verdicts rather than treating nearby results as matches.

## Review by Q12

I reviewed the repair against delivery-errors B–E, using the statement of every cited node rather than its proof or its title. I checked that each new statement introduces its own rings, field topology, spaces, site, coefficient system and modules, with definition nodes for each specialized notion. Both carry only a statement and source, with no proof steps. The internal inverse formula in the first is a characterization of the asserted inverse, not an inline proof. The second's matrix description similarly characterizes its asserted extension and its independence of choices; proving it is the assigned task.

Parent step 1 uses exactly the site definition's weakly etale objects and `lem-sfb-snc-root-limit-normal-charts`: I read that node's statement, which gives both normality of every weakly etale S-algebra Q and injectivity of multiplication by the same parameter product s. Its hypotheses have precisely the regular separated finite-type characteristic-p base, affine etale chart, strict normal crossing branches, prime-to-p tower and weakly etale A-to-R map of the parent. No Noetherian conclusion is inferred. The principal-open identification is the localization universal property, not a hidden geometric theorem.

Parent step 2 cites the first new node's actual coefficient bijection on any affine pro-etale object over Z, not merely its component or continuous-function clause. Step 1 supplies the normal Q and regular s hypotheses; the finite norm-topological l-adic field is nonarchimedean. This new node's statement explicitly includes the actual pulled-back all-continuous coefficient sheaf, its restriction normalization, and naturality. No switch to locally constant or discrete coefficients occurs.

Parent step 3 cites the second new node's full Hom formula. It requires only that j be open, C_E be a commutative condensed ring, the modules be lisse, and all affine chart section maps be bijective. These are the parent's assumptions and step 2. The new node's statement, not an imagined stronger result about extending objects, supplies precisely this Hom bijection, including zero ranks. Its proof obligation is the complete common-cover, finite-matrix and overlap-descent argument saved below. Neither a clause of the parent nor a new theorem equivalent to the whole parent has been substituted for the argument.

Parent step 4 cites the cartesian-coefficients node for the canonical coefficient identification and the second new node's explicit conditional pullback compatibility formula. I read the cartesian statement, including its untwisted coefficient identification and exact inverse-image description; the parent uses its finite E coefficient case, not a Tate twist or finite reduction. The new node explicitly assumes the coefficient-section hypothesis again on X'; it does not falsely assert that this hypothesis survives every base change automatically. In this application the root presentation tensors to the root presentation over each affine chart of U', so repeating steps 1–3 proves that hypothesis. For an arbitrary affine object over the base-changed tower, its inverse images of the affine base charts have affine refinements. The coefficient sheaf axiom and uniqueness glue the local section extensions, so the all-affine coefficient-section hypothesis follows, not only its version over a single base chart. The common local free bases pull back to free bases. The conditional comparison then identifies the two inverse Hom maps under the canonical composition comparisons, exactly as in the original uniqueness argument. Affine refinements and sheaf descent handle a nonaffine U'. This argument uses no finite-type property of Q or of U'.

I also checked the statements of the old proof's algebra/topology/coefficient inputs, which remain future proof inputs for the first new task: total-fraction integral closure says precisely that the integral idempotent returns to Q, the clopen/idempotent statement gives the actual inverse-image correspondence D(e), affine qcqs and qcqs spectral provide the hypotheses of the component theorem, and the canonical realization statement applies on any scheme (not just Noetherian ones). This prevents a future worker from reusing the Noetherian generic-fibre sibling in place of the needed result.

Small cases: Q=0 gives two empty spectra and singleton function rings; s=1 gives the identity; a product of normal domains with a nonzero element in each factor gives the same componentwise calculation; a non-Noetherian normal union of tame-root domains is within the first task's hypotheses. The nonzerodivisor assumption cannot be dropped: Q=k×k with s=(1,0) removes one component and loses its functions. Normality is also substantive: Q=k[x,y]/(xy), s=x+y, is connected but D(s) has two disconnected branches, so the E-valued function taking 0 and 1 on those branches has no extension. For the second task j=id works for every coefficient ring, either rank zero gives an empty matrix and a unique map, and the empty scheme has a singleton Hom set. For a common trivializing cover, overlaps are refined by affine opens, never assumed affine because X is separated. In different bases the two local extensions agree because their difference has coefficient entries restricting to zero, and restriction is injective. The base-change condition in the new statement is intentionally conditional and is verified afresh in the root-tower application.

The return required a structural repair, and I made it: two comparable new independent proof tasks, with their original arguments retained, and a four-step parent assembly under the size limit. I did not merely summarize the 5700-character proof. The parent's statement and all eight mathematical claims are unchanged. No STATEMENT-DISPUTED correction was necessary.

## Preserved proof and assignment of all eight original steps

The following are copied verbatim from the current returned proof, together with their original cited nodes. They are handoff material in this report; the new JSON nodes deliberately have no proof. Workers on the first task use steps 2–5; workers on the second use steps 6–8's module and uniqueness parts. Step 1's geometry is already its own cited task, while the parent retains its localization setup and the presentation/edge-case checks from step 8.

### Original step 1

Write $B=\operatorname{Spec}A$, $T=\operatorname{Spec}S$ and $s=t_1\cdots t_r\in S$. An affine object $W=\operatorname{Spec}Q\to T$ of the small pro-etale site is weakly etale, by [def-weil-pbc-proetale-site]. Apply [lem-sfb-snc-root-limit-normal-charts] to the given chart and $A\to R$, and to $S\to Q$. It gives that $Q$ is normal and multiplication by $s$ on $Q$ is injective. The open $W^\circ=W\times_T T^\circ$ is $\operatorname{Spec}Q[1/s]$, directly by the localization universal property: a map factors through this inverse image exactly when the image of $s$ is invertible. No Noetherian assertion about $Q$ or $S$ is used.

Cited statements: lem-sfb-snc-root-limit-normal-charts, def-weil-pbc-proetale-site

### Original step 2

The localization map $Q\to Q[1/s]$ is injective: a fraction $q/1$ is zero only if $s^Nq=0$, and repeated injectivity of multiplication by $s$ gives $q=0$. Since $s$ is a nonzerodivisor, $Q[1/s]$ embeds into the total ring of fractions of $Q$. Every idempotent $e$ in $Q[1/s]$ is integral over $Q$, satisfying $e^2-e=0$. By [lem-weil-pbc-normal-ring-integrally-closed-total], $e$ is in $Q$; injectivity gives the idempotent equation there and uniqueness. Thus idempotents restrict bijectively. By [lem-weil-pbc-spec-clopen-idempotent], this is precisely the inverse-image bijection $\operatorname{Clop}(W)\to\operatorname{Clop}(W^\circ)$, because $D(e)$ pulls back to $D(e/1)$. This also works for $Q=0$, when both spectra are empty.

Cited statements: lem-weil-pbc-normal-ring-integrally-closed-total, lem-weil-pbc-spec-clopen-idempotent

### Original step 3

Both $W$ and $W^\circ$ are affine, hence qcqs by [lem-weil-pbc-affine-scheme-qcqs], and spectral by [lem-weil-pbc-qcqs-scheme-spectral]. Apply [lem-sfb-spectral-clopen-component-homeomorphism] to their inclusion and the clopen bijection of step 2. It gives the normalized homeomorphism $h_W:\pi_0(W^\circ)\xrightarrow{\sim}\pi_0(W)$ with $h_Wq_{W^\circ}=q_Wj_W$, where each $q$ is the quotient map to connected components. This includes empty $W$.

Cited statements: lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-qcqs-scheme-spectral, lem-sfb-spectral-clopen-component-homeomorphism

### Original step 4

The norm topology of $E$ is totally disconnected: ultrametric balls are clopen and separate any two distinct points. Hence a continuous function from a connected space to $E$ is constant. For $a:|W^\circ|\to E$, write $a=\bar a q_{W^\circ}$. The quotient topology makes $\bar a$ continuous. Define $\widetilde a=\bar a h_W^{-1}q_W$. It is continuous and restricts to $a$. Conversely, factor any continuous function on $W$ through $q_W$ to see that this formula recovers it from its restriction. Thus actual restriction $C(|W|,E)\to C(|W^\circ|,E)$ is a bijection. It is a ring homomorphism by pointwise operations. For any $T$-map $v:Z\to W$ between affine site objects, restriction commutes with precomposition, so uniqueness gives $\widetilde{a\circ v^\circ}=\widetilde a\circ v$.

Cited statements: none (elementary)

### Original step 5

Use [lem-weil-pbc-condensed-field-continuous-realization] for the totally disconnected normed field $E$. Its canonical ring-sheaf isomorphism identifies the actual pulled-back continuous coefficient sections on $W$ with $C(|W|,E)$ and those on $W^\circ$ with $C(|W^\circ|,E)$. The normalization on profinite test functions identifies their restriction with the restriction of step 4. Consequently $\Gamma(W,C_{E,T})\to\Gamma(W^\circ,C_{E,T^\circ})$ is bijective for every affine site object, naturally in that object. This is the all-continuous coefficient ring, not its discrete or locally constant substitute.

Cited statements: lem-weil-pbc-condensed-field-continuous-realization

### Original step 6

Choose a common pro-etale trivializing cover of $\mathcal N,\mathcal N'$ using [def-sfb-lisse-coefficient-module]: take fibre products of their trivializing covers and refine by affine opens. The site covering rule of [def-weil-pbc-proetale-site] permits these refinements. On a member $W$ the modules are finite free of ranks $a,b$. By [sk-def-sfb-module-objects], a linear sheaf map is determined by the images of the $a$ standard basis sections; each is a $b$-tuple of coefficient sections. Conversely a $b\times a$ matrix of sections defines a linear map on every object over $W$ by restricting its entries and multiplying vectors. For a morphism on $T^\circ$, extend its matrix entries uniquely by step 5, obtaining a linear sheaf map on each $W$. This description also proves local uniqueness. Empty matrices handle either rank zero.

Cited statements: def-sfb-lisse-coefficient-module, def-weil-pbc-proetale-site, sk-def-sfb-module-objects

### Original step 7

On an overlap of two trivializing members, refine by affine opens. The two constructed maps have the same restriction to the punctured overlap, namely the given morphism. In either set of restricted bases their difference has zero matrix after restriction. Step 5 on each affine refinement forces every entry of that difference to vanish, so the maps agree. The sheaf gluing axiom, applied on every test object to the images of sections, glues them uniquely to a module morphism on $T$; additivity, scalar compatibility and naturality hold because they hold on this cover. The same local uniqueness shows that any two global maps with the same restriction agree. This proves surjectivity and injectivity of the required Hom restriction.

Cited statements: none (elementary)

### Original step 8

For a pro-etale base change $U'\to U$, put $T'=T\times_U U'$; the root-algebra presentation base changes to the stated presentation over $U'$, since tensor products commute with the displayed generators, relations and filtered colimit. Coefficients identify under pullback by [sk-prop-sfb-cartesian-coefficients]. Pullback carries the restriction of a map to the restriction of its pullback by the fibre-product projection equations. It carries local free bases to local free bases. Therefore the pullback of the unique extension and the extension of the pulled-back morphism restrict to the same map on $T'^\circ$; injectivity already proved for the new chart makes them equal. This is the requested base-change naturality. If $r=0$, $s=1$, $j$ is the identity and all formulas reduce to the identity. If the chart is empty, all Hom sets are singletons. The proof constructs only morphisms between the supplied modules.

Cited statements: sk-prop-sfb-cartesian-coefficients

## Validation

The first required remote dry run exited 0 and printed OK (not pushed), commit 707d66ad307, with preflight passed. After that pass I clarified the nonaffine-base coefficient-section gluing in assembly step 4; a final dry run is required on this exact version before pushing. Local JSON checks confirmed the original item statement is unchanged, both new nodes are unsplit with no proof steps, the parent is below 3000 characters and no step exceeds 2000 characters, and every citations.json excerpt occurs verbatim in the cited statement. No Lean, Lake or local preflight/DAG-review script was run.
