# Worker report — Q103

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-finding-opens.json`: existing statement node, split; statement unchanged, proof replaced by a short assembly.
- `dag/nodes/sec-trace-formula/lem-trf-relation-incidence-open-model.json`: new statement node, unsplit; no Mathlib match. The incidence morphism, its open image, its fppf factor, and its natural local representing property.
- `dag/nodes/sec-trace-formula/lem-trf-fppf-local-open-subfunctor-descent.json`: new statement node, unsplit; no Mathlib match. General descent of an open model from an fppf-locally surjective scheme presentation of a sheaf.
- `citations.json`: verbatim statement excerpts for all citations in the four assembly steps.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact blueprint tag, finding_opens, restricted quotient, saturation, incidence/quotient and fppf/open-subfunctor concepts. No project declaration states this result. Read `lean/Sheaf/AlgebraicGeometry/EtaleRelationFindingOpens.lean`: `AlgebraicGeometry.AlgebraicSpace.etale_relation_finding_opens` ends with `sorry`, so it is not an attachment. Its two coequalizers and sheafification universal properties encode precisely the two quotient sheaves. No Lean file was changed and no compiler was run.

## WANTED

None. All source arguments are available in the local Stacks sources.

## Repair and baseline

The dispatched sandbox contained only `.brief*` markers: there was no node, report, citations file or search log to resume. The required initial dry run exited with `FAILED: no node files under .../dag/nodes/`. I copied the current repository item as the baseline, preserving all historical search, Lean, audit, review and blueprint fields. Its eight proof steps match the returned 385/588/917/671/806/551/619/1083-character argument. There is consequently no retained alternate split to rebase. The delivery tool constructs the commit against current server main.

The sole return asks to distribute the 5620-character proof into at least two comparable statement-only nodes, without losing any argument, retaining the item statement and making its assembly at most 3000 characters. I extracted old steps 3–5 into the incidence-model node and old steps 6–8 into the general open-subfunctor descent node. These are independent tasks: the first proves a concrete local model over U and never handles arbitrary maps to F; the second assumes a local model and proves a general sheaf descent theorem without any equivalence relation or quotient. Neither restates the entire item. Their source workloads have respectively 2394 and 2253 characters. Both new nodes have `status: unsplit`, empty `proof` and `proof_deps`, and null `proof_origin`. The complete old argument is retained below for their future workers, rather than inserted as a forbidden proof sketch into either statement.

Assembly steps 1 and 2 retain old steps 1 and 2, adding explicit sheafification and site-axiom citations. Step 3 applies the incidence model with v the identity of U. Step 4 checks local surjectivity of the quotient presentation and applies general descent. The assembly is 2159 characters. Every proof step is under 2000 characters. The statement is byte-for-byte unchanged. I corrected stale `source.place` metadata: relation restriction is 02V8, descent of opens is 03N0, and 023Q concerns representable-functor descent; 02VH/02W2 were not the right labels for the assertions claimed there.

## Sources and route

Read `GOAL.md`, the three blueprint levels in `SETUP.md`, the stage-1 brief, stage document, worker role and delivery-errors B–E. Read the chapter `sec-trace-formula` and unit `sk-i-curve-zero`; this repair stays in the existing scheme-quotient infrastructure below that unit and changes no chapter or unit statement or route. The nearest blueprint ancestor is `lem-trf-local-term-locality`. New nodes retain its exact ancestry and add this item at the front of `via`; their `from.place` identifies the affine-summand open-embedding support and the relevant paragraphs of Tag 02WU. No SGA source is used.

For the item and incidence-model node, read `literature/stacks-project/spaces.tex`, Tag 02WU, label `lemma-finding-opens`, including the complete proof and displayed diagram; also `groupoids.tex`, Tag 02V8 `lemma-restrict-relation` and Tag 045Z `lemma-quotient-pre-equivalence-relation-restrict`. In the source, W is t(s^{-1}(g(U'))); in the new node it is the image of E=U'×_U R. These are the same set: the projection E→s^{-1}(g(U')) is surjective, because a scheme fibre product has a point above a pair of points with the same image (after a common residue-field extension). The factor E→W packages the two successive fppf morphisms in the source diagram. The source's 'g is surjective' at that diagram means onto its image W^1, not onto U. The new statement explicitly excludes any added surjectivity hypothesis on g.

For the descent node, read Tag 02WU's choice of local representatives, compatibility on overlaps, descent, and final two directions of the representing property; read `descent.tex`, Tag 03N0 `lemma-open-fpqc-covering` and Tag 023Q `lemma-fpqc-universal-effective-epimorphisms`; read `topologies.tex`, Tag 022C `lemma-zariski-etale-smooth-syntomic-fppf-fpqc` with its affine finite-subcover proof. The generic statement merely replaces the quotient presentation U→F by its explicit local lifting property; no part of this descent argument uses that F is an algebraic space.

## Review by Q103

I opened the item, both new statements, and the statements of every node cited by the assembly. I also reread every dependency statement in the original eight steps, so the work allocation below does not silently inherit a bad citation.

Step 1 uses `def-pc-fibre-product`, whose universal property identifies R'(T) with triples of endpoints and an R-arrow, and `def-weil-pbc-sheafification`, whose universal property supplies the canonical map from quotient classes. Reflexivity, symmetry, transitivity and uniqueness of the arrow with specified endpoints are a direct calculation from the item's equivalence relation hypothesis; no etaleness is used. This remains elementary.

Step 2 uses `lem-weil-pbc-site-sheafification-sections-local`, which actually states the local representatives needed, and `lem-trf-etale-relation-kernel-pair`, which actually identifies h_R with h_U×_F h_U for a monomorphic equivalence relation with no etaleness hypothesis. The item's j is precisely such a monomorphism on functors. A common refinement of covers is allowed by the site axioms in `def-weil-pbc-sites-and-cohomology`, whose equalizer sheaf condition gives separation. The R-arrow therefore yields an R'-arrow and equality of the local quotient sections. It would be incorrect to use `lem-trf-etale-relation-restriction-quotient` here: that node assumes g and both legs etale. I retained the existing valid kernel-pair route instead.

Step 3 uses only the statement of `lem-trf-relation-incidence-open-model`: all of its schemes, relation, flatness and lfp assumptions are those of the item, and its extra sectionwise injectivity assumption was proved in step 2. Its explicit local-model conclusion includes v=1_U, not just existence of an open set. This provides the exact h_U-base-change model the next node requires. No argument from a dependency proof is used as if it were its statement.

Step 4 again uses the local-representative assertion of `lem-weil-pbc-site-sheafification-sections-local`. Choosing an element of each nonempty quotient class is allowed by classical choice and supplies actual maps to U on a common covering; no global section or global surjectivity of g is asserted. For `lem-trf-fppf-local-open-subfunctor-descent`, F and F' are already fppf sheaves by their definitions, alpha is sectionwise injective by step 2, q is locally surjective by this argument, and W has the stipulated isomorphism by step 3. Its conclusion gives the isomorphism over h_T on all test schemes, hence the entire item conclusion. citations.json contains literal statement excerpts for every cited node of these four steps, checked by substring comparison.

For the incidence node I checked the hypotheses and both directions of the local model separately. Projection E→R is the base change of g, not of s; its composite with t is flat and lfp using exactly the old base-change and composition dependency statements. `lem-weil-pbc-qcqs-morphism-permanence` supplies lfp base change in clause (3) without a qcqs-base restriction. `lem-weil-pbc-flat-lfp-open` then makes W open. The factor through W has unchanged local rings and local finite presentations; these are the actual notions in `def-weil-flat-morphism` and `def-sbc-locally-finite-presentation`. For v:V→U, the projection D→W_V is the base change of E→W, so the statements of `lem-weil-pbc-surjective-base-change`, `lem-weil-pbc-flat-morphism-base-change`, and the permanence node really give a one-member fppf cover. On D the R-arrow identifies the two F-sections; injectivity of alpha gives agreement on overlaps, and F' being a sheaf glues the lift. Conversely a local U'-representative plus the kernel-pair statement gives an E-point, forcing the image into W_V; factoring through an open is a literal restriction of the topological and sheaf maps. These constructions are unique, hence commute with arbitrary base changes. No affine-overlap hypothesis is used.

For the descent node I checked that compatibility of the inverse-image opens follows from both being models of the same subfunctor on an overlap; no claim about an arbitrary isomorphism of schemes identifying their images is made without its map to that overlap. Its mono hypothesis gives the required uniqueness. To pass to fpqc, the actual statement of `def-weil-pbc-fpqc-covering` asks for finitely many affine source opens over each affine target open. The proof of 022C supplies them using openness of the fppf maps and quasi-compactness of that affine, exactly the facts supplied by `lem-weil-pbc-flat-lfp-open` and `lem-weil-pbc-affine-scheme-qcqs`. Thus `lem-weil-pbc-open-subscheme-fpqc-descent` applies to genuinely equal-overlap opens. `lem-weil-pbc-fpqc-representable-descent` states existence AND uniqueness of gluing morphisms to arbitrary target schemes; it supplies the representable sheaf condition, not just full faithfulness of Yoneda. Local sections of G then glue uniquely because G is a sheaf and alpha is injective. On every Z→T, pull back the covering to obtain both implications of the representing property. This proves naturality, independence of choices and base-change compatibility, rather than asserting them without an argument.

Small-case checks: U'=empty gives E=W=empty and the initial restricted quotient; g=identity gives W=U, since the equivalence relation has diagonal arrows, and the local model is the full representable functor. For the diagonal relation and a nonsurjective open immersion g, W is exactly the image of g; for a surjective flat-lfp g it is U. The generic descent statement gives empty opens for G initial and full opens for alpha an isomorphism. The empty test scheme allows an empty covering: both sheaves have a singleton value there, and the unique open and model are empty. No nonemptiness, finite-cover, separatedness, quasi-compactness of U, or quasi-separatedness of an overlap is introduced. Nonreduced schemes cause no problem because factorization is only through open subschemes.

B1–B7: both new statements introduce all their objects and define the relation, canonical map and local lifting condition inline; their mathematical notions cite the exact definition nodes they use. They contain assertions only, no proof instructions or hidden proof. The node fields have the required empty proof data, inherited chapter/unit, full source tags and labels, and blueprint data. JSON uses ordinary TeX escapes once in the decoded strings. Both have three search kinds (plus LeanFinder) run by the mandated command; LeanSearch's HTTP rate limit is recorded as unavailable, not a negative match. Searches are recorded with their exact tool and query, including unsuccessful Loogle patterns. The close candidates were read: Mathlib `Sites/Representability.lean` assumes already relatively representable open immersions and a Zariski cover; `Morphisms/FlatDescent.lean` lines 131–155 proves a property of an existing scheme morphism, not existence of a scheme model for a sheaf. Neither specializes in one line to these nodes. No new definition or hollow object is introduced. The comparisons below explain the same-tag candidates; no dependency cycle is created because neither new statement depends on this item or any quotient representability result above it.

The repair changes the distribution of work, not just its prose length. All old arguments appear verbatim below, assigned to the new tasks. No proof was discarded, and the two tasks are of comparable scope. The only correction beyond distribution was explicit citation of the site and sheafification universal properties and the stale source-tag metadata noted above.

## Searches and duplicate search record

Searched the whole DAG for 02WU, 03N0, 045Z, saturation, open subfunctor, representability/descent and incidence; read the closest candidate statements rather than inferring their content from titles. Ran `tools/blueprint_refs.py ancestor` and full-blueprint searches for finding opens, representability local, saturation, incidence, open immersion, open subfunctor, fppf sheaf, 02WU and 03N0. The returned matches are special Picard/Hilbert functors, space-specific statements, or unrelated uses of 'coincidence'; none is either new assertion. Searched the project source for the exact item tag and concepts as recorded under Attachments.

The following command results are retained in searches.jsonl; no search is inferred or fabricated:

### lem-trf-fppf-local-open-subfunctor-descent

- `grep` query `open.*subfunctor|subfunctor.*open|fppf.*representab|representab.*fppf|open.*fpqc`: Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean; Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean; Mathlib/AlgebraicGeometry/Morphisms/FlatMono.lean. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leansearch` query `Representability by open subschemes descends from an fppf covering for a monomorphism of sheaves of sets`: service unavailable: {"error":"Rate limit exceeded: 60 per 1 minute"}. Verdict: unavailable.
- `loogle` query `CategoryTheory.MorphismProperty.IsRepresentable, AlgebraicGeometry.IsOpenImmersion`: loogle: unknown identifier 'CategoryTheory.MorphismProperty.IsRepresentable'. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leanfinder` query `A monomorphism of fppf sheaves is representable by open immersions if its pullback to a scheme locally surjecting onto the target sheaf is an open subscheme`: AlgebraicGeometry.instMonoObjWalkingSpanCompOverSchemeTopMorphismPropertySpanOverForgetForgetForgetNoneWalkingPairSomeMapInitOfIsOpenImmersionLeftDiscretePUnit; AlgebraicGeometry.Scheme.LocalRepresentability.isRepresentable; AlgebraicGeometry.instMonoObjWalkingSpanCompSchemeSpanForgetNoneWalkingPairSomeMapInitOfIsOpenImmersion; AlgebraicGeometry.Scheme.LocalRepresentability.representableBy; AlgebraicGeometry.IsOpenImmersion.le_monomorphisms; AlgebraicGeometry.IsOpenImmersion.mono; AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono; AlgebraicGeometry.Scheme.pullback_map_isOpenImmersion. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `grep` query `LocalRepresentability|local.*surject|open.*immersion.*descent`: Mathlib/AlgebraicGeometry/Sites/Fpqc.lean; Mathlib/AlgebraicGeometry/Sites/Representability.lean; Mathlib/AlgebraicGeometry/Sites/Representability.lean; Mathlib/AlgebraicGeometry/Sites/Representability.lean; Mathlib/AlgebraicGeometry/Sites/Representability.lean; Mathlib/AlgebraicGeometry/Sites/Representability.lean. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `loogle` query `AlgebraicGeometry.IsOpenImmersion, CategoryTheory.MorphismProperty.relative`: none. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leanfinder` query `Compatible open subschemes representing a subsheaf on an fppf covering descend and represent that subsheaf globally, using descent of opens and the sheaf gluing condition`: AlgebraicGeometry.Scheme.OpenCover.ext_elem; TopCat.Presheaf.generateEquivalenceOpensLe_inverse'; AlgebraicGeometry.Scheme.LocalRepresentability.glueData_openCover_map; AlgebraicGeometry.Scheme.subcanonical_zariskiTopology; AlgebraicGeometry.ExistsHomHomCompEqCompAux.𝒰S; AlgebraicGeometry.Scheme.LocalRepresentability.glueData_J; TopCat.Presheaf.generateEquivalenceOpensLe; SheafOfModules.QuasicoherentData.coversTop. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.

### lem-trf-relation-incidence-open-model

- `grep` query `quotient.*relation|relation.*quotient|saturat.*open|open.*saturat`: none. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leansearch` query `The incidence image of a flat locally finitely presented relation represents the pullback to its atlas of a restricted quotient sheaf`: service unavailable: {"error":"Rate limit exceeded: 60 per 1 minute"}. Verdict: unavailable.
- `loogle` query `AlgebraicGeometry.IsOpenImmersion, AlgebraicGeometry.Flat`: AlgebraicGeometry.Flat.instRespectsSchemeIsOpenImmersion; AlgebraicGeometry.Flat.instOfIsOpenImmersion; AlgebraicGeometry.descendsAlong_isOpenImmersion_surjective_inf_flat_inf_quasicompact'; AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leanfinder` query `For a flat locally finitely presented equivalence relation R on U and a flat locally finitely presented map g from U prime to U, the open image of U prime times U R represents the restricted quotient sheaf after pullback to U`: AlgebraicGeometry.Scheme.LocalRepresentability.glueData_V; AlgebraicGeometry.Scheme.LocalRepresentability.glueData_t'; AlgebraicGeometry.Scheme.LocalRepresentability.glueData_f; AlgebraicGeometry.PresheafedSpace.GlueData.pullback_base; AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'; AlgebraicGeometry.Scheme.LocalRepresentability.glueData_t; AlgebraicGeometry.Scheme.LocalRepresentability.comp_toGlued_eq; AlgebraicGeometry.Scheme.Hom.opensRange_pullbackSnd. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.
- `leanfinder` query `The saturation of the image of a flat locally finitely presented scheme morphism under an equivalence relation is open and represents the inverse image of the restricted quotient sheaf`: AlgebraicGeometry.Flat.instOfIsOpenImmersion; AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono; AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_glueDataObjMap; AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.imageBasicOpen_image_open; Algebra.isOpen_smoothLocus; AlgebraicGeometry.UniversallyOpen.of_flat; AlgebraicGeometry.Scheme.IdealSheafData.opensRange_glueDataObjMap; AlgebraicGeometry.Flat.isQuotientMap_of_surjective. Verdict: no match: scheme morphism properties and Zariski gluing do not state this fppf quotient or sheaf descent assertion.

## Not duplicates

lem-trf-fppf-local-open-subfunctor-descent vs lem-coef-infinity-cartesian-initial-boundary-lift: the existing node is a theorem on boundary lifts in cartesian fibrations of infinity-categories, sourced to Kerodon Tag 02WU, Proposition 7.1.5.19(2). This new node concerns schemes and fppf sheaves, sourced to Stacks Tag 02WU, lemma-finding-opens. These are different tag systems and different mathematical statements.

lem-trf-relation-incidence-open-model vs lem-coef-infinity-cartesian-initial-boundary-lift: the existing node is a theorem on boundary lifts in cartesian fibrations of infinity-categories, sourced to Kerodon Tag 02WU, Proposition 7.1.5.19(2). This new node concerns schemes and fppf sheaves, sourced to Stacks Tag 02WU, lemma-finding-opens. These are different tag systems and different mathematical statements.

lem-trf-fppf-local-open-subfunctor-descent vs lem-galois-fpqc-descending-types-morphisms: the existing statement is 'Reduction of effective fpqc descent for a type of morphisms to flat surjective morphisms of affines (Stacks 02W3, one-member coverings)', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-pd-descended-overlap-glue-data: the existing statement concerns overlap-transition scheme gluing data; the new node concerns an open subfunctor of an arbitrary sheaf and its fppf-local scheme presentation.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-etale-covering-affine-refinement: the existing statement is 'An etale covering of an affine scheme is refined by a finite family of affine opens of its members', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-etale-open-fpqc-descent: the existing statement descends opens in an already given etale scheme; the new node constructs the representing open for a morphism of arbitrary fppf sheaves.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-finite-locally-free-degree-etale-descent: the existing statement is 'Finite locally free of degree d descends along etale coverings (Stacks 02VO)', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-fpqc-affine-standard-refinement: the existing statement is 'Affine fpqc coverings admit finite standard refinements', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-fpqc-detects-openness: the existing statement only detects openness of a subset from fpqc inverse images; the new node must identify a subsheaf with the represented open after descent.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-fpqc-finer-than-etale: the existing statement is 'Every small etale covering family is an fpqc covering', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-weil-pbc-open-subscheme-fpqc-descent: the existing statement descends given compatible opens; the new node also derives overlap compatibility from sheaf pullbacks and proves the descended open represents the sheaf pullback on every test scheme.

lem-trf-fppf-local-open-subfunctor-descent vs lem-sfb-fpqc-labelled-clopen-descent: the existing statement concerns labelled open-and-closed partitions on an fpqc cover; the new node allows opens that are not closed and identifies a sheaf fibre product.

lem-trf-fppf-local-open-subfunctor-descent vs lem-trf-etale-affine-quotient-representable: the existing statement is 'Representability facts for an affine etale-relation quotient', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-fppf-local-open-subfunctor-descent vs lem-trf-etale-relation-finding-opens: the existing node is the whole quotient open-immersion theorem being repaired; this new node is only one proper subargument, with the remaining hypotheses and work isolated separately.

lem-trf-relation-incidence-open-model vs lem-trf-etale-affine-quotient-representable: the existing statement is 'Representability facts for an affine etale-relation quotient', with its own geometric hypotheses and conclusion; it does not state the explicit incidence-model assertion or the arbitrary-fppf-sheaf local-open-model criterion.

lem-trf-relation-incidence-open-model vs lem-trf-etale-relation-finding-opens: the existing node is the whole quotient open-immersion theorem being repaired; this new node is only one proper subargument, with the remaining hypotheses and work isolated separately.

## Preserved arguments and exact work allocation

These are the returned proof steps, verbatim, retained as source material for the future workers. They are not proof fields of the statement-only nodes.

### Old step 1 — retained in item assembly

For every $T$, a pair $(u'_1,u'_2)$ belongs to $R'(T)$ exactly when $(g u'_1,g u'_2)$ belongs to $R(T)$, by the fibre-product definition [def-pc-fibre-product]. Pullback of an equivalence relation along a function is reflexive, symmetric and transitive, and $R'(T)\to U'(T)^2$ is injective. Thus $R'$ is an equivalence relation, so both presheaf quotients in the statement are defined.

Original dependency statements to reuse: def-pc-fibre-product.

### Old step 2 — retained in item assembly

The map $F'\to F$ is injective. Indeed, locally on an fppf covering any two sections $b,c\in F'(V)$ lift to $u',v'\in U'(V)$, using [lem-weil-pbc-site-sheafification-sections-local] for the quotient presheaf, choosing representatives of its quotient classes. If their images in $F$ agree, [lem-trf-etale-relation-kernel-pair] gives a unique $r:V\to R$ with $s r=g u'$ and $t r=g v'$. Hence $(u',r,v')$ belongs to $R'(V)$, so $b=c$ locally and therefore globally by the sheaf condition. The kernel-pair node assumes only a monomorphic equivalence relation, not etaleness, and applies here.

Original dependency statements to reuse: lem-weil-pbc-site-sheafification-sections-local, lem-trf-etale-relation-kernel-pair.

### Old step 3 — lem-trf-relation-incidence-open-model

Put $E=U'\times_{g,U,s}R$ and let $p:E\to U$ be $t$ after projection to $R$. That projection is the base change of $g$, hence flat by [lem-weil-pbc-flat-morphism-base-change] and locally of finite presentation by clause (3) of [lem-weil-pbc-qcqs-morphism-permanence]. Composition with $t$ preserves these two properties by [lem-pc-flat-compose] and [lem-sbc-locally-finite-presentation-composition]. Thus $W=p(E)$ is open in $U$ by [lem-weil-pbc-flat-lfp-open]. The map $p$ factors through this open as a surjection $\bar p:E\to W$. This factor is still flat and locally of finite presentation: its stalk maps are those of $p$, and an affine presentation $B=A[x_1,\ldots,x_n]/(f_1,\ldots,f_m)$ remains such a presentation over a smaller basic target open: $B_a=A_a[x_1,\ldots,x_n]/(f_1,\ldots,f_m)$ [def-weil-flat-morphism, def-sbc-locally-finite-presentation]. There is no assumption that $g$ is surjective onto $U$.

Original dependency statements to reuse: lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence, lem-pc-flat-compose, lem-sbc-locally-finite-presentation-composition, lem-weil-pbc-flat-lfp-open, def-weil-flat-morphism, def-sbc-locally-finite-presentation.

### Old step 4 — lem-trf-relation-incidence-open-model

Fix $v:V\to U$, and set $W_V=v^{-1}(W)$, with its open subscheme structure. The map $D=E\times_W W_V\to W_V$ is surjective by [lem-weil-pbc-surjective-base-change], flat by [lem-weil-pbc-flat-morphism-base-change], and locally of finite presentation by [lem-weil-pbc-qcqs-morphism-permanence](3). It is therefore a one-member fppf covering [def-pc-fppf-site]. On $D$, the maps to $U'$ and $R$ supplied by $E$ show that the section of $F$ induced by $v$ is the image of a section of $F'$. On $D\times_{W_V}D$ these two sections of $F'$ agree, since their images in $F$ agree and step 2 proved injectivity. They glue uniquely, giving a morphism $h_{W_V}\to h_V\times_F F'$.

Original dependency statements to reuse: lem-weil-pbc-surjective-base-change, lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence, def-pc-fppf-site.

### Old step 5 — lem-trf-relation-incidence-open-model

Conversely, let $z:Z\to V$ and $b\in F'(Z)$ have the same image in $F(Z)$ as $v z$. By [lem-weil-pbc-site-sheafification-sections-local], on an fppf cover $\{Z_k\to Z\}$ the section $b$ is represented by $b_k:Z_k\to U'$. Equality in $F$ and [lem-trf-etale-relation-kernel-pair] give $r_k:Z_k\to R$ with $s r_k=g b_k$ and $t r_k=v z|_{Z_k}$. Thus $(b_k,r_k)$ gives a map $Z_k\to E$, so $v z(Z_k)\subset W$. Joint surjectivity of this covering implies $z(Z)\subset W_V$. A morphism whose image lies in an open factors uniquely through the open subscheme, by restriction of its continuous map and structure-sheaf map [def-weil-open-immersion]. This produces the inverse to step 4: uniqueness follows from step 2, and both constructions commute with restriction. Hence $h_V\times_F F'\cong h_{W_V}$ over $h_V$.

Original dependency statements to reuse: lem-weil-pbc-site-sheafification-sections-local, lem-trf-etale-relation-kernel-pair, def-pc-fppf-site, def-weil-open-immersion.

### Old step 6 — lem-trf-fppf-local-open-subfunctor-descent

For an arbitrary $a:h_T\to F$, [lem-weil-pbc-site-sheafification-sections-local] applied to $U(-)/R(-)$ gives an fppf cover $\{\varphi_i:T_i\to T\}$ and representatives $a_i:T_i\to U$. Put $W_i=a_i^{-1}(W)$. Steps 4 and 5 identify $h_{T_i}\times_F F'$ with $h_{W_i}$. On $T_i\times_TT_j$, the two pullback open subschemes therefore represent the same subfunctor of the representable functor of the overlap: both are its pullback of $F'\to F$. Their unique isomorphism over the overlap identifies their open images, so the two pullback opens are equal.

Original dependency statements to reuse: lem-weil-pbc-site-sheafification-sections-local.

### Old step 7 — lem-trf-fppf-local-open-subfunctor-descent

Every fppf covering $\{T_i\to T\}$ is fpqc. To check [def-weil-pbc-fpqc-covering], flatness is already part of [def-pc-fppf-site]. For each affine open $V\subset T$, cover every $\varphi_i^{-1}(V)$ by affine opens $V_{ij}$. Their images in $V$ are open by [lem-weil-pbc-flat-lfp-open] and jointly cover $V$. Since an affine scheme is quasi-compact by [lem-weil-pbc-affine-scheme-qcqs], finitely many of these images cover $V$. These are precisely the affine opens and finite-image-cover condition in the fpqc definition. This is the short argument of Stacks Tag 022C, written out rather than introduced as another node.

Original dependency statements to reuse: def-weil-pbc-fpqc-covering, def-pc-fppf-site, lem-weil-pbc-flat-lfp-open, lem-weil-pbc-affine-scheme-qcqs.

### Old step 8 — lem-trf-fppf-local-open-subfunctor-descent

By step 7, the cover of $T$ is fpqc. Apply [lem-weil-pbc-open-subscheme-fpqc-descent] to the equal-overlap opens of step 6 to obtain a unique open $W_T\subset T$ with inverse images $W_i$. Representable functors are sheaves on the fppf site: by step 7 this follows from the existence and uniqueness of descent of morphisms in [lem-weil-pbc-fpqc-representable-descent], with arbitrary target scheme. The local identifications $h_{W_i}\cong h_{T_i}\times_F F'$ agree on overlaps because they are identifications of subfunctors of $h_{T_i}$, using step 2. They therefore glue, by the sheaf condition, to $h_{W_T}\cong h_T\times_F F'$. More explicitly, after any $Z\to T$ pull back the covering; membership in $W_T$ and existence of a section of $F'$ above $a|_Z$ agree on that covering by steps 4 and 5, and the unique local sections glue. Thus this is a natural isomorphism on all test schemes. Since $a$ was arbitrary, the map $F'\to F$ is represented after every scheme base change by the open immersion $W_T\hookrightarrow T$ [def-weil-open-immersion], which proves both assertions.

Original dependency statements to reuse: lem-weil-pbc-open-subscheme-fpqc-descent, lem-weil-pbc-fpqc-representable-descent, def-weil-open-immersion.

For the generic descent task, substitute G for F' and q for the quotient map in old steps 6–8. Local representatives are supplied as a hypothesis there; the parent verifies that hypothesis using its existing sheafification node. The local model is supplied as the other hypothesis, and its overlap pullbacks are obtained directly by composing maps into the sheaf fibre product. The fpqc finite-subcover argument and the gluing verification remain exactly the arguments written above. For the incidence task, injectivity is a hypothesis proved in the parent, so its future proof uses old steps 3–5 without redoing old steps 1–2.

## Unfinished work

The two new statement nodes deliberately remain unsplit so other workers can prove their separate arguments in parallel. This is the requested outcome, not an unfilled portion of the item's assembly. No source dispute or mathematical obstruction was found.

## Dry-run repair log

The first completed packaging dry run requested two additional same-tag comparisons with `lem-coef-infinity-cartesian-initial-boundary-lift`. I opened its statement: it concerns boundary lifting in cartesian fibrations of infinity-categories and cites Kerodon 02WU, not Stacks 02WU. I added both explicit comparisons above; neither candidate states a scheme or sheaf assertion.
