# Q29 stage-1 delivery

Item: lem-sfb-scheme-etale-relative-differentials-comparison. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-etale-relative-differentials-comparison.json — item, statement unchanged, seven proof steps, status split. Not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-etale-localization-relative-differentials.json — one new statement-only prerequisite, Stacks Tag 04BX, status unsplit. Mathlib supplies ring-level ingredients but no exact scheme differential-sheaf theorem.
- citations.json — a verbatim statement excerpt for every citation of every item step.
- searches.jsonl — the msearch-generated search records. All retained earlier searches were read, including the results from before the launcher pause.

There is one new node and zero Mathlib leaves. No Lean was written or compiled. The shared repository and launcher files were not edited, and no git command was run in the shared repository.

## Attachments

None. Searches in lean/WeilConjectures by the exact blueprint tag, the item id, relative differential notation, etale differential comparisons, and 04BX found no declaration proving this item or the new prerequisite. The affine differential declarations in the project are partial ingredients, not the claimed ringed-topos comparison. Mathlib declarations are not project attachments.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Findings and corrections

The item had an empty proof and was still unsplit when work resumed. Its statement agrees with spaces-more-morphisms.tex, lemma-match-modules-differentials (04CS), with the concrete sheafification model furnished by sites-modules.tex, lemma-differentials-sheafify (08TP). Its statement, hypotheses and statement dependencies are unchanged.

The source ends by omitting the verification of the inverse comparison. I expanded it instead of treating agreement on Zariski opens as sufficient for arbitrary maps of etale sheaves. First construct a factorization for any target sheaf G by restricting its derivation to Zariski opens and applying the specified extension theorem. For an affine etale chart Spec B -> Spec A the difference between the two candidate derivations kills A; Omega_{B/A}=0 then forces it to vanish. Finally the existing open-determination theorem gives uniqueness for maps out of the associated tensor-sections sheaf. This distinguishes the generator check for derivations from the linear-map uniqueness check. The source also writes that c-double-prime and c-prime are mutually inverse although the maps with opposite domains are c-double-prime and c; the delivered proof names the correct two maps b and c. This is a proof-notation typo, not a change to the mathematical statement.

The new node is only the Zariski scheme-sheaf comparison under etale changes of the source and base (04BX). It mentions neither the small etale topos nor the associated etale sheaf. Its proof is deliberately empty; the item carries the actual comparison argument. The new node's intended later proof is the one printed at 04BX: change the base by the ordinary differential transitivity sequence, then use smooth transitivity and vanishing of relative etale differentials for the source change. No such sketch is put into its statement.

Every step is shorter than 2000 characters. Step 5 is elementary after its three cited inputs: the difference derivation factors through the zero ring-differential module and is zero, then the sheaf axiom detects equality. Step 7 is the two universal-property uniqueness equations. None of the source's substantive comparisons has been hidden in an elementary label.

## Searches and blueprint provenance

I read the chapter record and unit sk-thm-sf-ctf-stability, then the current latest blueprint files in sec-six-functors-basics/sk-thm-sf-ctf-stability/, including its direct-images proof (3). This item is an inherited support input in the differential-finite-presentation branch below that proof, not the unit's key statement; no unit realization fields are changed.

Before creating the new node I searched the entire DAG by 04BX, lemma-sheaf-differentials-etale-localization, and etale-localization/differential words, searched the whole blueprint using tools/blueprint_refs.py search 04BX and search 'etale localization relative differentials', and searched project Lean by the id, tag and concept. Both blueprint searches returned zero matches. The broader differential blueprint search found no equivalent standalone theorem. The ancestor command returns None for this imported support chain; the new node retains node=null and extends the exact inherited via chain with this item, with a concrete source-proof place. The item's existing concrete from.place is retained and same_as is [].

Mathlib searches used only the mandated msearch.py. The new node records two semantic phrasings, LeanSearch, two Loogle searches and source grep, with the exact query texts and original logged results. The item retains its earlier Q46 searches and appends this session's comparison searches. All services answered; none was recorded as unavailable. I read Mathlib/RingTheory/Etale/Kaehler.lean:38-52 (tensorKaehlerEquivOfFormallyEtale and its formula on differentials) and Algebra/Category/ModuleCat/Differentials/Presheaf.lean:193-239 (sectionwise presheaf differentials and their universal derivation). The former is only a ring theorem; the latter does not identify the presheaf sheafification with the scheme's Zariski differential sheaf. Affine-to-scheme gluing is not a one-line specialization, so the new node is not marked mathlib.

## Not duplicates

No existing nonmerged node was found with source Tag 04BX or its label.

lem-sfb-etale-localization-relative-differentials vs lem-sfb-scheme-etale-relative-differentials-comparison: 04BX compares two Zariski scheme differential sheaves under an etale source/base square; the item compares Zariski-associated etale modules with the differential object of the small etale ringed morphism. The former is the first prerequisite of the latter, not a restatement of its conclusion.

lem-sfb-etale-localization-relative-differentials vs lem-trf-relative-differential-sheaf-base-change: the existing node assumes a cartesian square and allows arbitrary base change; the new node assumes both horizontal maps etale and does not require a cartesian square. A general etale source change with unchanged base is the case used here and is not cartesian in general.

lem-sfb-etale-localization-relative-differentials vs lem-trf-formally-etale-differentials-base-change: the existing node concerns commutative rings with the cotangent-module criterion for formal etaleness; the new node is a Zariski sheaf isomorphism for arbitrary scheme squares with two etale horizontal maps.

lem-sfb-etale-localization-relative-differentials vs lem-sfb-scheme-naive-cotangent-etale-comparison: the existing node is a derived comparison for a sheaf naive cotangent complex between Zariski and etale ringed sites. It does not state the scheme-to-scheme etale-localization comparison. No derived or per-degree substitute is introduced here.

## Review by Q29

I checked the item against Stacks spaces-more-morphisms.tex 04CS, lemma-match-modules-differentials, including all proof paragraphs, and 04CT, definition-sheaf-differentials, for the ringed-topos interpretation. The base morphism is arbitrary in the source and remains arbitrary in the item. The quasi-coherence of the ordinary differential sheaf is its affine-local form, not a finite-presentation claim. I checked the concrete sectionwise sheafification model in sites-modules.tex 08TP and the derivation-representing language in 04BL/04BN. I read more-morphisms.tex 04BX, lemma-sheaf-differentials-etale-localization, for the new node: its square commutes, only the two horizontal maps are etale, and no cartesian or finite-type assumption on the vertical maps is present. The new node states exactly that canonical differential map, normalized on local differentials, with no proof or proof dependencies.

For Step 1 I opened the statements of the new 04BX node, def-sc-etale-qcoherent-module, lem-sfb-relative-differentials-sheaf-universal-property, both scheme module-pullback lemmas, and lem-weil-pbc-etale-composition-cancellation. The first gives q_h, the definition gives the section values and restrictions of F_et, scheme universality and the adjunction determine the differential comparison, and the composition comparison puts the two pullback sources in the same module. The etale cancellation lemma explicitly says every map between etale U-schemes is etale, so it applies to the restriction arrow. I verified the equality on pulled-back da instead of asserting unspecified naturality.

For Step 2 I opened lem-trf-space-enlarged-etale-ringed-site-model and lem-weil-pbc-etale-inverse-image-section-description, whose statements supply chart localization/composition and local representatives from etale objects of the base. The latter is applied to the underlying sheaf of sets; vanishing is tested by the target sheaf's separatedness. A representative comes from V_i etale over V, and 04BX applies with identity source arrow and base arrow V_i -> V. It identifies the two universal differentials, so the regular function from V_i has zero V-relative differential. The cited scheme universal-property node explicitly includes base-vanishing. I did not assume a section of f^{-1}O_V is pulled back from a Zariski open of V.

For Step 3 I read the statement of lem-trf-sheafified-module-differentials-cokernel. It identifies this exact sectionwise sheafification, carries its derivation to the representing derivation, and defines the representing property. Thus it supplies existence and uniqueness of c; a definition of a module category is not being used as a theorem about derivations.

For Step 4 I read lem-trf-zariski-etale-tensor-sections for the direct-image restriction formula, lem-sfb-relative-differentials-sheaf-universal-property for factorization into any O_U-module sheaf, and lem-trf-etale-tensor-sections-adjunction-extension for the explicitly normalized extension beta_D and its equality on every open. The target G is arbitrary and is never assumed quasi-coherent. Only the source F is quasi-coherent; def-sc-etale-qcoherent-module says its tensor-sections presheaf is already a sheaf. The source's Descent 070S/03FH ringed-site discussion agrees with this construction.

For Step 5 I read the full statements of lem-weil-pbc-etale-composition-cancellation, lem-weil-pbc-etale-ring-map-iff-etale-affine and def-weil-pbc-kahler-differentials. The first makes Spec B -> Spec A etale after choosing affine opens, the second explicitly includes Omega_{B/A}=0, and the third represents derivations into every B-module. Here G(T) is such a module, so the difference E_T factors through zero and vanishes. I verified the scalar ring is A, from a Zariski open of U, not the possibly larger inverse-image base-section ring. The argument uses an affine open cover of each chart, not affine intersections, and therefore needs no separation hypothesis.

For Step 6 I opened lem-trf-etale-tensor-sections-open-determination. It says exactly that the restriction to all Zariski opens is injective on module-presheaf maps out of the specified tensor-sections presheaf, without a target quasi-coherence assumption. This is applied to F and G after uniqueness of the Zariski factorization from the scheme universal-property node. Step 7 is then checked directly: bc fixes d_et and cb fixes d^a, so the two respective uniqueness assertions give the two identity maps. The final isomorphism b has the direction required by the item and satisfies b d^a=d_et.

I checked B1--B9 for the one new node: it is self-contained, names each object and relevant definition, uses normal single-escaped TeX in decoded text, cites the correct 04BX label, has no proof and no match claim, records only executed searches, and is not a clause of the item. I checked the C1/C4 obligations by reading every cited statement and writing its verbatim excerpt in citations.json; no proof of a cited node is used as an interface. The dependency union equals the union of the step uses. I also checked that every chosen existing prerequisite has no path back to the item, so the new split introduces no cycle.

Small cases: with X_2 empty the new comparison is the unique zero-module isomorphism; with identity horizontal maps it is the identity on da. With S_2=S_1 and X_2 an etale open or a finite separable extension chart, it is the usual localization or separable differential comparison; nilpotents in the base are allowed throughout. The case of an arbitrary noncartesian etale square is included by the statement of 04BX itself. For the item, f=id gives zero differentials, U empty gives zero sheaves, and an arbitrary nonflat/non-finite-type f still has affine differential modules and the same argument. No new hypothesis was inferred from these examples.

Generic off-unit tools are declared in split_report.tool_uses: the chart model, local inverse-image representatives, the sheafified differential universal property, Zariski–etale restriction, section-normalized extension, and open determination. They implement the 04CS argument and do not replace a geometric step of the unit. The source and every prerequisite are present; nothing remains unfinished except the intentionally unsplit new 04BX node.

## Validation

The required remote dry run exited successfully: OK (not pushed), commit 103383f0c34, preflight passed. The remote delivery preflight includes check_dag.py and review_split.py. This report records that result; the final report package is rechecked before push. No check_dag.py, review_split.py, preflight_delivery.py, compiler, or Lake command was run locally.
