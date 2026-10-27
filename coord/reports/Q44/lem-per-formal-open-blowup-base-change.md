# Q44 stage-1 report

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-formal-open-blowup-base-change.json: statement split into eight explicit proof steps; statement and statement dependencies unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-per-completion-finite-type-base-change.json: new statement-only lemma, unsplit; no Mathlib match. Completion of arbitrary finite-type schemes, completed tensor formula and functoriality, independent of blowups.
- dag/nodes/sec-deligne-laumon-a1/lem-per-adic-formal-open-gluing.json: new statement-only lemma, unsplit; no Mathlib match. General formal-space/ideal descent, independent of blowups.
- citations.json: verbatim statement excerpts for every step/node pair. Complete statements are quoted for interfaces with several clauses used.
- searches.jsonl: results recorded by the mandatory msearch.py command. All searches were executed and their hits read; the two finite-module completion and ordinary locally ringed-space gluing candidates were inspected in source.

## Attachments

None for this item. Searched the project under lean/WeilConjectures for the blueprint tag, formal scheme/blowup terminology and Rees algebra terminology. Ordinary blowup declarations in WeilConjectures/Blowup/ do not state this formal-scheme item. In particular blowupFlatBaseChangeIso in FlatBaseChange.lean:155 is ordinary, and has a different factor order; it is not an attachment for the present item. No Lean was written or compiled.

## Wanted literature

WANTED: Michael Temkin, Functorial desingularization of quasi-excellent schemes in characteristic zero: the non-embedded case, arXiv:0904.1592v2, §§2.4.3–2.4.8 (printed pp.14–15), archival copy for lem-per-formal-open-blowup-base-change. Read the source online at https://math.huji.ac.il/~temkin/papers/Non_Embedded_Desingularization.pdf on 2026-10-24. The proof_origin is agent, because the naturality and cancellation details are expanded here and the archive is absent.

## Corrections and scope

The imported statement is retained. Its source's compatibility assertion is expanded rather than used as an uncited theorem. A tempting proof of rigidity using the complement of the exceptional divisor would be invalid as a formal-space density argument: an open center can have the whole closed fibre as support. Temkin §2.4.5 also explicitly warns that a completed chart need not embed in the formal localization at its exceptional generator. Step 5 instead uses cancellation of the exceptional generator on actual completed charts, then continuity and separatedness. This is a proof correction, not a statement dispute.

The first draft's tower induction needed a flatness check at intermediate stages. Added Step 6 using the existing flat-module base-change and flat-module-completion nodes. In particular I did not replace an arbitrary ideal completion with the local maximal-ideal completion theorem. Non-affine overlaps are handled by common principal formal refinements and open gluing. The statement does not assume quasi-excellence until its last clause; none was used earlier.

No unit or chapter record is changed. The latest blueprint ancestor lem-per-artin-gabber-affine-curve and the unit sk-p-dl-a1-perverse were read. This descendant supplies formal-resolution tools under the ancestor's Step 3 branch and does not change that unit's route. Off-unit unsplit algebraic inputs are declared in split_report.tool_uses where required.

## Unfinished work

No unfinished work in the one-level split. The two new nodes intentionally have statements only, no proof steps and no proof dependencies. They remain future stage-1 items. No Mathlib leaves were added.

## Review by Q44

I read the whole required delivery-errors sections B–E, the stage-1 brief, GOAL.md, the three blueprint levels in SETUP.md and the live item. For the item I read Temkin §§2.4.3–2.4.8 online, including the counterwarning on completed charts, and Stacks divisors.tex Tags 0804 (lemma-blowing-up-affine), 0805 (lemma-flat-base-change-blowing-up), 02OS (lemma-blowing-up-gives-effective-Cartier-divisor), 0806 (lemma-universal-property-blowing-up), and 0BFL (lemma-characterize-affine-blowup). The latter three informed the chart-cancellation check but are not black-box proof citations. For the first new node I read formal-spaces.tex Tag 0AHY and equation 0AHZ, and algebra.tex 031C and 0316: the new statement identifies the completed tensor, not the generally incorrect uncompleted tensor. For the second I read the topologically ringed-space description in 0AHY and the open topological/sheaf gluing construction 01JA. Its assertion is general formal gluing with ideal descent, not a disguised assertion of this item's blowup clauses.

I opened and read every statement cited in the eight steps and checked it against the exact hypotheses as follows.

1. The affine-cover node really covers the blowup by the ratio rings, and the finite-type-algebra theorem really needs only a Noetherian base. The ratios of a finite set of ideal generators generate each ratio ring, so the hypothesis holds. The homogeneous-localization cocycle node really supplies the identity/inverse/triple equalities transported by completion. The new completion node gives the completed charts and their Noetherian formal scheme, not just a degreewise identification.
2. The ordinary flat comparison theorem alone has a short context-dependent statement, so its actual comparison-definition node is cited too. I read that definition: its flatness hypothesis is satisfied by A→B and its degree-zero/coefficient maps specify the canonical morphism. The new completion node identifies the completed ordinary pullback with the formal product for this finite-type Z; it does not assert an uncompleted tensor identity.
3. The principal-refinement node states both the completed-localization formula and common principal refinements. Localization is Noetherian by its cited node, so the completion-flat theorem applies. Localization flatness and composition flatness give the precise flat ring map to which Step 2 applies. The formal-gluing node supplies gluing on arbitrary overlaps, including ideals; no affine intersection or quasi-excellence hypothesis was smuggled in.
4. The two chart nodes actually state injectivity of multiplication by a and J C_a=(a), respectively. Completion flatness plus the explicitly cited flatness definition preserves that injection. The same reasoning after principal localization proves the sheaf assertion, not merely its global-section version. The cocycle node supplies the overlap localization where ratios become units; completion preserves that open restriction by the new completion node. The proof does not assume a injective on A itself.
5. The only outside facts are the formal affine continuous-map correspondence and equality of maps on an open cover, both explicitly in the new nodes' statements. The substantive cancellation argument is written in the item: choose a target b-chart locally, write b=a d, cancel a in a=a d v*(a/b), and get the target a-chart. Then fix every ratio, hence the dense original ratio ring and its separated completion. This neither cites the proof of another node nor outsources the rigidity clause to a new lemma.
6. The module base-change node says C⊗_A B is flat over C. The flat-module-completion node allows arbitrary ideals of a Noetherian base, and arbitrary flat modules, so it applies to this usually non-finite C-module. It yields flatness of the completed chart map. Finite type over B gives Noetherianity of C⊗_A B before completion; the completion Noetherian and completeness node statements give exactly the remaining stage hypotheses. This repairs the missing induction hypothesis in the draft.
7. General comparisons and inverses glue by the general formal-gluing statement. Coefficientwise equality supplies identities and composition compatibility; the new completion node explicitly includes both. The tower induction starts with length zero, uses Step 6 for the next base change, and Step 5 for uniqueness; it preserves the specified ideal at every stage. Finite disjoint unions and the unit center use explicit componentwise/chart calculations, not new clause nodes.
8. The G-ring and J-2 affine-cover nodes supply their predicates on every affine open of Spec A from its one-chart cover. Since a G-ring is Noetherian by definition, this gives every-affine quasi-excellence and makes the next hypothesis precise. The finite-type quasi-excellence node applies to the ordinary blowup over Spec A. The formal-affines node explicitly states quasi-excellence of every formal affine after completion of a Noetherian quasi-excellent scheme. The locality node explicitly states affine-cover independence, which transfers that conclusion between the covering completed models. These are precisely the statements cited, with the Q-algebra structure unchanged under completion.

I checked small cases for the item and both new nodes. For K=0 these are ordinary schemes and the usual blowup; for nilpotent J its Rees Proj is empty, so all completed charts are zero rings, and no cancellation is applied to a nonempty chart. For J=(1) the chart is A and its center is empty. For A=0, empty covers, empty disjoint unions and length-zero towers the constructions and uniqueness statements have their expected empty/identity values. An identity flat map gives identity coefficient maps. A zero chart is allowed. For the completion node C need only be a finite-type algebra, not a finite A-module (the polynomial example prevents confusing the two); non-flat base change is allowed there because it only compares completion with formal product, not blowup with blowup. For the gluing node overlaps may be non-affine and no common global algebra is assumed. Every non-elementary step is fully written and names its inputs; none is longer than 2000 characters, and the new statements contain no proof sketches. I checked every citations.json quote by exact substring membership in the corresponding statement.

## Search audit

Searched the entire DAG for the item, formal spectra/formal blowup, completion/base change, gluing, and the source tags; searched the entire current blueprint with blueprint_refs.py for formal blow, completion, completed tensor, gluing formal, formal completion, Noetherian formal and completion base change. None states either new node. The existing formal-principal-refinement and formal-completion-reduction-dictionary nodes were read and reused or distinguished: principal section localization and a quotient dictionary do not give the finite-type completed product. Ordinary scheme and locally ringed-space GlueData are candidates, but not one-line specializations giving topological sheaves and formal coherent-ideal gluing. Mathlib AdicCompletion.ofTensorProductEquivOfFiniteNoetherian in AsTensorProduct.lean:328 was inspected with its finite-module hypothesis; it cannot apply to arbitrary finite-type chart algebras. All recorded queries exactly match msearch.py output and no unavailable service was counted as an absence. The item carries its earlier searches unchanged plus this session's searches.

## Not duplicates

lem-per-completion-finite-type-base-change vs def-per-adic-formal-geometry: existing node concerns adic formal completions, formal spectra and affine-chart regularity; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs def-per-adic-principal-chart-data: existing node concerns principal formal opens, section topologies and canonical comparison data; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-per-formal-affine-principal-refinement: existing node concerns principal refinements and local algebra of noetherian formal affine charts; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-per-formal-completion-reduction-dictionary: existing node concerns infinitesimal quotients on arbitrary affine charts of a formal completion; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-per-noetherian-formal-affine-coherent-modules: existing node concerns finite modules and coherent sheaves on a noetherian formal affine; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs def-weil-pbc-coherent-formal-modules-affine-quotient-cone: existing node concerns canonical cone on sections of affine formal quotients; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs def-weil-pbc-multivariate-power-series: existing node concerns formal power series ring in finitely many variables; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-adic-completion-mod-ideal: existing node concerns the completion along a finitely generated ideal is complete with the same quotient; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-adic-completion-noetherian: existing node concerns the completion of a noetherian ring is noetherian; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-coherent-formal-modules-affine-complete: existing node concerns affine formal modules: complete; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-coherent-formal-modules-affine-quotient-cone: existing node concerns finite completed modules are limits of their canonical affine quotient cones; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-completion-noetherian-quotient-noetherian: existing node concerns adic completion is noetherian when the quotient is noetherian and the ideal finitely generated; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-completion-tensor-quotient-separated: existing node concerns quotient projections separate a completed finite tensor; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-g-ring-completion-regular: existing node concerns the completion of a g-ring along an ideal is a regular ring map; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-weil-pbc-power-series-onto-completion: existing node concerns power series in generators of i map onto the i-adic completion; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-sfb-artin-completed-polynomial-test-ring: existing node concerns completed polynomial test rings and their lifting property; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-sfb-supported-complex-ext-completion: existing node concerns supported pseudo-coherent ext is unchanged by completing coefficients; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-completion-finite-type-base-change vs lem-trf-complete-model-coefficient-nonvanishing: existing node concerns coefficient control and monomial survival in completed monoid hypersurfaces; the new statement gives completion of arbitrary finite-type schemes, its completed tensor product under any complete Noetherian adic base change and the formal affine morphism correspondence.

lem-per-adic-formal-open-gluing vs def-per-adic-formal-geometry: existing node concerns adic formal completions, formal spectra and affine-chart regularity; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs def-per-adic-principal-chart-data: existing node concerns principal formal opens, section topologies and canonical comparison data; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-per-formal-affine-principal-refinement: existing node concerns principal refinements and local algebra of noetherian formal affine charts; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-per-formal-completion-reduction-dictionary: existing node concerns infinitesimal quotients on arbitrary affine charts of a formal completion; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-per-noetherian-formal-affine-coherent-modules: existing node concerns finite modules and coherent sheaves on a noetherian formal affine; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-weil-pbc-constant-group-scheme-multiplication: existing node concerns the multiplication of the constant group scheme: the components of t_e x_t t_e and the glued morphism; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-weil-pbc-glue-schemes: existing node concerns glueing schemes along open subschemes; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-weil-pbc-proper-coproduct: existing node concerns disjoint union of two proper schemes over a base is proper; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-weil-pbc-scheme-coproduct-copies: existing node concerns coproduct of copies of a scheme is etale over it; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-weil-pbc-scheme-morphism-gluing: existing node concerns morphisms of schemes glue along an open cover; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-a1-normal-geometric-cover-universe-descent: existing node concerns small finite etale subcovers of universe-enlarged normal geometric coverings; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs lem-a1-universe-enlarged-proetale-cover: existing node concerns fpqc covers remain fpqc after canonical universe enlargement; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-adic-formal-open-gluing vs def-trf-scheme-universe-enlargement: existing node concerns canonical universe enlargement of a fixed scheme; the new statement glues adic formal spaces with continuous local morphisms and coherent formal ideals; it is not ordinary scheme gluing or a formal affine quotient/section dictionary.

lem-per-completion-finite-type-base-change vs lem-per-adic-formal-open-gluing: the former compares completion with adic base change on an already supplied scheme, while the latter constructs formal spaces and ideals from arbitrary open descent data. Neither states an existence/base-change/rigidity clause specialized to blowups.

## Validation tool failure

The required deliver.py --no-push invocation exited 1 after server preflight timed out after 720 seconds and its fallback timed out after 600 seconds. Before admission it waited 1314 seconds in the server queue. The separate srvcheck.py check_dag invocation failed with the same 720-second remote and 600-second fallback timeouts. Neither returned any mathematical/preflight finding. A retry of the final sandbox entered a queue of 79 requests, remained at 79 for more than 150 seconds, and was cancelled to leave no active delivery process. The final local JSON cross-check validates all 37 step/node citation quotes and every new-node query against searches.jsonl; the longest step has 1319 characters. No push was attempted and no successful final dry run is claimed.
