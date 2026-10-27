# Stage-1 report: lem-sfb-space-schemehood-local-ring-test

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-schemehood-local-ring-test.json: statement node, now split; no exact Mathlib match. Five proof steps, using eleven existing dependency nodes.
- citations.json: one verbatim statement quotation for each citation of each proof step.
- searches.jsonl: actual msearch.py records for this item; earlier searches in the repository item are retained.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures for the exact item id, enough_local, enoughLocal, schemehood, IsAlgebraicSpace, AlgebraicSpace and isScheme. No declaration stating this algebraic-space criterion was found; scheme-theoretic-dominance declarations do not concern it. No sorry declaration was counted as finished.

## WANTED

None. All sources needed here are available locally.

## Findings and corrections

The imported statement agrees with Stacks spaces-limits.tex, Tag 0B80 (lemma-enough-local). It retains qcqs of the morphism, and tests only points in the image of X. No statement change or dispute is needed. The original item had no proof. Its Mathlib searches were inherited from Q120; I retained them and added five actual logged searches of my own (LeanSearch, Loogle, grep, and two LeanFinder phrasings). The returned QuasiSeparated declarations are about scheme-source morphisms. Scheme.LocalRepresentability.isRepresentable gives Zariski gluing once scheme open representatives exist, not the required passage from local-ring pullbacks to those representatives. I read Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean and Sites/Representability.lean to check that distinction.

The DAG already has both local-ring affine-neighbourhood limit statements, both schematic-stage formulations, and the largest schematic-open theorem. I use lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods, whose statement specifies the actual canonical maps, and lem-sfb-space-affine-limits-schematic-stages, whose statement specifies the sheaf limit and eventual schemehood. Nothing is moved into a renamed copy of the item.

The item has inherited blueprint.from.node = null; blueprint_refs.py ancestor reports None. I preserve this maintainer-owned ancestry and its explicit inherited place, set same_as to [], and identify the supporting Tag 0B80 argument in split_report. Searches of the whole blueprint for 0B80, schemehood, scheme limit, 07SR, local ring and affine neighbourhood found no blueprint statement of this criterion. Read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The proof stays below the inherited compactification/direct-image prerequisites; it changes no chapter or unit route.

## Not duplicates

No new nodes. Existing lem-weil-pbc-affine-neighbourhood-stalk-limit is a second local-ring-limit formulation, and lem-sfb-affine-space-limit-schematic-stage is a second schematic-stage formulation. I cite an existing statement in each case and create neither a duplicate nor an item-clause restatement. The field-base lem-sfb-space-dense-schematic-locus would require a field; the cited lem-sfb-space-largest-schematic-open works over the arbitrary base S of this item.

## Review by Q127

I read the item and all eleven cited node statements, with their Stacks sources open. The central source is spaces-limits.tex Tag 0B80 in full. I also read Tag 07SR (lemma-limit-is-scheme) and its Situation 084R, the local-ring-limit discussion in limits.tex Tag 0GWT (lemma-morphism-glueing-near-closed-point), the affine base-change lemma in spaces-morphisms.tex, the quasi-separated base-change and source lemmas there, and the open-subspace, quasi-compact-space and largest-schematic-open statements and proofs in spaces-properties.tex. There are no new-node sources to certify.

Step 1 explicitly resolves a real convention issue: the item uses point-space quasi-compactness and affine tests, whereas some tools quantify over quasi-compact algebraic spaces. lem-sfb-qc-space-affine-etale-atlas gives an affine atlas P of any such test C. lem-trf-space-fibre-products-etale-covers gives the surjective etale pullback E_P to E_C. lem-a1-space-etale-open-image supplies both the quasi-compact image and the atlas/topology equivalence. Consequently a single affine test proves the requisite quasi-compactness over C; no descent theorem has been silently assumed. This is a short argument from those statements, marked elementary.

Step 2 uses the full statement of lem-weil-pbc-local-ring-spec-limit-affine-neighbourhoods: the neighbourhood set is nonempty and directed, its inclusions are affine, and its limiting cone is the canonical local-ring map. In particular it does not merely identify an unspecified abstract limit with a stalk. The fibre-products node supplies X_W as an algebraic space. The given quasi-compactness of g supplies quasi-compactness of each X_W, rather than an unjustified claim that X is globally quasi-compact. lem-sfb-space-quasiseparated-test-calculus supplies base change of relative quasi-separatedness. lem-weil-pbc-affine-scheme-qcqs supplies absolute quasi-separatedness of W; the first assertion of lem-sfb-space-qcqs-source-products then supplies absolute quasi-separatedness of X_W. Step 1 reconciles that node's test convention. The absolute conclusion forgets the structural map to S; no quasi-separatedness of S or T is assumed.

Step 3 takes affine base change exactly from lem-sfb-space-affine-locality. I wrote the limit comparison on every S-scheme test: a common X-section and compatible maps to the affine neighbourhoods give a unique map to the local-ring spectrum, and conversely. Directedness makes the X-sections common; the projection equations in the local-ring-limit node give the equality over T. Naturality is immediate from composing these maps. Thus the cited limit theorem is being applied to its specified sheaf limit, not to an unverified category-level limit. This is a universal-property calculation, not a separate hidden representability lemma.

Step 4 uses exactly the schematic-stage assertion in lem-sfb-space-affine-limits-schematic-stages. I verified all its assumptions: small nonempty directed index, qcqs stages, affine transitions, a sheaf limit, and a scheme as that limit. None of these requires finite presentation of g, a Noetherian base, or that every point of T be hit. The chosen x supplies precisely the hypothesis that X_L is a scheme. The output is one affine neighbourhood W containing t with schematic X_W, not a claim that the entire morphism spreads out over all of T.

Step 5 uses the explicit point-preimage clause in lem-a1-space-open-factor-scheme-tests to ensure x belongs to X_W. lem-sfb-space-largest-schematic-open says that the schematic open contains every such X_W. Finally lem-a1-space-etale-open-image supplies the bijection between open subspaces and point opens, so equality of point sets implies equality with X. This avoids citing a gluing theorem whose statement only asserts algebraic-space gluing. It also shows that the empty space is covered by the argument.

For the delivery-errors B checklist I checked self-contained unchanged hypotheses, correct TeX, Stacks tags with labels, real searches and explicit provenance; no statement-only new nodes or leaves are being introduced. For C I verified each cited statement says the fact taken from it and copied it verbatim into citations.json. All non-elementary inputs occur in uses, whose union is proof_deps. I traversed the cited nodes' dependencies read-only and found no path back to this item. The generic off-unit tools are declared in split_report.tool_uses, with their purpose; I did not set the maintainer-owned tool_uses field. For D the actual argument remains in the item, particularly the limit comparison and neighbourhood assembly. For E I tested X empty, a point mapping into a proper subset of T, a non-quasi-separated global base, and affine neighbourhoods whose intersections need not themselves be affine. Directedness only chooses a smaller affine neighbourhood inside an intersection; every transition is a map between affine schemes. No field, integrality, reducedness, properness, flatness or finite-presentation hypothesis was added or used. Every proof step is under 2000 characters, and no new lemma is hidden by a long step.

## Unfinished

None in the one-level split. The required server dry run and delivery are performed after this report is written; their tool output is the validation record.
