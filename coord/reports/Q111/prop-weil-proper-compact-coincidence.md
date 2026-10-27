# Worker report: Q111 / prop-weil-proper-compact-coincidence

## Files written

- dag/nodes/sec-zeta-weil/prop-weil-proper-compact-coincidence.json: split statement, unchanged statement and stmt_deps; short assembly.
- lem-weil-proper-finite-normalization: statement, unsplit; no Mathlib match.
- lem-weil-proper-integral-tower-comparison: statement, unsplit; no Mathlib match.
- lem-weil-proper-coefficient-descent: statement, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for every assembly dependency.
- searches.jsonl: unaltered msearch log; repair.py is the sandbox-only JSON writer.

## Attachments

None. AlgebraicGeometry.WeilComplex.proper_compact_coincidence in lean/WeilConjectures/ZetaFunction/Weights.lean:71 concerns Weil complexes built from rational adic sheaves, not every finite, integral, rational and common-stage coefficient construction of this item. It does not supply the full statement. The project theorem WeilConjectures.properCompactCoincidence in lean/Sheaf/Paper/ProperCompactCoincidence.lean:85 has sorry at line 143. No Lean files were changed and no compiler was run.

## WANTED

None. All immediate sources were available in the repository. No SGA sources are used.

## What was wrong and what changed

The released repair note requires spreading the 3658-character old proof into at least two genuinely separate parallel tasks. The sandbox initially contained only dispatcher marker files: no node, report, search log or prior delivery to resume. I copied the live returned head as the baseline, retaining all its fields and its statement. Three new tasks now carry the old finite, integral and field-coefficient arguments. Each is unsplit, with no proof steps, proof dependencies or embedded proof sketch. Their statements prescribe the relevant diagrams and normalized comparisons; the detailed old arguments are retained verbatim below for the future workers. The last Fib_s/cohomology argument remains elementary in the parent assembly. There is no statement dispute or route change. The parent is not the key node of sk-input-weights, so the unit realization fields were not changed.

## Unfinished work

No repair task remains before delivery checks. Proving the three new statement-only nodes belongs to the later workers by the explicit re-split order. No claim of a completed Lean proof is made.

## Not duplicates

lem-weil-proper-finite-normalization vs cor-cbc-proper-coincidence: the existing corollary defines the identity-open proper comparison and proves its base-change exchange compatibility; the new task asserts refinement-independent normalized finite comparisons and their compatibility with the actual quotient restriction maps. It is not a new node just for existence of the identity-open isomorphism.
lem-weil-proper-finite-normalization vs prop-compactification-coherence-detailed: the existing theorem compares compactifications on etale-origin inputs; it does not identify the identity-compactification output with ordinary direct image together with quotient compatibility.
lem-weil-proper-finite-normalization vs lem-coef-proper-identity-open-site-comparison: that node compares etale/pro-etale site-change mates; this node compares quotient coefficients and compactification choices on one pro-etale site.
lem-weil-proper-integral-tower-comparison vs lem-sf-integral-compactification-comparison-bridge: the existing bridge identifies composition comparisons for three compactified morphisms with counit formulas under additional Tor and system hypotheses; this task identifies the two entire defining towers for one proper morphism, including their actual quotient transitions and limit projections.
lem-weil-proper-integral-tower-comparison vs lem-pod-identity-compact-support-normalization: that theorem concerns the identity morphism of Spec k and the completion unit; here f is an arbitrary proper morphism and its target is not required to be a point.
lem-weil-proper-integral-tower-comparison vs det-sp-tower-classes: that node constructs Kummer and diagonal classes and the projective-line trace, not the two direct-image towers or their comparison.
lem-weil-proper-coefficient-descent vs lem-sf-framework-common-stage-descent: that generic descent theorem assumes scalar compatibility. The new task verifies scalar compatibility of the specified identity-open, projection-normalized proper comparison before localizing and descending it.
lem-weil-proper-coefficient-descent vs lem-weil-point-transformation-coefficient-descent: that theorem concerns supplied transformations from point sections to sections after an automorphism pullback and assumes their scalar equation; this concerns the actual proper-image comparison on an arbitrary proper morphism and asserts its scalar equation.
lem-weil-proper-coefficient-descent vs lem-sf-native-weil-proper-shriek-star: that node is about native equivariant derived operations on Weil categories, not the four recorded coefficient constructions and their specified comparisons.
lem-weil-proper-coefficient-descent vs lem-sf-rational-direct-image-coefficient-compatibility: that node fixes a pullback stage-system and the invertible right mate of its coefficient map; it does not verify the compatibility of the compact-support/ordinary comparison.

## Review by Q111

I read coord/delivery-errors.md B–E in full, the chapter and unit, the released keep_plan repair note, the current main-20261015 statement and proof, the live returned four-step proof and its existing review, and the project Lean statement/docstring. The new finite task realizes the identity compactification paragraph: it includes the sectionwise extension-by-zero normalization, all common-refinement independence and cocycle identities, and the actual quotient comparison square. I read the statements of def-weil-extension-by-zero, def-compact-support-direct-image-detailed, def-weil-compactifications-refinements, lem-sf-proetale-constructible-origin, prop-compactification-coherence-detailed and lem-sf-compact-support-restriction-of-scalars. They define the exact finite formulas, supply bounded constructible etale origin, and specify that restriction comparison as identity-open restriction followed by ordinary restriction. The finite task does not assert coherence on the whole unbounded pro-etale category: only its identity-open coefficient square is on that ambient domain; common refinements are restricted to bounded constructible inputs.

For the integral task I read def-weil-integral-rational-qbar-compact-support and def-weil-derived-direct-image in full. The terms are restricted to completed integral coefficients, not ordinary constant coefficients. Both tower transitions are the prescribed reduction followed by their specified restriction map. The new statement makes the commuting transition squares and equality of limit projections explicit; taking a limit of an isomorphism of diagrams is routine, but the identification of the diagrams is the separate work. It concerns the derived objects themselves, not only their cohomology groups. No additional finite Tor amplitude is silently imposed.

For the field task I read def-weil-rationalization-karoubi (raw Hom localization, with no Karoubi completion), def-weil-algebraically-closed-coefficients (pair objects and common-stage representatives), def-weil-compact-support-finite-action and def-weil-compact-support-coefficient-action. I retained the obligation to prove compatibility of the actual normalized scalar maps: this is stated as an equation, not assumed away or replaced by unspecified isomorphisms. Projection-preserving tower normalization is a hypothesis for the supplied integral comparisons and is supplied by the integral task in the assembly. The task explicitly requires naturality for sums of pure tensors, representative independence and the equations over each further common extension. Generic common-stage descent alone does not establish those hypotheses.

Assembly C4 audit: step 1 uses the finite task's natural, refinement-independent finite comparison, the ordinary/compact definition's coefficient and geometric data, and the definition of proper over a field. Each statement was open while writing the step. Step 2 uses the integral task's full diagram isomorphism and induced natural integral isomorphism, including projection compatibility. Step 3 uses the field task's conditional scalar equation and rational/common-stage conclusions; its supplied comparisons meet the hypotheses by step 2 and the specified identity normalization in step 1. Step 4 uses exactly the displayed Fib_s and H^i definitions: apply each functor to an isomorphism and its inverse; functoriality preserves the two identity composites. Every direct citation has its exact statement quotation in citations.json. No non-elementary deduction is left without a node and no node's proof is used as its statement.

Self-containedness and small cases: X empty gives the zero diagrams and zero isomorphisms; f=id on Spec k reduces to the identity-extension comparisons and completion tower on both sides; zero input gives zero at every stage; n=1 has no predecessor and its outgoing transition condition comes from n=2. A nontrivial finite extension requires both scalar comparisons in the displayed square; neither was suppressed. For projective space no smoothness, dimension or cohomological amplitude assumption has been added. A nonproper affine line is excluded, as it must be. The rational/common-stage task assumes only integral comparisons actually supplied by the preceding task, with their normalization. The task sizes are comparable and none recovers all coefficient cases of the item alone. The unchanged final cohomology argument is still fully written out in the assembly.

Search audit: I searched the whole DAG by proper coincidence, identity compactification, tower/transition agreement and coefficient descent, and ran blueprint_refs ancestor and searches for proper coincidence, identity compactification, tower comparison, rationalization natural, compactification coefficient, restriction scalars, proper tower and common-stage descent. Existing definition and general descent nodes were read; the nonduplicate distinctions are above. Mathlib searches used only msearch.py; their actual outputs are in searches.jsonl and the node records use the exact query text. Two phrasings were tried for each substantive question (LeanFinder and LeanSearch). Returned scheme-module pushforward/restriction identity and composition declarations concern O_X modules, not these constant finite pro-etale coefficient functors; I read Mathlib/AlgebraicGeometry/Modules/Sheaf.lean, including pushforwardId and restrictFunctorId. The derived-limit grep hits in PointwiseRightDerived/PointwiseLeftDerived concern existence of pointwise Kan extensions, not adic quotient towers. CategoryTheory.Functor.mapIso only handles application of an existing functor to a known isomorphism, not the new comparisons. Loogle unknown-identifier responses are recorded unavailable and the successful mapIso search is retained as an alternative. No unrun search is recorded.

## Preserved argument for each new task (old returned proof verbatim)

### Old step 1 / lem-weil-proper-finite-normalization

Use the finite-field and coefficient data of [def-weil-ordinary-compact-cohomology]. In particular $Y$ is a separated finite-type $k$-scheme and $\ell$ is invertible in $k$. Since $Y$ is proper over $k$, $a_Y:Y\to s=\operatorname{Spec}k$ is proper by [def-weil-proper-morphism]. Thus $c_0=(\operatorname{id}_Y,a_Y)$ is a compactification by [def-weil-compactifications-refinements]. For $j=\operatorname{id}_Y$, every object $V\to Y$ factors through $j$, so the presheaf defining $j_!M$ in [def-weil-extension-by-zero] is exactly $M$, on sections, restriction maps and morphisms; it is already a sheaf. Hence $j_!$ is naturally the identity, including on complexes. The formula of [def-compact-support-direct-image-detailed] therefore gives $Ra_{Y!,n}^{c_0}\cong Ra_{Y*,n}$ for every $n\geq1$. Bounded constructible finite-coefficient objects have etale origin by [lem-sf-proetale-constructible-origin], so [prop-compactification-coherence-detailed] identifies the compactification-independent functor with this value on its required domain; its identity and cocycle clauses make this identification natural and independent of a common refinement.

Uses: def-weil-ordinary-compact-cohomology, def-weil-proper-morphism, def-weil-compactifications-refinements, def-weil-extension-by-zero, def-compact-support-direct-image-detailed, lem-sf-proetale-constructible-origin, prop-compactification-coherence-detailed.

### Old step 2 / lem-weil-proper-integral-tower-comparison

For integral coefficients choose $c_0$ at every level in [def-weil-integral-rational-qbar-compact-support], and put $K_n=K\otimes^L_{\mathcal O_E}A_{E,n}$. The two towers defining $Ra_{Y!}K$ there and $Ra_{Y*}K$ in [def-weil-derived-direct-image] have the same terms $\operatorname{Res}_n Ra_{Y*,n}K_n$. Their transition maps also agree: [lem-sf-compact-support-restriction-of-scalars] specifies the compact-support coefficient comparison as $j_!\operatorname{Res}=\operatorname{Res}j_!$ followed by the ordinary derived-direct-image coefficient comparison. For $j=\operatorname{id}_Y$ the first map is the identity on every section, so both transitions are the same reduction map $K_{n+1}\to\operatorname{Res}K_n$ followed by the same ordinary coefficient comparison. Thus the tower identifications commute with every transition, and taking the derived limit of this identical diagram yields $Ra_{Y!}K\cong Ra_{Y*}K$, naturally in $K$.

Uses: def-weil-integral-rational-qbar-compact-support, def-weil-derived-direct-image, lem-sf-compact-support-restriction-of-scalars.

### Old step 3 / lem-weil-proper-coefficient-descent

For $\Lambda=E$, [def-weil-derived-direct-image] and [def-weil-integral-rational-qbar-compact-support] use the rationalized category of [def-weil-rationalization-karoubi]. Apply localization to the integral isomorphism and its inverse: on a morphism $u\otimes a$ its naturality equation is the integral naturality equation for $u$ multiplied by $a\in E$. The two composites remain identities, giving $Ra_{Y!}\cong Ra_{Y*}$ over $E$. For $\Lambda=\Qlb$, use [def-weil-algebraically-closed-coefficients]: on an object $(E,K_E)$ take the isomorphism over $E$, and on a morphism represented over a common extension $L$ use its naturality equation over $L$. The finite-level comparisons above are identities after choosing $c_0$, so extension of coefficients sends each comparison to the comparison for the extended coefficients. Consequently these equations agree after every further extension and define a natural isomorphism in the common-stage category. This treats all four coefficient rings in the statement's notation.

Uses: def-weil-derived-direct-image, def-weil-integral-rational-qbar-compact-support, def-weil-rationalization-karoubi, def-weil-algebraically-closed-coefficients.

### Old step 4 / retained elementary assembly

For each coefficient ring $\Lambda$ and $K\in D^b_c(Y,\Lambda)$ of [def-weil-ordinary-compact-cohomology], apply $\operatorname{Fib}_s$ to the isomorphism $Ra_{Y!}K\cong Ra_{Y*}K$ and its inverse. Their composites remain identities. The displayed definitions give $\RGammac(Y,K)\cong\RGamma(Y,K)$. Applying the degree-$i$ cohomology functor to these two inverse maps again gives inverse maps, hence $H_c^i(Y,K)\cong H^i(Y,K)$ for every integer $i$. For a Weil complex the same assertion applies to its underlying complex, as stipulated in that definition.

Uses: def-weil-ordinary-compact-cohomology.

## Checks and delivery

The required server dry run completed successfully at 8bc7ac08a25; its durable .stage1-ready.json receipt matches every input. The provider interruption lost the tool session after completion, so I checked the receipt and confirmed no deliver.py process remained before continuing. A final dry run follows the report update and the proof_origin correction (the blueprint proof is agent-written).
