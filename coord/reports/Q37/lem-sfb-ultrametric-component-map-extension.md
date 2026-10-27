# Q37 stage-1 report: lem-sfb-ultrametric-component-map-extension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-component-map-extension.json`: item, statement unchanged, four complete proof steps, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-space-totally-disconnected.json`: new statement, Mathlib leaf. The general metric-space ultrametric instance gives total separation, with the inferred total-disconnectedness instance explicitly named and located.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-connected-component-lift.json`: new statement, Mathlib leaf. General arbitrary-space component factorization, uniqueness, and continuity/surjectivity of the quotient map; every matching declaration and line is identified.
- `citations.json`: one verbatim quotation for every citation in the item's numbered proof steps.
- `searches.jsonl`: actual searches logged by the prescribed msearch command; all successful.
- `write_split.py`: sandbox-only JSON writer, retained for reproducibility.

## Attachments

None. Searched the project under `lean/WeilConjectures/` by the exact blueprint tag, ultrametric/nonarchimedean terminology, and connected-component factorization. The existing project topology files give different results (for example component-map injectivity under connected-fiber assumptions). DenseOpenFunctions concerns locally finite functions and open embeddings; FieldCoefficient/ConstantSheaf defines coefficient functions. Neither states this item's arbitrary-space ring isomorphism with every clause. Mathlib declarations are recorded as leaves, not as project attachments.

## WANTED

None. All mathematical sources needed here are available locally.

## Findings and corrections

The sandbox initially held launcher markers only, with no item copy, report, or searches to reuse. The repository item was unsplit, with an empty proof and no released repair note. Its existing six Mathlib-search records are retained; fresh searches for the whole item were run and appended. Its statement and maintainer-owned metadata have been preserved.

Bhatt–Scholze Lemma 4.2.12, PDF printed p. 30, ends with the factorization of a continuous map to a totally disconnected target through connected components. Its statement is formulated for qcqs schemes. We do not apply that scheme assertion to arbitrary spaces: the cited general Mathlib connected-component lifting declarations have arbitrary topological source and target, and directly supply the generality this item needs. The ring inverse calculation and absolute-value specialization are marked agent-written.

The inherited blueprint ancestor is null: `python3 tools/blueprint_refs.py ancestor lem-sfb-ultrametric-component-map-extension` explicitly printed None. The inherited via chain and non-unspecified place are retained. New leaves inherit the same ancestor and prepend this item to the via chain. The source obligation is the all-continuous component restriction in det-thm-sf-ctf-stability-direct-images paragraph (3), as realized by the parent normal-generic-continuous-sections proof step 3. This changes no chapter or unit route and requires no unit realization edit.

No statement dispute or source error was found. Nothing remains mathematically unfinished. No Lean was written, no compiler/build/Lake command was run, and no repository or launcher file was written or git command run there.

## Not duplicates

lem-sfb-ultrametric-space-totally-disconnected vs lem-sfb-ultrametric-criterion-natural-norms: the existing leaf characterizes when a field norm is ultrametric by natural-number norms; it gives no total separation or total disconnectedness. The new leaf assumes an ultrametric on an arbitrary metric space and gives these topological conclusions.

lem-sfb-continuous-connected-component-lift vs lem-sfb-component-quotient-clopen-naturality: the existing statement gives the induced map between component quotients and a clopen pullback bijection, not the lift of an arbitrary continuous function into an arbitrary totally disconnected target. It does not replace the new general factorization theorem.

lem-sfb-continuous-connected-component-lift vs lem-sfb-spectral-clopen-component-homeomorphism: that existing result assumes spectral spaces and a clopen pullback bijection and concludes a component homeomorphism; the new leaf needs no spectral hypothesis and factors maps to arbitrary totally disconnected spaces.

lem-sfb-continuous-connected-component-lift vs lem-weil-pbc-condensed-field-continuous-realization: the existing statement identifies coefficient ring sheaves on a scheme, not arbitrary-space continuous maps through their component quotient.

lem-sfb-continuous-connected-component-lift vs lem-zl-affine-component-site-projection: the existing statement constructs a geometric morphism and evaluates inverse-image sheaves under a split-cover condition. It does not state arbitrary-space continuous factorization.

lem-sfb-ultrametric-space-totally-disconnected vs lem-sfb-ultrametric-component-map-extension: the new leaf is a general metric-space tool, with no field, continuous-function ring, component-homeomorphism hypothesis, precomposition map, or extension operator. It is an exact Mathlib result, rather than moving this item's proof to another unsplit node.

lem-sfb-continuous-connected-component-lift vs lem-sfb-ultrametric-component-map-extension: the new leaf is a general topological universal property for any totally disconnected target. It has no field or ring structure and no comparison between two spaces or inverse operator. The item retains the actual argument that the restriction map is a ring isomorphism with the stated inverse.

The whole DAG was searched by the pertinent Mathlib declarations and by statement concepts. The candidate statements above were opened and read, as were the profinite-component-ring-pullback and profinite-sections-finite-quotient statements, which concern different algebraic/site constructions. Blueprint searches for connected component, totally disconnected, ultrametric, connectedComponentsLift, and totally separated found no equivalent statement, so same_as is empty. Neither new source claims a Stacks tag; there are no same-tag pairs to distinguish.

## Review by Q37

I read AGENTS.md, the worker brief and role, stage 1, GOAL.md, the three levels in SETUP.md, the chapter and assigned unit records, and delivery-errors B–E in both copies. I read the actual last paragraph of Bhatt–Scholze Lemma 4.2.12 using pdftotext and compared its qcqs-scheme setting with this item's broader hypothesis. I also read the parent normal-generic-continuous-sections statement and its component-extension step to check the required direction of the map. The item asks for the actual restriction along i; no topological equivalence of Y and Z is assumed.

For the ultrametric-space leaf I read Mathlib/Topology/MetricSpace/Ultra/TotallySeparated.lean, especially line 25 and the inferInstance example at line 32, and Mathlib/Topology/Connected/TotallyDisconnected.lean lines 208–220. The first named instance assumes MetricSpace and IsUltrametricDist and gives total separation. The second named instance at 218 infers total disconnectedness with no extra hypothesis. This is an allowed Mathlib-leaf instance chain, with both declarations, files, and lines recorded. I did not generalize to pseudometrics: a pseudometric with distinct points at zero distance would invalidate the conclusion. Empty metric spaces, a singleton, a two-point discrete metric, and the trivial absolute value are included without a hidden nonempty assumption.

For the component-lift leaf I read TotallyDisconnected.lean lines 243–279 and Clopen.lean lines 515–546. The former constructs the lift, proves its continuity and composite identity, and proves uniqueness without assuming the competing factor continuous; the latter gives the precise connected-component quotient, its quotient topology, and the surjective/continuous quotient map. Its target hypothesis is total disconnectedness only, not Hausdorffness, compactness, local connectedness, or discreteness. A quotient of the empty space is empty; functions from it factor uniquely. No replacement of connected components by quasi-components or of continuous by locally constant functions occurs.

Step 1 uses exactly the metric leaf's displayed ultrametric hypothesis and topological conclusion, quoted in citations.json. The equality a-c=(a-b)+(b-c) verifies that hypothesis for the supplied genuine metric on A; there is no need to construct an equivalent absolute value or to assume completeness.

Step 2 uses exactly the component-lift leaf's factorization, continuity, and uniqueness statements, all quoted verbatim. Step 1 supplies the sole target hypothesis. The source can be Y or Z without a compactness or spectral assumption. The same leaf explicitly supplies continuity and surjectivity of the quotient map, so no unquoted quotient theorem is hidden in the later composition.

Step 3 is elementary and cites no theorem: the ultrametric inequality proves continuity of addition, the metric proves continuity of negation, and the displayed epsilon/delta estimate proves continuity of multiplication. The bound M=1+|x|+|y| is positive, including zero coordinates. With delta<min(1,epsilon/M), the two product-difference terms are both strictly below epsilon. Pointwise ring laws and preservation by precomposition are evaluated directly. Thus no separate general topological-ring or ring-homomorphism lemma is being smuggled in.

Step 4 uses results proved in steps 2 and 3 and the given homeomorphism equation. I checked the two directions separately: h^{-1}h proves i^*E_i=id; uniqueness applied to bar(g)h proves E_i i^*=id. The homeomorphism direction is pi_0(Y) to pi_0(Z), so the inverse formula has the right domain. The inverse ring-map equations follow by the injectivity just proved. Empty Y forces empty Z by surjectivity of the quotient map and bijectivity of h, so both function rings are the one-element ring; rings are not silently required to be nontrivial. With the trivial absolute value the metric is discrete and every calculation remains valid. The argument also covers noncompact spaces and incomplete nonarchimedean fields.

I checked B1–B10: the new leaves contain statements only and no proof; every object and relevant notion is introduced; TeX uses ordinary single escapes in parsed strings; source attribution does not invent a Stacks tag; all match clauses have real source lines; every recorded search was actually run. For C1–C8 I checked every used statement and verbatim quote, no use of a cited node's proof, no dependency back to the item, and no off-route unsplit tool. For D1–D5 the item retains the inverse and ring arguments and the leaves are strictly more general exact Mathlib tools. For E1–E7 I checked every hypothesis, small cases, actual maps, and explicitly wrote the compatibility equations. Every step is under 2000 characters; none hides a long inline comparison lemma. There was no previous sandbox proof to preserve and no mathematical correction to the item statement was needed.

## Validation

The initial required server dry run rejected the two leaves because neither statement cited a definition node. I read def-weil-size-convention in full and explicitly adopted its containing-universe convention in each new statement and stmt_deps, for the spaces, component quotients and function sets. This is a metatheoretic convention, not a compactness or separation hypothesis. The universe-polymorphic Mathlib declarations already have this generality; their mathematical search questions and matches are unchanged. The verbatim quotes were refreshed. The corrected server dry run and push follow.
