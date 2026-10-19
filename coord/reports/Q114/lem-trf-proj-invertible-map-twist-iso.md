# Stage-1 delivery: lem-trf-proj-invertible-map-twist-iso

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-proj-invertible-map-twist-iso.json`: unchanged statement, six-step split, existing searches retained and actual new item searches added.
- `citations.json`: a verbatim statement quotation for every node used in every proof step.
- `report.md`: worker report and self-review. Sandbox preparation scripts and `searches.jsonl` are not DAG delivery files.

Zero new nodes, zero Mathlib leaves. No unit record was changed.

## Attachments

None. The exact item id/tag has no hit in either read-only project source tree. I additionally searched `WeilConjectures/` of slopmaster2 for invertible-map-into-proj, section-generation, Proj twists, and pullback comparisons, and read `AlgebraicGeometry/ProjectiveSpace/OfInvertible.lean` (especially lines 253–298). Its `exists_hom_twistRestrict` gives the polynomial projective-space construction, not this arbitrary graded-ring canonical comparison, uniqueness, and compatibility. `ProjectiveSpectrum/Twist/Modules.lean` has chart trivializations; those are ingredients, not an exact attachment for this item.

## WANTED

None. Both source tags are present locally.

## What needed repair or clarification

The imported item had no proof. The final split proves it directly from the existing localization definition of twisting sheaves, tensor pullback, section rings, and nonvanishing-section trivialization. Removed the unused quasi-compact-scheme and ample-invertible-module statement dependencies; no compactness or ampleness hypothesis occurs in the item and its statement is unchanged.

The first dry run refused the proposed new generated-chart node because of same-tag duplicates. On self-review I also found that it repeated the item's main clause (D1). I dropped that uncommitted draft entirely and replaced it with the explicit chart calculations now in Steps 1–6. There are no new nodes requiring a same-tag non-duplicate comparison. The initial report's product-degree shortcut was also replaced: Step 6 proves the actual multiplication square by arbitrary homogeneous fractions, without assuming that multiplication of twisting sheaves is invertible.

The preliminary srvcheck calls passed. The full dry run, including delivery preflight, will be repeated on this final version before pushing.

## What remains

The stage-1 split is complete. No new lemma is left unsplit. Existing prerequisite nodes retain their own states. No Lean was written, and no compiler, Lake, build tool, or direct git command was run. No other agent was started.

## Searches and blueprint

Read `coord/brief-stage1.md`, `roles/worker.md`, `stages/1-dag.md`, SETUP's three levels, GOAL, dag-sync, delivery-errors B–E, and the chapter/unit records. The item is a historical section-algebra/Proj helper under `lem-trf-local-term-locality`; its recorded ancestor and via chain are retained. This delivery elaborates that helper and changes no chapter, unit, trace, or purity route. The whole-blueprint searches for `generated-chart comparison` and `01NK` returned zero blueprint nodes. Searches of the whole DAG for both tags and the Proj/twist/section-ring terminology exposed the existing chart, section-ring numerator, and graded-sheaf nodes. I read those candidate statements; the final proof reuses the general graded-module sheaf and nonvanishing trivialization statements, and creates nothing.

Ran the required logged Mathlib searches for the item: LeanFinder, Loogle, grep, LeanSearch, and second semantic phrasings. Existing item searches were retained. Hits include `AlgebraicGeometry.Proj.fromOfGlobalSections`, `fromOfGlobalSections_morphismRestrict`, `pullbackAwayιIso`, and their chart identities; these construct scalar-function Proj maps or chart pullback squares and do not state the full invertible-sheaf result. The natural-language results were read. The grep commands reported zero hits. Loogle returned an unknown-identifier diagnostic, recorded as unavailable rather than evidence of absence. Searches run for discarded draft names are not represented as searches for a delivered new node.

## Not duplicates

No new node is delivered. The uncommitted generated-chart draft was removed because it repeated a clause of the item. Existing same-tag section-ring chart nodes are reused as reference material, not copied or edited.

## Review by Q114

I read Stacks `constructions.tex`, Tag 01NK (`lemma-invertible-map-into-proj`, lines 3217–3321) and Tag 01N8 (`lemma-converse-construction`, starting at line 2449), with the chart and uniqueness arguments open. Tag 01NK constructs the graded comparison by extending the graded section homomorphism after inverting a positive homogeneous element. Tag 01N8 identifies the degree-d comparison locally by sending the pulled-back basis f to its nonvanishing image section. I read the full statements of every node used below. The final item keeps arbitrary nonnegative grading, arbitrary schemes, positive d, and the specified open generation hypothesis; it never assumes the ring is generated in degree one or that O(1) is invertible globally.

Step 1 cites `def-weil-pbc-proj-twisting-sheaf` for chart sections `(A_f)_m`, localization restriction maps, and the section `b/1`; `def-sc-invertible-section-ring` for tensor multiplication and its preservation by psi; and `def-sc-section-generating-locus` for the local generator on T_s. These are exactly their statements. The step writes the definition of the canonical comparison already named by the item: extend psi by f^{-1} mapping to the inverse generator. It does not take an unstated twist-isomorphism conclusion from the existing generation-locus morphism node. Dividing by a power of the nonvanishing section is legitimate even when L itself is not trivial on that entire open. Only its e-th power needs the indicated generator.

Step 2 uses the invertible-module definition (locally free rank one), the tensor-product definition (tensor powers), and the generating-locus definition (nonvanishing equals local free generation). I checked the cover argument for the specified family psi(A_d), rather than substituting all global sections: the finite germwise expression of 1 forces some coefficient of this very family to be a unit. This proves that the W_a cover without compactness. A local basis of L tensor-powers to a basis of every positive power, so the trivialization used here needs no separate geometric lemma.

Step 3 cites the complete twisting-sheaf chart definition and `lem-weil-pbc-proj-graded-module-sheaf-exists`. The latter explicitly supplies g^N=ca when D_+(g) lies in D_+(a), plus the localization restriction maps and their composition. Thus a^{-1}=c/g^N is actually available in each such A_g. Multiplication by a and its inverse have degrees d and -d and identify degree-zero and degree-d parts. They commute with restriction. These are explicit inverse maps on a basis of opens, so the sheaf condition extends them uniquely; no affine-module comparison theorem or global invertibility of O(d) is silently used. The same definition's clause (3) says the global section a restricts to a/1, the required local basis.

Step 4 cites `def-pc-module-pullback` for the tensor formula and functoriality, and `lem-weil-pbc-nonvanishing-section-trivializes` for its exact isomorphism a ↦ a s on a nonvanishing open. The latter applies to the invertible module L tensor d, verified in Step 2. Pullback preserves the explicit inverse maps of Step 3; the displayed tensor/unitor formulas identify its basis with 1 tensor a. The image is psi(a) by Step 1. Thus the comparison is locally the identity in these bases, and the inverses glue because they invert the same sheaf map. This uses the theorem's actual statement, not a definition of nonvanishing standing in for trivialization.

Step 5 is elementary: on each W_a any O-linear map is determined by that single basis. The section-normalization hypothesis supplies equality on the basis; sheaf separation supplies global equality. It proves uniqueness among all comparisons, including comparisons not already known invertible.

Step 6 cites precisely the twisting-sheaf localization formula, section-ring tensor multiplication, tensor pullback, and sheaf tensor-product definition. The two routes on b/f^p tensor c/f^q both give psi(bc)/s_f^(p+q). Restriction and multiplication in A_f agree by the chart definition. Bilinear extension accounts for arbitrary pulled-back coefficients, and sheafification accounts for arbitrary sheaf sections. This checks the actual graded multiplication square for all nonnegative degrees on U(psi), then restricts it to any common generated open. It is stronger than a check only on the selected degree-d global generators, and does not need the false assumption that every Proj multiplication map is invertible.

I tested V empty, A_d zero, the zero ring, d=1, a nilpotent homogeneous element (its chart is empty), and a weighted grading with no degree-one generators. If A_d=0 the generating hypothesis forces V empty. Nilpotent sections create empty generating opens and do not invalidate the cover under its hypothesis. For A=k[t] with deg(t)=2, choosing d=2 gives the expected basis t while no assertion is made in degree one. The direct multiplication identity also works when the component theta_m is not an isomorphism. No finite-generation, Noetherian, ample, or quasi-compactness hypothesis is imported. The proof uses no SGA source, contains no cycle, and all six steps are below 2000 characters (largest: 1000). The two off-unit theorem uses are declared as generic tool uses in split_report. The other citations are definitions. Every quote in citations.json is copied verbatim from the current cited statement, and proof_deps is exactly the union of step uses.
