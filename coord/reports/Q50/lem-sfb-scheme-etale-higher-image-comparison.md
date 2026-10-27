# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-etale-higher-image-comparison.json: split, statement unchanged, five steps following Stacks 071N.
- dag/nodes/sec-six-functors-basics/lem-sfb-qcoh-cohomology-etale-pullback-naturality.json: statement, unsplit, no Mathlib match. This is a functoriality assertion for ordinary quasi-coherent cohomology, independent of the morphism f and its higher images.
- citations.json: one verbatim statement quotation for every use in every item step.
- report.md: this report. Search outputs and the exact msearch.py search log are retained in the sandbox.

## Attachments

None. Searched the project for the exact blueprint tag and by etale/Zariski, quasi-coherent, and higher-image concepts. The available EtaleZariskiQcohComparison and OrdinaryHigherImageQuasiCoherent declarations supply different inputs, not the entire item. No exact project attachment was found.

## Wanted literature

None. All sources needed for this split are present under literature/stacks-project/.

## Corrections and scope

The item's statement is faithful to descent.tex Tag 071N, lemma-higher-direct-images-small-etale. No statement correction or STATEMENT-DISPUTED is needed. The empty proof was replaced. The inherited source correctly concerns all structure-sheaf modules, not constant coefficient modules. I did not use the constant-coefficient module-forgetting nodes as a replacement for this assertion.

The chapter/unit records have a historical mismatch: the item has chapter sec-six-functors-basics, whereas dag/units/sk-thm-sf-ctf-stability.json names sec-six-functors. I read the current blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and direct-images.proof.md as well as the records. The latest proof (3) uses compactification and no longer explicitly spells out the inherited alteration route. This item is an already-created supporting coherent-cohomology comparison; it does not replace a unit step. blueprint_refs.py ancestor returns None, matching the inherited null ancestor. The inherited from/via history is retained and the new node extends that chain.

A potential new affine-evaluation node was rejected: quasi-coherence + affine vanishing + the existing unrestricted Leray edge statement give the required qcqs version immediately. The existing lem-pc-cohomology-sections-affine-base has separatedness, so it was not cited. A potential generic ringed higher-image-presheaf node was also rejected: the quotient-of-cocycles computation takes a few lines from definitions and the existing module sheafification interface. Its computation appears in Step 2.

## Unfinished work

The one new node is intentionally statement-only; it joins the stage-1 queue. Its missing input is compatibility of the canonical comparison with etale pullback, not a new existence assertion for higher-image comparison. No Lean was written or compiled. No agents were started.

## Review by Q50

I read descent.tex 071N in full, including its references to 01XJ, 01XK, 02KH, 03DW and 072W; coherent.tex's quasi-coherence lemma, affine-base Leray application and flat-base-change lemma; sites-cohomology.tex's explicit injective-resolution proof of 072W and its module/abelian comparison 03FD; and descent.tex's 03DW and pullback clause of 03LC. The new node isolates the functoriality implicit in treating the source's objectwise comparisons as a presheaf comparison. Its prospective proof is to take the canonical ringed-site comparison, use the commuting Zariski/etale restriction square and its pullback comparison, and apply functorial derived sections. Scalar linearity follows by applying naturality to multiplication by each global function. This argument is recorded here, not inserted into the unsplit node's statement or proof fields.

In Step 1, the equivalence node really gives the inverse by open restriction and the comparison for pullback along every scheme morphism. Only its unrestricted pullback and equivalence clauses are used; its separated pushforward clause is not used. lem-pc-finite-support-hi clause (1) gives quasi-coherence for exactly qcqs f; its compact-base clauses (2),(3) are not invoked.

In Step 2, def-trf-space-etale-module-functors gives the specified chart-limit direct image. For schemes X_U is itself the terminal chart, so the limit/evaluation identification is the universal-property calculation written in the step. The sheafification-interface node gives the module structure and linear universal map. The slice comparison node gives derived evaluation versus abelian cohomology on the localized site, and the separate ringed-site module/abelian evaluation comparison gives the module interpretation there. I corrected the draft to cite both; the former alone did not say module cohomology on the slice. The etale localization node supplies the site equivalence. The restricted rings agree objectwise, so no separate ringed equivalence is assumed without explanation. A common larger universe makes the chosen small presentations and coefficients small; enough injectives is already part of the stipulated computation.

Step 3 uses the new node exactly for its etale-pullback equation and scalar compatibility. The existing 03DW node only claims naturality in module morphisms on a fixed scheme, so it would not justify this step alone. The equivalence supplies the coefficient identification and its preservation of quasi-coherence. Morphisms between objects of X_et are etale by the localization-site description; no arbitrary scheme map is asserted etale.

For Step 4, qcqs-morphism-permanence clause (3) applies to any base change, not just affine or field extensions. The higher-image quasi-coherence node applies to p_U. Affine vanishing and unrestricted Leray then give the edge isomorphism for qcqs p_U, without assuming separatedness. Flatness of g is a clause of the etale definition. The existing flat-base-change node explicitly states the sheaf-level comparison g* R^q f* F -> R^q p_U* a_U* F; I use this clause, not only its affine-ring consequence. The associated-module equivalence's section formula identifies its sections with the target sheaf's value.

In Step 5, I added the existing flat-base-change-map-sections node after checking that an assertion of vague compatibility would hide the essential morphism. It identifies the adjoint of base change with cohomology pullback on represented classes and is independent of lifts. Flatness of the second projections is supplied by the existing flat-base-change node for morphisms. Applying the class formula to two maps and their composite proves the displayed equation by composition of pullback cochains. The rest is elementary sheaf gluing using the affine-open-basis node: overlaps need not be affine, because equality is checked on their affine open covers. No false intersection-closed affine basis is used. The source only requires a sheafified presheaf, so I do not identify arbitrary raw presheaf sections with higher-image sections.

Every proof use has a quote in citations.json copied verbatim from the cited statement. Generic off-unit tools are declared in split_report.tool_uses. I reviewed every step against C1 and C4, and B--E against the actual JSON. All steps are below 2000 characters; no long-step lemma is hidden. The only elementary-marked step is the explicit resolution/quotient calculation in Step 2. I did not create nodes for that calculation or for combining the existing Leray inputs.

Edge cases checked: q=0 gives ordinary flat base change and the identity-normalized equivalence; M=0 gives zero on both sides; X or U empty gives zero groups and the empty-cover sheaf condition; no quasi-compactness of Y is introduced; non-separated qcqs morphisms are allowed throughout; arbitrary etale objects need not be affine or quasi-compact, since the final comparison uses their affine open covers. The new node holds for any scheme Z and etale a, with no noetherian, field, dimension, or separatedness hypothesis. It specializes in degree zero to pullback/restriction of sections. It is not a clause of the item's higher-direct-image statement: it compares cohomology of varying schemes and gives the restriction square that the assembly needs.

Mathlib searches were run through msearch.py, twice with different semantic phrasings, plus Loogle, grep and LeanSearch. I read all returned hits. Mathlib's cohomologyPresheaf (Sites/SheafCohomology/Basic.lean, lines 65--89 read) defines abelian Ext-valued presheaves, not this ringed-site topology comparison. The other hits give underived pushforward/pullback, scheme section naturality or topology relations; none proves the new node. Search records retain the exact query and full returned results. Queries for the two rejected candidate nodes remain in the log, without creating those nodes.

## Not duplicates

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-trf-zariski-etale-functor-comparison-square: this existing node compares underived functors and degree-zero direct image; it does not compare positive cohomology or give its etale-pullback square.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-trf-scheme-zariski-etale-quasi-coherent-equivalence: this existing node supplies the underived module equivalence and pullback identification, not naturality of cohomology under etale pullback.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-trf-etale-line-sections-normalized-comparisons: this existing node normalizes sections and restriction for line modules; the new node concerns all quasi-coherent modules and all cohomological degrees.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-trf-scheme-etale-invertible-comparison: this existing node is the underived equivalence for invertible modules, not the comparison on higher cohomology.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sfb-scheme-etale-higher-image-comparison: the item compares higher-image sheaves for a qcqs map f; the new node concerns the canonical global-cohomology comparison and its restriction square for an etale map, with no f or higher-image assertion.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-zariski-qcoh-comparison: this node is explicitly natural in module maps on a fixed scheme; the new node adds the equation for an etale map between schemes and makes the module-linear restriction comparison explicit.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-tensor-positive-direct-image-vanishing: this existing node asserts vanishing of positive images for restriction to opens, not the canonical cohomology pullback square.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-zariski-abelian-positive-comparison: this existing node gives positive-degree additive comparison natural in module maps at a fixed scheme; it does not assert etale-pullback compatibility.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-qcoherent-cohomology-ulift: this existing node changes the coefficient universe for qc separated schemes and states no Zariski/etale pullback square.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-qcoherent-ulift-finite-cech-comparison: this existing node computes lifted positive etale cohomology by a finite Cech complex on separated schemes, without the varying-scheme restriction equation.

lem-sfb-qcoh-cohomology-etale-pullback-naturality vs lem-sc-etale-tensor-direct-image-identification: this existing node is an underived additive sheaf identification on open sections, making no cohomological assertion.
