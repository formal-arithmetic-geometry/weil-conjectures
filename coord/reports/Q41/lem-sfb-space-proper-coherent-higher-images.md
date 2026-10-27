# Stage-1 delivery: lem-sfb-space-proper-coherent-higher-images

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-coherent-higher-images.json`: item, split into six steps; its statement and statement dependencies are unchanged.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-coherent-two-of-three-devissage.json`: statement, unsplit, no Mathlib match. Tag 08AN, with the zero-object case explicit.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-chow-acyclic-full-support-witness.json`: statement, unsplit, no Mathlib match. The existential Chow-twist construction in the proof of Tag 08AR, including its genuine scheme theoretic support and acyclicity requirements.
- `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-topos-relative-leray.json`: statement, unsplit, no Mathlib match. Tag 0734 for module sheaves and arbitrary ringed-topos morphisms.
- `dag/nodes/sec-six-functors-basics/lem-sfb-space-affine-module-higher-image-vanishing.json`: statement, unsplit, no Mathlib match. Tag 073H in module sheaves, not only after forgetting scalars.
- `citations.json`: every proof-step citation, with a verbatim quote of the cited statement.

## Attachments

None. The exact blueprint tag has no declaration under `lean/WeilConjectures/`. Concept searches found DirectImageBoundedCoherent, ProperSupportHigherDirectImageBound, GradedCohomologyModuleFinite and the scheme ChowTwistFiniteCohomology construction. They concern schemes and their Zariski module categories, not the algebraic-space small-etale assertion. No Mathlib declaration is represented as a project attachment.

## WANTED

None. All sources needed here are present as Stacks TeX. No SGA source is used.

## Findings and corrections

The item was an unsplit supporting node with no earlier sandbox attempt. I retained its statement, inherited blueprint fields, and earlier Mathlib searches, and appended the searches actually run for Q41. `tools/blueprint_refs.py ancestor` returns None; the inherited null ancestor, exact place and via chain are retained. The newest blueprint direct-images proof (3) retains the compactification/proper/open route; the present coherent-finiteness tool remains below the inherited alteration and moduli prerequisites and replaces no unit-level step. This is not the key statement of the unit, so no unit realized field is changed.

## Source error

STATEMENT-DISPUTED (auxiliary source edge case, not the item): as literally printed, Tag 08AN does not require P(0). On the empty Noetherian algebraic space, P constantly false satisfies its first two implications and its integral-subspace condition vacuously, but its conclusion is false for the zero coherent module. The new devissage statement explicitly assumes P(0). The property used in this item satisfies it, so no hypothesis or conclusion of the assigned theorem changes. Nonempty irreducible subspaces are required explicitly. Also the closing stalk paragraph of 08AR writes g' where its maps to Z must be pi, and the displayed graph arrow omits its source. The new witness states the correctly typed pi and (j,pi) diagram and zero annihilator directly.

## Not duplicates

lem-sfb-space-coherent-two-of-three-devissage vs lem-sfb-space-coherent-devissage: Tag 08AN uses two-out-of-three and one module of exactly each integral scheme theoretic support. The existing Tag 07UT uses extension closure and a module permitting submodule choices inside every nonzero ideal; that extra idealwise input is not provided by the witness used here.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-sfb-space-proper-coherent-higher-images: both mention 08AR, but the new node is the existential projective-twist witness for one integral proper space, with vanishing positive images and zero annihilator. The item asserts coherence of all higher images of every coherent module on arbitrary proper maps. The item carries the devissage and localization argument itself.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-sfb-proper-space-coherent-derived-image: that existing same-tag citation uses 08AR to treat every cohomology sheaf in a bounded-below complex. The new node only constructs one acyclic faithful sheaf and its projective cover, strictly below that universal assertion.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-pc-q2-chow-twist-finite-cohomology: the existing statement assumes a specified scheme diagram and concludes finite global cohomology, with neither surjectivity nor full support. The new statement is for possibly nonschematic integral algebraic spaces, gives the cover, zero annihilator and higher-image vanishing. Neither statement is a one-line application of the other.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-pc-chow-relative-ample-twist: that is scheme-only relative ampleness for an already specified diagram, not existence of a faithful acyclic module on a space.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-sfb-space-weak-chow: the existing node supplies a proper surjective quasiprojective scheme cover only; it supplies neither coherent twist pushforward, acyclicity nor annihilator control. The new witness is the smaller analytic input obtained from this cover and simultaneous Serre vanishing.

lem-sfb-ringed-topos-relative-leray vs lem-sfb-ringed-site-leray-spectral-sequence: the existing node has global cohomology as its target; the new node has an arbitrary second module direct image and a sheaf-valued abutment.

lem-sfb-ringed-topos-relative-leray vs sk-thm-groth-ss: its general abstract statement assumes injective-to-acyclic compatibility, and its unconditional relative-site specialization is for abelian sheaves. The new node supplies the unconditional module statement for arbitrary structural ring maps; tensor pullback need not be exact, so that compatibility is an actual theorem, not an inferred instance.

lem-sfb-ringed-topos-relative-leray vs det-thm-groth-ss: the same distinction holds for this duplicate imported formulation: it does not unconditionally supply relative module Leray for ringed topoi.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sfb-space-affine-higher-direct-image-vanishing: both use 073H, but the existing node explicitly derives direct image in abelian sheaves of the underlying module. The new node derives direct image in the categories of structure-modules. Comparing the two is nontrivial for nonflat structural ring maps; it is not an elementary relabelling or a constant-coefficient specialization.

lem-sfb-ringed-topos-relative-leray vs lem-sp-cartan-eilenberg-comparison-independence: the existing statement proves independence of comparison maps between chosen Cartan–Eilenberg presentations; it does not establish relative module direct-image acyclicity or the ringed-topos Leray theorem.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-acyclic-abutment: the existing abstract abutment statement assumes the injective-to-acyclic compatibility; the new ringed-topos statement establishes the applicable module theorem without that extra hypothesis.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-acyclic-augmentation: the existing augmentation statement assumes an abstract acyclic composite-functor setup; it does not supply that setup for arbitrary structural ring maps.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-augmentation-comparison: the existing statement compares augmentations in an abstract Cartan–Eilenberg model under acyclicity assumptions, rather than establishing relative module Leray for ringed topoi.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-decalage-injective-model: the existing statement constructs injective models for shifted truncations; it does not assert the relative direct-image spectral sequence or its module acyclicity input.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-decalage-truncation-diagram: the existing statement identifies truncation diagrams in an abstract Cartan–Eilenberg model, not the unconditional relative module direct-image theorem.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-good-cut-identification: the existing statement identifies good cuts and filtered models; it does not supply injective-to-acyclic compatibility for ringed-topos module direct images.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-page-realization: the existing statement realizes pages for derived composites of abstract left exact functors; it does not identify the abutment with the derived underived composite without the acyclicity input needed here.

lem-sfb-ringed-topos-relative-leray vs lem-sp-ce-second-image-truncation: the existing statement identifies second-image truncations in a Cartan–Eilenberg model; it does not establish module direct-image Leray or the ringed-topos acyclicity hypothesis.

lem-sfb-ringed-topos-relative-leray vs lem-sp-grothendieck-canonical-image-filtration: the existing statement identifies the canonical filtration for an abstract pair already satisfying injective-to-acyclic compatibility; it does not prove compatibility for arbitrary ringed-topos maps.

lem-sfb-ringed-topos-relative-leray vs thm-sp-grothendieck: the existing general theorem explicitly assumes that the first functor sends injectives to objects acyclic for the second. The new statement supplies the relative module theorem for arbitrary ringed-topos maps, where this compatibility needs proof because tensor inverse image need not be exact.

lem-sfb-ringed-topos-relative-leray vs def-sc-spectral-object-bottom-page-map: the existing node defines a bottom-page map for an already supplied spectral object; it proves neither the existence nor the module acyclicity of relative Leray.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-pqf-open-module-cohomology-comparison: the existing node compares global module and additive cohomology on scheme opens; the new node asserts vanishing of module higher direct images for affine algebraic-space morphisms.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-module-cup-flasque-acyclicity: the existing node gives global module acyclicity for a module with flasque underlying sheaf on a scheme; it does not give relative affine quasi-coherent acyclicity on algebraic spaces.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-picard-external-cup-scalar-comparison: the existing node concerns degree-one external cup and scalar comparison maps over fields, not higher module direct-image vanishing for affine spaces.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-picard-external-cup-unit-comparison: the existing node identifies external cup unit comparison maps, not higher module direct-image vanishing for affine spaces.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-scalar-unit-cohomology-pullback-comparison: the existing node concerns compatibility of degree-one unit/scalar cohomology with scheme pullback, not relative affine module acyclicity.

lem-sfb-space-affine-module-higher-image-vanishing vs new-picard-derived-fibre-naturality: the existing node concerns degree-one derived fibre comparisons in proper flat scheme families with invertible modules; the new node treats arbitrary quasi-coherent modules under affine algebraic-space maps.

lem-sfb-space-affine-module-higher-image-vanishing vs new-sc-scalar-abelian-ext-factorization: the existing node factors a degree-one scalar Ext map for scheme cohomology; it gives no affine higher direct-image vanishing.

lem-sfb-space-affine-module-higher-image-vanishing vs new-sc-scalar-unit-comparison-family: the existing node gives degree-one scalar/unit comparison bijections on schemes, not relative affine module vanishing.

lem-sfb-space-affine-module-higher-image-vanishing vs new-sc-scalar-unit-pullback-naturality: the existing node gives naturality of field-scheme degree-one scalar comparisons under pullback; it gives no relative affine vanishing theorem.

lem-sfb-space-affine-module-higher-image-vanishing vs def-sc-topological-abelian-cohomology: the existing node defines topological-space abelian cohomology; it does not state an algebraic-space module direct-image vanishing result.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-additive-cohomology-scalar-comparison: the existing node gives degree-one scalar-compatible additive comparison for a separated finite-type curve; it does not treat affine module higher direct images.

lem-sfb-space-affine-module-higher-image-vanishing vs lem-sc-etale-qcoherent-source-comparison-natural: the existing node compares etale and Zariski global quasi-coherent cohomology on a qc separated scheme and its endomorphisms; it does not state module higher-image vanishing for affine maps of spaces.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-pc-m1-projective-pushforward-finite-type-independent: the existing node proves degree-zero finite-type pushforward for an already supplied projective scheme embedding and finitely presented module; it supplies neither a cover of a space, a faithful twist, nor positive-image vanishing.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-sfb-space-chow-configuration: the existing node constructs the distinct-tuples Chow configuration and its auxiliary open from an etale atlas; it supplies no coherent faithful acyclic twist module on the given integral proper space.

lem-sfb-space-chow-acyclic-full-support-witness vs lem-sfb-space-etale-maximum-degree: the existing node bounds atlas degrees and isolates the maximal-degree open with lower-degree boundary; it supplies neither the projective cover nor the full-support acyclic coherent sheaf.

## Review by Q41

I read spaces-cohomology.tex Tag 08AR in full, its coherence conventions 07UB, closure lemmas 07UC/07UD, the actual statement and proof of 08AN, weak Chow 089J, and twisting 08AQ. For the new Leray node I read sites-cohomology.tex 0734 and its injective-to-acyclic explanation, rather than assuming module inverse image is exact. For affine module acyclicity I read 073H, its representable chart reduction, and the module/additive cohomology comparison 03FD. For the witness I checked the two projective embeddings, simultaneous large twists, projective finiteness in coherent.tex 02O4, and the nonzero-section argument giving full support. The unsplit witness deliberately states those obligations rather than hiding them in an elementary step or giving it a proof dependency on the assigned item. Its future split must use projective degree-zero finiteness on etale charts to establish coherence of pi_*L^d, not invoke 08AR circularly.

Step 1 uses the exact scheme locally-Noetherian finite-type theorem pqf-lem-locnoeth-lft on charts, not on a nonschematic space. Fibre-product existence, proper base change and module higher-image etale restriction are each supplied by their cited statements. Properness gives quasi-compactness; closed scheme-test diagonals are affine, hence quasi-compact, so over the affine base the source is quasi-separated. Together with the chart calculation this supplies all three Noetherian conditions. Chartwise coherence is already the explicit convention of the item, so its descent does not silently assume global Noetherianity of Y.

Step 2 checks enough injectives using the ringed-site Grothendieck node and the enough-injectives node. The derived-functor long-exact statement applies to this additive left exact direct image. The higher-image quasi-coherence node says exactly that all of its terms are quasi-coherent for qcqs f. The kernels/colimits node supplies quasi-coherent images, the support/subquotient node supplies coherent subobjects and quotients, and the coherent-abelian node supplies extensions. Thus the long exact sequence really proves every case of two-out-of-three, including its initial zero, rather than misusing closure under kernels of arbitrary noncoherent modules.

Step 3 writes the coordinatewise injectivity and finite-sum resolution argument. Summand closure is realized as a kernel of an idempotent between coherent modules, exactly what the cited coherent-abelian statement supplies. This elementary step introduces no extra general lemma and assumes r >= 1 as required by the devissage node.

Step 4 checks g is proper by the exact closed-subspace-proper and proper-composition statements. The new witness is used only after reducedness, nonempty irreducibility and an affine Noetherian target have been obtained. It gives one specific coherent full-support module G, its zero annihilator, coherent degree-zero image and zero positive images; no clause is borrowed from the proof of a cited node.

Step 5 uses the closed-coherent node only for coherence, not for an unstated derived assertion. Affineness is checked on the actual closed scheme tests. The new module-affine vanishing statement provides the needed module R^q i_*, unlike the older abelian version. Relative module Leray has exactly the composable ringed-topos objects required; a sole surviving row gives one graded piece in each finite abutment filtration. Finally the closed-module essential image and quotient ring statements identify the annihilator: a local class acts as zero precisely when its class on Z acts as zero on the faithful G. This establishes scheme theoretic, not merely topological, support.

Step 6 applies precisely the stated new two-out-of-three devissage theorem after verifying P(0), isomorphism invariance, the positive finite-sum implication and its witness for every integral closed subspace. It then uses Step 1's chart reduction. I checked that the existing 07UT statement cannot be substituted here without its additional idealwise hypothesis.

I tested the item and new nodes on the empty space, zero sheaf, identity and closed-immersion maps, an integral point, and projective space over a field. The devissage zero hypothesis repairs the empty-space failure. The witness excludes the empty integral space but allows zero-dimensional and finite proper spaces; d=0 and pi the identity are consistent there. It does not assume that Z is itself a scheme, that pi is birational, that A is a field or reduced, or that g is flat. The relative Leray assertion is only first-quadrant module Leray, not unbounded convergence. Affine module acyclicity includes identity maps and empty sources and asserts no underived exactness on all modules.

DAG, blueprint and source searches were performed before writing nodes, including exact tags 08AN, 08AQ, 08AR, 0734, 073H and the conceptual searches recorded above. The Mathlib queries and original results are retained in searches.jsonl and the per-node search-results files; each new node includes the literal output of its five executed queries. Hits were read: module pushforwardComp is underived, Noetherian and proper instances concern schemes, and the Tilde.lean grep hits at 567 and 587 concern underived quasi-coherence. None is an exact or one-line match, so there are zero new Mathlib leaves. The unused exploratory forget-comparison searches created no node. All six proof steps are below 2000 characters; no long step hides a standalone argument. Every cited statement was opened and copied verbatim to citations.json. Generic off-unit tools are declared in split_report.tool_uses; no maintainer-owned tool_uses field was written. I wrote no Lean, ran no compiler and made no repository or launcher edits.

## Unfinished work

None for this one-level stage-1 split. The four new nodes are intentionally statement-only and unsplit, as required. The server review_split check passed. The first dry run requested additional same-tag statement comparisons; I opened every flagged statement and recorded every pair above before rerunning. The final dry run and push are recorded by the delivery command.
