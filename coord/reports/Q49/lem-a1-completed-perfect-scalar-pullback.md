# Stage-1 repair: completed perfect scalar pullback

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-completed-perfect-scalar-pullback.json`: existing statement, unchanged; split into a short assembly.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-adic-scalar-flat-reduction-model.json`: statement, `unsplit`; five actually executed searches, no full Mathlib match. No proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-projective-quotient-augmentation.json`: statement, `unsplit`; five actually executed searches, no full Mathlib match. No proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-constant-complex-strict-base-change.json`: statement, `unsplit`; five actually executed searches, no full Mathlib match. No proof steps or proof dependencies.
- `dag/nodes/sec-deligne-laumon-a1/lem-a1-completed-scalar-exact-base-change.json`: statement, `unsplit`; five actually executed searches, no full Mathlib match. No proof steps or proof dependencies.

## Attachments

None. I searched the project under `lean/WeilConjectures/` for the item tag and scalar-complex notion. No declaration there states the whole item. The supplementary `lean/Sheaf/Paper/CompletedPerfectScalarPullback.lean` has `completedPerfectScalarPullback` at line 951 with `sorry` at line 955. Its `modelModules_exact` at line 298 also has `sorry`; its finished helper calculations are useful source material, not an attachment of the item.

## WANTED

None. I read the local Bhatt–Scholze PDF (extracted into this sandbox) and the cited Stacks TeX sources; no source was downloaded.

## Repair and scope

The repair order in `coord/repair-notes/lem-a1-completed-perfect-scalar-pullback.json` is released stage 1 and preserves the old plan. The sandbox initially contained only `.brief*` markers, no nodes, report or search log, and no delivery process was running. I copied the current returned node into the sandbox and retained the complete original JSON as `returned-original.json`. The live statement, statement dependencies, imported metadata, chapter and unit are unchanged. The assembly proof is 1952 characters, below the 3000-character bound, and this delivery adds four comparable tasks. No Lean, compiler, Lake, repository writes or direct git commands were used.

The new tasks expose real independent work, rather than a rename of the full theorem: (A) coefficient datum, K-flat model and finite-reduction normalization; (B) canonical augmentation and completeness, including its contractible cokernel and projection normalization; (C) compatibility of geometric inverse image with the entire strict finite tower; (D) exact completed scalar realization and ordinary pullback for arbitrary scalar modules. Only assembling the specified integral pullback and transferring a vanishing interval remain in the parent. A later worker can work on any one of these four without waiting for proofs of the other three; all have statement-only deliveries.

## Review by Q49

I read the parent, its released repair note, the chapter and unit records and the relevant current blueprint ancestor. This is the scalar-model subargument used in the finite-etale fibre/purity branch, not a new route for the affine-line estimate. The chapter is fixed and the unit is not the item's key node, so no unit binding was edited. I read delivery-errors B–E, including the duplicate and citation examples, against the actual node files.

For A I read Stacks `sites-modules.tex`, lemma-completion-flat (093M), `sites-cohomology.tex`, lemma-bounded-flat-K-flat (06YQ) and lemma-pullback-K-flat (0G7E), plus the model_good and derivedReductionIso interfaces in the existing Lean module. The DVR and finite-residue statements, finite quotient lemma, adic datum, independent-universe local flatness/K-flat change-of-rings statements were opened. The pi-power map is injective because R is a domain and pi is nonzero; ell=u*pi^e with e positive ensures each quotient is ell-power torsion. Finite-projective splittings are asserted in each degree only: they need not commute with the differential. The normalized balancing map, its inverse, differential compatibility and unit compatibility are explicit theorem obligations in A, not something claimed from a generic K-flat definition. A does not assert invertibility of a coefficient pullback map.

For B I read Stacks `sites-cohomology.tex`, lemma-derived-limit-is-ok (0941), `proetale.tex`, proposition-enough-weakly-contractibles (099Q), and Bhatt–Scholze Proposition 6.6.11 and its proof. The PDF's global stratification equivalence assumes a topologically Noetherian scheme, and Lemma 6.5.9 is stated for qcqs schemes. I do not apply either global statement to arbitrary schemes. The retained proof uses the existing local perfect-model completeness theorem, the Roos/intrinsic equivalence and the explicit pro-etale quotient-cone computation, all of whose statements impose no scheme finiteness hypothesis. I opened the finite-perfect coefficient-limit, epimorphic tower, exact countable products and normalized strict Roos comparison nodes. B asks for the actual quotient augmentation, not merely an arbitrary isomorphism with some derived limit. Its cokernel is the shifted cone of the identity, with the cone sign fixed consistently; this is where invertibility is proved, and the normalized strict comparison is where its projections are proved. The degreewise finite-free retract and all original projection data are part of B's statement.

For C I read Stacks `sites-modules.tex`, lemma-tensor-product-pullback (03EL), the geometric constant-module inverse-image statement and the exact finite-constant pullback statement. I checked that the latter assumes a finite ring; C explicitly assumes every R/I^n is finite. It has no projectivity requirement for the basic chain/tower assertion. The original differential and the consecutive quotient are both checked on the sheafification-unit pure tensors, and the statement requires equality on locally generating tensors, not just on global constant sections. The normalized reduction unit and its zero shifted-product component are recorded. The parent only needs this strict comparison; no claim that inverse image commutes with the infinite coefficient limit is used.

For D I read Stacks 093J, 093M and 03EL in `sites-modules.tex`, and opened the exact-functor complex-cohomology, constant-module section properties, geometric inverse-image tensor comparison and independent-universe pullback-existence nodes. Noetherianity of R is present for scalar flatness. D is about all scalar modules, not finite-projective ones; H^j(P) can have pi-torsion. I checked both balanced inverse equations: the forward composite inserts c_g(1)=1, while the reverse composite moves c_g(b) across the balancing relation to recover b. The coefficient square is determined after every finite projection, and ordinary direct image preserves those limits as a right adjoint. This separates flatness over the constant scalar ring from the unnecessary flatness of c_g.

For the five assembly steps, I opened every cited statement and copied it verbatim in `citations.json`. Step 1 takes A's coefficient datum, flat K-flat model and normalized reduction, with exactly the parent's finite-extension hypotheses. Step 2 takes B's canonical augmentation, completeness and projections, and C's strict finite tower comparison; C applies to R and I=(pi), whose finite quotients were verified in step 1. Step 3 uses the actual definition of integral pullback, functorial strict Rlim and the integral/completed comparison: the latter explicitly requires derived completeness, supplied by B, and identifies the specified finite projections. Step 4 takes D's exact cohomology and ordinary pullback comparison with N=H^j(P), using Noetherianity from A. Step 5 is the elementary zero-sheaf consequence, with no flatness or representative-support argument hidden in it. The three existing non-elementary citations in step 3 are generic tools already used by the old route, and the existing off-unit tool declarations for these uses are retained.

I tested zero complexes, a single finite free term, an acyclic two-term identity complex, the two-term scalar differential pi (whose cohomology is torsion), n=1, the identity scheme morphism, and an empty scheme. The identity complex tests the cone signs and the pi complex tests the distinction between projective terms and nonprojective cohomology. The empty scheme causes no faithful-flatness inference: the vanishing argument pulls back the zero sheaf. Nothing assumes B_T faithfully detects an algebraic scalar module. No new statement assumes Noetherianity or finite type of a scheme. No parent statement dispute was found.

I corrected the old Step 8 classification: existence of the coefficient-induced module adjunction and the canonical ordinary comparison are assigned as genuine obligations to D, rather than calling that entire paragraph elementary. I also removed phrases about a comparison 'remaining unproved' from the assembly: these now have explicit statement-only tasks. I did not erase the old argument: the full text and its dependency lists follow below, with an owner assigned to every paragraph. All new proof lists and proof dependency lists remain empty, so no new node is prematurely split.

## Search and duplicate audit

Before writing the new files I searched the DAG titles/statements by scalar, constant, quotient, projective, reconstruction and cone-contractibility terms, opened the close candidates, and used `tools/blueprint_refs.py ancestor` and `search`. Searches for 'scalar pullback', 'normalized reconstruction', 'scalar flat', 'strict base', and 'exact scalar' had no exact blueprint match. 'quotient augmentation' returned `lem-weil-pbc-intrinsic-to-tower-complete` and `lemma-weil-pbc-koszul-quotient-limit`; those compare completeness notions or Koszul towers on general inputs, without proving this particular scalar model's canonical augmentation or its coefficient-retract/contractible-cokernel calculation. The new blueprint.from places identify the old step allocation and retain the original finite-etale-purity ancestor.

Each node has its own LeanFinder, Loogle, grep, and a second semantic phrasing with LeanSearch followed by a second grep. All 20 searches ran successfully with msearch.py and are recorded exactly in searches.jsonl and in the nodes. Full outputs remain in the per-node `.search*.txt` files. I read the hits, including Valued.integer finite-quotient facts, algebraic AdicCompletion flatness/tensor equivalences, abstract complex limits, presheaf pullback, ConstantSheaf's dense-subsite comparisons and abstract homology preservation. The algebraic flat_of_isNoetherian at Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:379 applies to algebraic completion, not the sheaf inverse limit with the required normalizations. ConstantSheaf.lean explicitly leaves general pullback compatibility as a TODO. Thus none gives a full task in one line. The parent retains its historical searches rather than inventing a rerun of them.

## Not duplicates

lem-a1-projective-quotient-augmentation vs def-sbc-strict-projection-tower-data: that defines abstract normalized limit data; this proves invertibility of a specified quotient augmentation for a particular projective model.

lem-a1-projective-quotient-augmentation vs lem-sf-open-reduction-adjunction-transport: that assumes reconstruction units invertible to transport open adjunctions; this proves the specific scalar model reconstruction and its actual projections.

lem-a1-projective-quotient-augmentation vs lem-coef-derived-tower-counit-projections: that constructs a derived adjunction and identifies its counit projections for arbitrary towers; it does not show the scalar quotient augmentation is invertible or its cokernel contractible.

lem-a1-projective-quotient-augmentation vs lem-sf-perfect-tensor-roos-completion: that is algebraic perfect tensor completion on the one-point ringed site with scalar-extension coherence; this is completed constant module-sheaf reconstruction on any scheme, including local completeness and K-injective normalization.

lem-a1-projective-quotient-augmentation vs lem-coef-sequence-sections-limit-comparison: that compares derived global sections with a total inverse limit; this establishes the scalar model itself as a canonically augmented limit and complete object.

lem-a1-projective-quotient-augmentation vs lem-coef-derived-system-evaluation-calculus: that gives system adjunction and mapping evaluation and explicitly does not assert reconstruction-unit invertibility; this proves it for the fixed scalar model.

lem-a1-projective-quotient-augmentation vs def-sf-strict-roos-coordinate-interface: that only defines coordinates and explicitly asserts no quasi-isomorphism; this proves a particular normalized quotient augmentation is a quasi-isomorphism.

lem-a1-projective-quotient-augmentation vs def-sf-open-semilinear-tensor-model-data: that defines open-extension and tensor comparison data; this asserts scalar quotient reconstruction without any open immersion.

lem-a1-projective-quotient-augmentation vs lem-sf-integral-compactification-system-realization: that concerns finite-type constructible systems and compactification expressions; this proves scalar quotient reconstruction on arbitrary schemes without those geometric hypotheses.

lem-a1-projective-quotient-augmentation vs lem-coef-sequence-pushforward-limit-projections: that identifies pushforward with total limit and normalizes unit/counit projections; it does not prove the scalar quotient unit invertible.

lem-a1-projective-quotient-augmentation vs lem-coef-finite-adjunction-diagram-realization: that constructs finite exceptional functors and enriched adjunctions over finite-type schemes; this has no exceptional functor and proves scalar quotient completeness on any scheme.

lem-a1-projective-quotient-augmentation vs def-sf-adic-module-quotient-data: that defines algebraic quotient functors and maps; this proves their completed sheaf-complex augmentation is a normalized derived-limit isomorphism.

lem-a1-constant-complex-strict-base-change vs lem-sfb-site-inverse-image-multimap-universal: that is the universal property of maps out of finite products of inverse images; this task needs actual normalized coefficient towers or completed scalar realization, not merely the universal property.

lem-a1-constant-complex-strict-base-change vs lem-sfb-site-inverse-image-bilinear-adjunction: that is a bilinear adjunction for arbitrary sheaves; this task identifies concrete scalar coefficient maps and their normalized complex comparisons.

lem-a1-constant-complex-strict-base-change vs lem-weil-pbc-ringed-slice-normalized-comparisons: that concerns slice restriction with supplied tensor/Hom models; this concerns arbitrary geometric inverse image and the completed or finite scalar coefficient diagrams.

lem-a1-constant-complex-strict-base-change vs def-coef-semilinear-geometry-derived: that defines required derived system normalization data, without an existence theorem for these constant scalar comparisons.

lem-a1-constant-complex-strict-base-change vs def-sf-point-evaluation-tensor-coherence: that defines coherence requirements for evaluation on a field point; this task proves comparisons of scalar module sheaves on arbitrary schemes.

lem-a1-constant-complex-strict-base-change vs def-sf-point-evaluation-scalar-data: that defines prescribed point-section scalar data; this task proves the relevant sheaf comparisons on arbitrary schemes.

lem-a1-constant-complex-strict-base-change vs lem-coef-signed-single-dual-restriction: that is compatibility of single-dual shift comparisons under slice restriction; no dual or shift comparison is being asserted here.

lem-a1-constant-complex-strict-base-change vs lem-sf-open-operation-models: that constructs open-operation data from fixed tensor and right-square presentations; this task concerns general scheme pullback of constant scalar modules and quotient towers.

lem-a1-constant-complex-strict-base-change vs lem-weil-ramified-finite-pullback-comparison: that assumes coefficient comparison data for two l-adic fields and proves ramified extension/pullback squares; this task constructs the fixed-scalar constant comparisons and their quotient/unit normalization.

lem-a1-constant-complex-strict-base-change vs lem-weil-finite-pullback-transition-generators: that computes a transition on generators in an already specified finite pullback tower; this task supplies the constant scalar comparison (or completed coefficient ring map and adjunction) itself.

lem-a1-constant-complex-strict-base-change vs def-sf-point-evaluation-tensor-data: that defines a tensor presentation for evaluation on a field point; this task is a theorem about actual module sheaves on arbitrary schemes.

lem-a1-constant-complex-strict-base-change vs def-sf-point-evaluation-derived-compatibility: that defines derived compatibility for point evaluation; this task asserts existence of actual scalar sheaf comparisons without a point-evaluation hypothesis.

lem-a1-adic-scalar-flat-reduction-model vs lem-a1-completed-perfect-scalar-pullback: the parent combines completed derived pullback, cohomology and amplitude; this is one of four explicitly ordered subarguments, with internal normalized model obligations and without the full pullback/amplitude conclusion.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-ringed-finite-free-resolution-tensor: that assumes an already specified finite-free sheaf resolution of one module; this constructs the adic scalar/projective complex model and its normalized whole quotient family.

lem-a1-adic-scalar-flat-reduction-model vs lem-sf-integral-line-tensor-comparison-representative: that tensors an existing good complex with a rank-one sheaf; this verifies scalar finite-projective models and their coefficient quotient units.

lem-a1-adic-scalar-flat-reduction-model vs lem-tw-finite-projective-model-pullback: that computes ordinary derived geometric pullback of a perfect scalar model; this task verifies all finite coefficient reductions and the scalar adic datum.

lem-a1-adic-scalar-flat-reduction-model vs lem-trf-finite-filtered-flat-resolution: that constructs a resolution of an arbitrary filtered complex; this task uses the original fixed projective scalar complex and its explicit quotient maps.

lem-a1-adic-scalar-flat-reduction-model vs def-trf-split-flat-filtered-sheaf-models: that defines filtered model predicates and convolution; this proves properties of actual adic coefficient and quotient complexes with no filtration.

lem-a1-adic-scalar-flat-reduction-model vs lem-pc-bounded-above-flat-tensor-acyclic-degree: that proves one fixed-degree tensor acyclicity under another lemma's hypotheses; this task requires the adic scalar datum and normalized finite reductions.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-standard-sheaf-cotangent-flat-functorial-model: that concerns polynomial cotangent resolutions on a topological space; this concerns constant adic scalar models on the pro-etale site.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-flat-scalar-tor-comparison: that identifies scalar Tor cohomology for an existing flat realization; this builds the projective quotient representatives and their unit normalizations.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-constant-field-tor-bounds: that is a field-coefficient Tor-amplitude criterion; this is a DVR completed coefficient reduction theorem.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-integral-quotient-resolution-normalization: that supplies the scalar ring's two-term quotient resolution under a condensed coefficient encoding; this task includes arbitrary bounded finite-projective scalar complexes and their differential, transition and unit normalization.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-ringed-site-point-kflat-resolution: that constructs some resolution compatible with a point; this uses the given bounded scalar representative and has no point or stalk.

lem-a1-completed-scalar-exact-base-change vs lem-a1-completed-perfect-scalar-pullback: the parent combines completed derived pullback, cohomology and amplitude; this is one of four explicitly ordered subarguments, with internal normalized model obligations and without the full pullback/amplitude conclusion.

lem-a1-completed-scalar-exact-base-change vs lem-sfb-site-inverse-image-multimap-universal: that is the universal property of maps out of finite products of inverse images; this task needs actual normalized coefficient towers or completed scalar realization, not merely the universal property.

lem-a1-completed-scalar-exact-base-change vs lem-sfb-site-inverse-image-bilinear-adjunction: that is a bilinear adjunction for arbitrary sheaves; this task identifies concrete scalar coefficient maps and their normalized complex comparisons.

lem-a1-completed-scalar-exact-base-change vs lem-weil-pbc-ringed-slice-normalized-comparisons: that concerns slice restriction with supplied tensor/Hom models; this concerns arbitrary geometric inverse image and the completed or finite scalar coefficient diagrams.

lem-a1-completed-scalar-exact-base-change vs def-coef-semilinear-geometry-derived: that defines required derived system normalization data, without an existence theorem for these constant scalar comparisons.

lem-a1-completed-scalar-exact-base-change vs def-sf-point-evaluation-tensor-coherence: that defines coherence requirements for evaluation on a field point; this task proves comparisons of scalar module sheaves on arbitrary schemes.

lem-a1-completed-scalar-exact-base-change vs def-sf-point-evaluation-scalar-data: that defines prescribed point-section scalar data; this task proves the relevant sheaf comparisons on arbitrary schemes.

lem-a1-completed-scalar-exact-base-change vs lem-coef-signed-single-dual-restriction: that is compatibility of single-dual shift comparisons under slice restriction; no dual or shift comparison is being asserted here.

lem-a1-completed-scalar-exact-base-change vs lem-sf-open-operation-models: that constructs open-operation data from fixed tensor and right-square presentations; this task concerns general scheme pullback of constant scalar modules and quotient towers.

lem-a1-completed-scalar-exact-base-change vs lem-weil-ramified-finite-pullback-comparison: that assumes coefficient comparison data for two l-adic fields and proves ramified extension/pullback squares; this task constructs the fixed-scalar constant comparisons and their quotient/unit normalization.

lem-a1-completed-scalar-exact-base-change vs lem-weil-finite-pullback-transition-generators: that computes a transition on generators in an already specified finite pullback tower; this task supplies the constant scalar comparison (or completed coefficient ring map and adjunction) itself.

lem-a1-completed-scalar-exact-base-change vs def-sf-point-evaluation-tensor-data: that defines a tensor presentation for evaluation on a field point; this task is a theorem about actual module sheaves on arbitrary schemes.

Additional close candidates opened beyond the source-tag list:

lem-a1-projective-quotient-augmentation vs lem-weil-pbc-finite-perfect-adic-coefficient-limit: it gives a Roos limit for compatible finite-free retract cones; the new task requires the actual normalized chain augmentation, its contractible cokernel, K-injective comparison and local/intrinsic completeness.

lem-a1-projective-quotient-augmentation vs lem-weil-pbc-finite-perfect-adic-marked-roos: it asserts the canonical quotient diagram has a completed realization as a Roos limit; it does not identify the specific augmentation chain map in the chosen strict resolution model, its actual projections or local/intrinsic units.

lem-a1-projective-quotient-augmentation vs lem-weil-pbc-finite-perfect-adic-canonical-comparison: it supplies some compatible retract cone but explicitly makes no limit or Roos claim; the new task proves the actual specified quotient cone and its normalized augmentation.

lem-a1-adic-scalar-flat-reduction-model vs lem-weil-pbc-completed-constant-finite-complex-realization: it concerns completed realization of finite modules over the algebraic completion; it does not specify the original projective scalar differential, its K-flat counit and degreewise unit/retract normalization.

lem-a1-completed-scalar-exact-base-change vs lem-weil-pbc-completed-realization-derived-cohomology: it supplies exactness and derived cohomology under normalized adic coefficient equivalences; the new task also constructs the actual projection-induced coefficient map and module adjunction, and gives ordinary pullback for every scalar module over a general Noetherian adic ring.

lem-a1-completed-scalar-exact-base-change vs lem-tw-finite-projective-model-pullback: it treats bounded finite-projective scalar complexes; the new task treats arbitrary scalar modules including nonprojective H^j(P), exact completed realization, and the coefficient-map adjunction.

lem-a1-constant-complex-strict-base-change vs lem-sp-proetale-scalar-balancing-chain: it balances a map of finite coefficient rings on an already given module-sheaf complex; the new task compares the entire constant scalar quotient tower including its normalized reduction units.

lem-a1-completed-scalar-exact-base-change vs lem-pur-completed-coefficient-structure-map: it constructs a projection-defined map in the l-adic case with existing completion-model data; the new task includes general Noetherian adic scalars, module adjunction, exact realization and arbitrary-module ordinary pullback.

lem-a1-completed-scalar-exact-base-change vs lem-tw-completed-coefficient-ringed-coherence: it proves composition and slice coherence of already specified l-adic coefficient maps; it does not supply exact realization or arbitrary scalar-module pullback.

lem-a1-projective-quotient-augmentation vs lem-weil-pbc-intrinsic-to-tower-complete: it assumes intrinsic completeness and gives a quotient-unit criterion; the new task verifies the concrete scalar model and the specified cone/projection/cokernel data.

lem-a1-projective-quotient-augmentation vs lemma-weil-pbc-koszul-quotient-limit: it identifies the Koszul completion functor with quotient completion on arbitrary input, without establishing the particular scalar object's unit is invertible.


### Additional live-source candidates from the first dry run

The delivery server had newer same-tag candidates than the initial local ordering. I opened each candidate and checked its full statement before recording these distinctions. No new task is an exact instance of any of them.

lem-a1-adic-scalar-flat-reduction-model vs lem-weil-pbc-completed-adic-koszul-kflat: it proves K-flatness only of a completed exterior Koszul complex, not the adic scalar datum or arbitrary scalar-complex reduction normalization.

lem-a1-adic-scalar-flat-reduction-model vs lem-weil-pbc-independent-bounded-flat-kflat: it assumes termwise flatness and proves K-flatness only; the new task also verifies constant projective flatness, adic coefficients and all quotient units.

lem-a1-adic-scalar-flat-reduction-model vs lem-weil-pbc-site-tensor-local-model-comparison: it compares fixed-degree cohomology of two supplied local tensor models, not completed scalar quotient representatives.

lem-a1-adic-scalar-flat-reduction-model vs lem-weil-pbc-split-perfect-tensor-kinjective: it preserves K-injectivity after tensor with a split perfect sheaf complex; no quotient normalization or coefficient datum is asserted.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-finite-flat-constructible-total-tensor: it treats tensor products of flat constructible finite-ring etale complexes on Noetherian schemes, rather than the completed DVR scalar complex on arbitrary schemes.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-finite-free-mono-cokernel-kflat: it computes a supplied monomorphism between finite free sheaves; the new task verifies general bounded finite-projective scalar complexes and the entire normalized quotient family.

lem-a1-adic-scalar-flat-reduction-model vs lem-sfb-flat-scalar-cyclic-resolution: it supplies a two-term scalar-cyclic resolution after assuming scalar flatness, not arbitrary projective complex realization and quotient units.

lem-a1-constant-complex-strict-base-change vs lem-a1-balanced-finite-tower-generator-comparison: it reassociates quotients of an already specified completed-module complex and compares its Koszul augmentation; the new task constructs constant scalar-complex tower comparisons or exact completed realization on all scalar modules.

lem-a1-constant-complex-strict-base-change vs lem-per-galois-descent-monodromy-tensor: it concerns Galois-descent tensors and monodromy on a nonempty connected Noetherian etale scheme, not scalar realization on arbitrary pro-etale schemes.

lem-a1-constant-complex-strict-base-change vs lem-per-local-system-tensor-monodromy: it describes stalk monodromy of local-system tensors; the new task constructs actual coefficient/module comparisons before any stalk or monodromy.

lem-a1-constant-complex-strict-base-change vs lem-per-proetale-scalar-slice-comparison: it commutes scalar extension with restriction to one slice; the new task concerns arbitrary scheme morphisms and constant or completed coefficient comparisons.

lem-a1-constant-complex-strict-base-change vs lem-pd-composite-module-oplax-mate: it equates composite internal module oplax maps with their adjunction mates, without proving these scalar realization or quotient-tower identifications.

lem-a1-constant-complex-strict-base-change vs lem-pd-generalized-tensor-normalization-unit-equation: it derives one module-unit equation under a supplied generalized tensor normalization, rather than existence/invertibility of the new normalized scalar comparisons.

lem-a1-constant-complex-strict-base-change vs lem-pd-ringed-tensor-adjunction-mate: it characterizes tensor comparison as the mate of a ringed module adjunction; the new task constructs the actual scalar realization/tower comparisons and their coefficient normalizations.

lem-a1-constant-complex-strict-base-change vs lem-pd-section-oplax-total-comparison: it compares internal and section module oplax total tensor presentations; the new task uses actual constant coefficient module sheaves and their scheme pullback.

lem-a1-constant-complex-strict-base-change vs lem-pd-section-ordinary-oplax-normalization: it normalizes the ordinary section tensor comparison of a supplied internal presentation, not these quotient towers or exact completed scalar realization.

lem-a1-constant-complex-strict-base-change vs lem-pod-etale-stalk-tensor-scalar: it is a geometric-stalk tensor/scalar compatibility theorem, not a sheaf-level constant complex tower or completed scalar realization theorem.

lem-a1-constant-complex-strict-base-change vs lem-pod-lisse-tensor-and-scalar-extension: it is closure of lisse coefficient sheaves under tensor and scalar extension, not these normalized chain comparisons or exact realization for arbitrary modules.

lem-a1-completed-scalar-exact-base-change vs lem-a1-balanced-finite-tower-generator-comparison: it reassociates quotients of an already specified completed-module complex and compares its Koszul augmentation; the new task constructs constant scalar-complex tower comparisons or exact completed realization on all scalar modules.

lem-a1-completed-scalar-exact-base-change vs lem-per-galois-descent-monodromy-tensor: it concerns Galois-descent tensors and monodromy on a nonempty connected Noetherian etale scheme, not scalar realization on arbitrary pro-etale schemes.

lem-a1-completed-scalar-exact-base-change vs lem-per-local-system-tensor-monodromy: it describes stalk monodromy of local-system tensors; the new task constructs actual coefficient/module comparisons before any stalk or monodromy.

lem-a1-completed-scalar-exact-base-change vs lem-per-proetale-scalar-slice-comparison: it commutes scalar extension with restriction to one slice; the new task concerns arbitrary scheme morphisms and constant or completed coefficient comparisons.

lem-a1-completed-scalar-exact-base-change vs lem-pd-composite-module-oplax-mate: it equates composite internal module oplax maps with their adjunction mates, without proving these scalar realization or quotient-tower identifications.

lem-a1-completed-scalar-exact-base-change vs lem-pd-generalized-tensor-normalization-unit-equation: it derives one module-unit equation under a supplied generalized tensor normalization, rather than existence/invertibility of the new normalized scalar comparisons.

lem-a1-completed-scalar-exact-base-change vs lem-pd-ringed-tensor-adjunction-mate: it characterizes tensor comparison as the mate of a ringed module adjunction; the new task constructs the actual scalar realization/tower comparisons and their coefficient normalizations.

lem-a1-completed-scalar-exact-base-change vs lem-pd-section-oplax-total-comparison: it compares internal and section module oplax total tensor presentations; the new task uses actual constant coefficient module sheaves and their scheme pullback.

lem-a1-completed-scalar-exact-base-change vs lem-pd-section-ordinary-oplax-normalization: it normalizes the ordinary section tensor comparison of a supplied internal presentation, not these quotient towers or exact completed scalar realization.

lem-a1-completed-scalar-exact-base-change vs lem-pod-etale-stalk-tensor-scalar: it is a geometric-stalk tensor/scalar compatibility theorem, not a sheaf-level constant complex tower or completed scalar realization theorem.

lem-a1-completed-scalar-exact-base-change vs lem-pod-lisse-tensor-and-scalar-extension: it is closure of lisse coefficient sheaves under tensor and scalar extension, not these normalized chain comparisons or exact realization for arbitrary modules.

lem-a1-projective-quotient-augmentation vs def-a1-lisse-section-evaluation: it defines evaluation of lisse coefficient data and scalar-size comparisons, rather than proving a projective quotient augmentation is invertible.

lem-a1-projective-quotient-augmentation vs lem-a1-normalized-roos-shift-comparison: it proves shift compatibility of the general normalized Roos comparison, not invertibility of the scalar model augmentation or local completeness.

lem-a1-projective-quotient-augmentation vs lem-a1-quotient-unit-shift-completeness: it assumes the unshifted quotient augmentation invertible and proves shifted completeness; this new task establishes that hypothesis for scalar projective models.

lem-a1-projective-quotient-augmentation vs lem-a1-roos-intrinsic-unit-comparison: it identifies canonical intrinsic and quotient units and concludes invertibility only for already complete inputs; this task establishes the specific scalar model completeness and explicit contractible-cokernel augmentation.

lem-a1-projective-quotient-augmentation vs lem-a1-signed-fiber-roos-normalization: it gives a general signed-coordinate comparison and augmentation equation, without claiming a given augmentation is invertible; this task proves that using coefficient retracts and its cokernel.

lem-a1-projective-quotient-augmentation vs def-zl-field-weil-shriek-shift-data: it defines field-stage pullback/shriek shifts and adjoint data, not completed scalar model reconstruction on an arbitrary scheme.

lem-a1-projective-quotient-augmentation vs def-fd-integral-pullback-shift-coordinates: it defines shift normalization and descent predicates without an existence assertion; this task asserts normalized scalar reconstruction and completeness.

lem-a1-projective-quotient-augmentation vs def-pod-integral-completed-comparison-data: it defines the integral/completed comparison record, not the concrete scalar quotient augmentation.

lem-a1-projective-quotient-augmentation vs lem-pod-integral-pullback-system-comparison: it identifies reduction of already constructible completed pullback with system inverse image; this task proves scalar quotient reconstruction without constructibility or a scheme morphism.

lem-a1-projective-quotient-augmentation vs lem-pod-integral-system-pullback-lift-associativity: it proves associativity of an assumed fixed lift family, not existence/invertibility of the scalar quotient augmentation.

lem-a1-projective-quotient-augmentation vs lem-pod-integral-system-reduction-fully-faithful: it is full faithfulness on derived-complete bounded constructible inputs; the new task proves completeness and the normalized reconstruction map for the given scalar model.

lem-a1-projective-quotient-augmentation vs def-weil-pbc-derived-reduction-model-data: it records a derived reduction functor and unit normalization without a new existence theorem; this task proves a concrete completed projective model is its normalized limit.

## Retained argument and assignment of work

The following is the returned proof verbatim, with all original citations. These are research/proof plans for the new unsplit tasks, not proof steps embedded in their JSON. They also preserve the earlier worker's exact normalizations and logged source choices. The new statements express the intermediate obligations these arguments establish.

### Returned step 1; assigned to lem-a1-adic-scalar-flat-reduction-model

The coefficient ring $R$ is a discrete valuation ring with maximal ideal $(\pi)$ and finite residue field. In particular it is a PID and is Noetherian. Each $A_n$ is finite, its consecutive quotient map is surjective, and it is killed by a power of $\ell$: write $\ell=u\pi^e$ with $e\ge1$ using the extended absolute value and the DVR factorization, and choose $m$ with $em\ge n$. Since $R$ is a domain and $\pi\ne0$, the complex $[R\xrightarrow{\pi^n}R]$ in degrees $-1,0$ resolves $A_n$ by two finite free modules. Thus $(R,(\pi))$ satisfies the hypotheses of the adic coefficient datum, including perfectness of all its quotients. Use its actual coefficient sheaves, completed limit, projections and strict quotient tower. The identification of finite coefficient sheaves with constant sheaves, supplied by the completed-constant reduction theorem, identifies this limit with the $B_T$ in the statement and respects every projection.

Cited nodes: lem-weil-l-adic-extension-integers-dvr, lem-weil-pbc-pid-noetherian-normal, lem-weil-valued-dvr-finite-quotients, def-weil-pbc-adic-coefficient-datum, lem-weil-pbc-completed-constant-sheaf-reduction

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 093M (lemma-completion-flat), with the finite-coefficient identification of the adic datum; the DVR consequences and its two-term quotient resolution"}

### Returned step 2; assigned to lem-a1-adic-scalar-flat-reduction-model

For each degree, projectivity makes P^r flat over R. The local equational criterion proves that its constant module sheaf is flat: lift a finite relation, its coefficients and its sections locally through the sheafification units, refine until the relation holds in P^r, factor it using algebraic flatness, and sheafify this factorization. The bounded-above-flat theorem at independent coefficient universes makes the constant complex K-flat. The identity-topos change-of-rings theorem transports K-flatness and termwise flatness through the recorded completed scalar extension. This proves model_good without using finite generation or flatness of the completed coefficient map. Derived reduction is consequently ordinary tensor on this complex. For the remaining normalized reduction comparison, the planned map in every degree is (b tensor p) tensor a mapped to a pr_n(b) tensor p; its inverse inserts 1. Balancing proves the inverse equations and compatibility with the original differentials and consecutive quotients. That last normalized comparison is still part of the unproved main theorem.

Cited nodes: def-weil-pbc-projective-module, lem-pur-derived-change-of-rings, lem-exc-site-local-relations-imply-flat, lem-weil-pbc-independent-bounded-flat-kflat, lem-pur-kflat-change-of-rings-independent, lem-weil-pbc-independent-sheaf-tensor-colimits

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tags 06YQ and 0G7E; local finite-relation flatness of constant module sheaves, bounded-above K-flatness, and change of rings at independent coefficient universes; remaining normalized finite reduction uses the elementary balanced-tensor calculation."}

### Returned step 3; assigned to lem-a1-projective-quotient-augmentation

Choose integers $c\le d$ outside which $P^\bullet$ is zero. Apply the completed perfect model completeness lemma with $A=R$, $I=(\pi)$, this bounded complex and either $T$. The Noetherian and maximal-ideal hypotheses were checked in step 1. Its complex $M^\bullet=B_T\otimes_RP^\bullet$ is exactly our displayed complex, with its original scalar differential. Hence $C_T(P)$ is locally derived $(\pi)B_T$-complete: $R\mathcal Hom(B_U[1/b],C_T(P)|_U)=0$ for every slice $U$ and every local section $b$ of $\pi B_T$. By step 1, $(R,(\pi))$ satisfies the adic coefficient datum, and $B_T$ is the coefficient sheaf $\varprojlim_n(A_n)_T$ of the completeness-equivalence theorem (its auxiliary prime $p$ is any prime $\ne\ell$ and enters none of its conditions). Its implication (ii)$\Rightarrow$(i),(iv) shows that $C_T(P)$ is derived complete in the Roos-triangle sense and that the explicit product-fibre unit of the intrinsic Koszul completion is invertible. This is the completeness required by the specified completed-pullback definition and by the integral-pullback comparison used in step 6; it imposes no finiteness or Noetherian hypothesis on $T$.

Cited nodes: lem-sfb-adic-perfect-model-complete-reduction, lem-pur-roos-intrinsic-completeness-equivalence

Source: {"document": "literature/stacks-project/proetale.tex", "place": "Tag 099Q (proposition-enough-weakly-contractibles), bounded perfect scalar model; Bhatt–Scholze Proposition 6.6.11 reverse-direction local model"}

### Returned step 4; assigned to lem-a1-projective-quotient-augmentation

Set $D_{T,n}=(A_n)_T\otimes_{\underline R_T}\underline{P^\bullet}_T$, restricted along $\operatorname{pr}_n$. Its quotient cone is $b\otimes p\mapsto\operatorname{pr}_n(b)\otimes p$ from $C_T(P)$. The $R$-linear splitting $i_r,s_r$ of step 2, tensored with $B_T$ and each $(A_n)_T$, makes the degree-$r$ cone a compatible split retract of the $m_r$-fold coefficient cone, degreewise only. By the finite-perfect coefficient-limit theorem, $C_T(P)$ with the quotient maps is the ordinary limit of the complex tower. In each degree $r$ the transition $\operatorname{Res}_{n+1}D^r_{T,n+1}\to\operatorname{Res}_nD^r_{T,n}$ is $q_{n+1,n}\otimes1$, epi by right exactness of tensor. Hence the epimorphic-tower theorem makes $1-s:\prod_nD^r_{T,n}\to\prod_nD^r_{T,n}$ surjective with kernel the limit, which the coefficient-limit theorem identifies with $C_T(P)^r$ and its quotient maps. Let $\mathsf C(D)=\operatorname{Cone}(1-s)[-1]$, with degree-$k$ part $\prod_nD^k\oplus\prod_nD^{k-1}$, and let $b:C_T(P)\to\mathsf C(D)$ have product component the quotient maps and zero shifted component. It is a chain map, since $1-s$ kills the quotient family, and degreewise injective. Its cokernel is identified, through $1-s$ on the first summand, with $\prod_nD^k\oplus\prod_nD^{k-1}$ and differential $(z,y)\mapsto(dz,\pm z-dy)$: the shifted cone of an identity, which is contractible. By the long exact cohomology sequence $b$ is a quasi-isomorphism. Pro-etale countable products are exact, so the strict Roos comparison theorem applies; it says that $b$ corresponds under its natural isomorphism $\rho_D:\mathsf C(D)\cong R\lim_n\operatorname{Res}_nD_{T,n}$ to the canonical derived map induced by the strict augmentation, and that $\rho_D$ commutes with every projection. Thus the canonical map $C_T(P)\to R\varprojlim_n\operatorname{Res}_nD_{T,n}$ (cone model and K-injective strict model alike) is an isomorphism whose projections are the original quotient maps. Both $b$ and $\rho$ are natural in strict maps of towers. The helper proofs are formalized: quotientTowerIso_naturality follows by constructing the natural transformation from consecutive arrows; reductionTowerMap_condition is naturality of unrestrictedIntegralTransition with its orientation reversed. The normalized quotient units commute with consecutive transitions because the transition preserves the coefficient 1. Conjugating by the finite reduction isomorphisms and canceling their inverse pairs makes the quotient family a cone. Joint monicity of product projections then proves limitUnit_condition. Invertibility of this chain map remains part of the unproved main theorem.

Cited nodes: lem-weil-pbc-finite-perfect-adic-coefficient-limit, lem-weil-proetale-surjective-tower-derived-limit, lem-weil-proetale-countable-products-exact, lem-weil-strict-roos-comparison, lem-weil-pbc-ringed-strict-tower-homotopy-limit

Source: {"document": "literature/stacks-project/sites-cohomology.tex", "place": "Tags 0940 (section-derived-limits) and 0941 (lemma-derived-limit-is-ok), applied to the finite-projective retracts of the actual coefficient cone"}

### Returned step 5; assigned to lem-a1-constant-complex-strict-base-change

At finite level the canonical constant-module inverse-image isomorphisms give $g^{-1}\underline R_V\cong\underline R_{V'}$, $g^{-1}(A_n)_V\cong(A_n)_{V'}$ and $g^{-1}\underline{P^r}_V\cong\underline{P^r}_{V'}$. They preserve constant scalar sections and are natural in $R$-linear maps. Combine them with the inverse-image tensor comparison, then cancel extension along the constant-ring isomorphism. This gives
$$g_n^*D_{V,n}\cong D_{V',n}.$$
On a tensor of constant sections the map is $a\otimes p\mapsto a\otimes p$. On its image under a differential both composites are $a\otimes d^rp$, and under a quotient transition both are $q_{n+1,n}(a)\otimes p$. The tensor comparisons are sheaf maps determined locally by pure tensors, so these equalities prove compatibility on the whole sheaves. Finite-level pullback is exact, hence this is also its derived comparison. It is an isomorphism of the strict towers of complexes, rather than a collection of unrelated derived isomorphisms.

Cited nodes: lem-sfb-geometric-inverse-image-constant-module, lem-pur-proetale-inverse-image-tensor-comparison, prop-weil-pbc-proetale-constant-exact

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 03EL (lemma-tensor-product-pullback); sites.tex Tag 0H7J (example-constant-sheaf), with canonical constant-section maps"}

### Returned step 6; assigned to Parent assembly step 3, with chain/tower naturality in lem-a1-adic-scalar-flat-reduction-model, lem-a1-projective-quotient-augmentation and lem-a1-constant-complex-strict-base-change

Use $C_V(P)$ itself as the K-flat representative from step 2. By the specified strict reduction-tower pullback, step 5 gives
$$Lg^*C_V(P)\cong R\varprojlim_n\operatorname{Res}_nD_{V',n}.$$
The inverse of the comparison in step 4 for $T=V'$ gives the asserted isomorphism with $C_{V'}(P)$, and identifies every projection with its ordinary quotient map. By step 3, $C_V(P)$ is derived complete in the Roos-triangle sense, so the integral-pullback comparison theorem gives a natural isomorphism $Lg^*C_V(P)\cong Lg^*_{\mathrm{comp}}C_V(P)$ with the strict-tower completed pullback, under which the defining projections of the two derived limits correspond. This is the asserted equivalence of the two pullbacks on this complete object. For a chain map $f:P\to Q$, every displayed reduction map commutes with $1\otimes f$ because both composites send $(b\otimes p)\otimes a$ to $a\operatorname{pr}_n(b)\otimes f(p)$. The ordinary limit cone comparison is natural by its universal property, and the strict derived-limit functor preserves this square. Thus the isomorphisms are natural in chain maps, independently of the auxiliary splittings, which were used only to establish invertibility.

Cited nodes: def-pur-integral-derived-operations, def-weil-pbc-completed-pullback, prop-weil-pbc-rlim-functoriality, lem-a1-integral-pullback-completed-comparison

Source: {"document": "literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf", "place": "Lemma 6.5.9(4)-(5), interpreted via the specified strict quotient tower; agent assembly and chain-map calculation"}

### Returned step 7; assigned to lem-a1-completed-scalar-exact-base-change

The constant-sheaf functor on $R$-modules is additive and exact by the constant-module section-properties theorem. The completed-constant reduction theorem says that $B_T$ is flat over $\underline R_T$, so $M\mapsto B_T\otimes_{\underline R_T}\underline M_T$ is additive and exact. Apply exact-functor preservation of complex cohomology to $P^\bullet$. Its comparison is induced by preservation of cycles and boundaries, so for every $j$ it is the canonical natural isomorphism
$$\mathcal H^j(C_T(P))\cong B_T\otimes_{\underline R_T}\underline{H^j(P^\bullet)}_T.$$
This uses flatness over the constant scalar ring; it makes no assertion about flatness of the coefficient map associated with $g$.

Cited nodes: lem-weil-pbc-constant-module-section-properties, lem-weil-pbc-completed-constant-sheaf-reduction, lem-weil-pbc-exact-functor-complex-cohomology

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tags 093J (lemma-constant-exact) and 093M (lemma-completion-flat); homology.tex Tag 010N (lemma-exact-functor)"}

### Returned step 8; assigned to lem-a1-completed-scalar-exact-base-change

Constant-section direct-image ring maps are natural in the coefficient ring, by naturality of the sheafification adjunction unit. Hence they define a natural transformation of the finite coefficient towers. Continuous direct image preserves limits, so the limit universal property gives directMap_existsUnique, with exactly the specified projections. Module direct image along this actual ring map is a right adjoint by the independent-universe ringed-site module pullback existence theorem; this proves ordinaryPush_isRightAdjoint. For the remaining ordinary comparison, use the constant-module inverse-image isomorphism and inverse-image tensor isomorphism to identify the pullback of B_Y tensor_R constant N with B_X tensor_R constant N. The coefficient maps agree on constant R after all finite projections, hence by the limit universal property. The balanced map b′ tensor (b tensor n) mapped to b′ g-sharp(b) tensor n and its inverse b′ tensor n mapped to b′ tensor (1 tensor n) are mutually inverse and natural in N. The comparison and its formulas remain part of the unproved main theorem.

Cited nodes: lem-sfb-geometric-inverse-image-constant-module, lem-pur-proetale-inverse-image-tensor-comparison, def-weil-pbc-completed-pullback, lem-pur-ringed-site-module-pullback-exists-universes

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Tag 03EL (lemma-tensor-product-pullback); elementary balanced-tensor cancellation along the projection-induced coefficient map"}

### Returned step 9; assigned to Parent elementary step 5

If $j\notin[a,b]$, step 7 identifies the assumed zero sheaf $\mathcal H^j(C_V(P))$ with $B_V\otimes\underline{H^j(P)}_V$. Ordinary ringed pullback sends the zero sheaf to zero, since inverse image and tensor send zero to zero. Step 8 identifies that pullback with $B_{V'}\otimes\underline{H^j(P)}_{V'}$, and step 7 identifies the latter with $\mathcal H^j(C_{V'}(P))$. Therefore the latter vanishes. This argument applies to each $j$ outside the given cohomological interval, irrespective of the degrees in which the chosen representative $P^\bullet$ is supported.

Cited nodes: none (elementary)

Source: {"document": "literature/stacks-project/sites-modules.tex", "place": "Elementary consequence of the exact cohomology and ordinary pullback identifications above"}

## Unfinished work

The four new tasks intentionally remain unsplit for parallel stage-1 workers. No mathematical subargument of the returned plan was discarded. Server dry-run results and the delivery commit are reported by the required delivery command.
