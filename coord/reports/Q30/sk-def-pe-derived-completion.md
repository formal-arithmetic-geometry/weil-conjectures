# Worker report: sk-def-pe-derived-completion

Files: the item (definition, eight-step split), `lem-pe-internal-section-tensor-comparison` and `lem-pe-kflat-roos-representative-invariance` (two new statement-only unsplit nodes, no Mathlib match), and the unit realization fields. Two new nodes, zero Mathlib leaves. citations.json contains 25 verbatim step/node certificates.

Attachments: none. The source search found no declaration with this blueprint tag. DerivedCategory/Complete/Defs.lean uses constant-ring module-valued sheaves and does not state this pulled-back condensed coefficient definition with its normalization and cohomology clauses. No Lean writing or compiler run.

WANTED: none.

The dedicated return in coord/returns/Q30.md identifies old steps 1 (2333 characters) and 3 (2740 characters). Their hidden internal/sectionwise tensor and K-flat representative comparisons have been extracted into general lemmas. The existing strict Roos augmentation comparison is reused. The item statement, route, remaining arguments and Lean metadata are preserved. Nothing remains unfinished at this split level; the new nodes deliberately carry statements only.

## Review by Q30

I read the main-20261015 unit and chapter records and the item's _section.md, including both normalization paragraphs. I read Stacks sites-modules.tex Tag 03EK (section-tensor-product, including balanced-bilinear universal property), Tag 0GMW (lemma-sheafification-tensor), sites-cohomology.tex Tags 06YS (lemma-K-flat-resolution), 06YY (lemma-derived-base-change), 0G7E (lemma-pullback-K-flat), 0D6D (lemma-derived-pullback-composition) and 06YQ (lemma-bounded-flat-K-flat), and derived.tex Tags 08TC (definition-derived-limit) and 07KC (lemma-products). The new sources distinguish these ingredients from the extracted agent arguments. Their statements are general comparisons, not restatements of the item or its normalization clause.

Step 1 uses the finite extension datum, condensed-ring functor, pulled-back coefficient functor, ambient Layer B row of derived-categories and Layer B relative derived tensor. I opened their statements: the maps R to B_(n+1) to B_n are their functorial images, and derived-categories is used only for its ambient category, not constructibility or its other existence assertions. The coefficient remains R=p_X^* underline(O_E).

Step 2 uses the sheafified tensor structure, its closedness and the new internal-section tensor comparison. The small-site/coefficient-universe convention is checked before applying this comparison to commutative R. The lemma explicitly compares the coequalizer relative tensor and sheafified sectionwise tensor, as well as total complexes, exactness and K-flatness. Old step 1's hidden comparison is now cited. Its proof idea, for the later splitter, is the identical sectionwise balanced-bilinear universal property, followed by exactness of the identity-on-underlying-sheaves equivalence and preservation of direct-sum totals. The unbounded total is not a finite-total shortcut.

Step 3 retains the K-flat representative calculation: the resolution statement supplies flat terms for every complex; derived extension explicitly computes on such representatives; change-of-scalars is the identity on underlying objects and maps. The kernel and cokernel argument explains exact restriction directly. The transition/unit square commutes strictly by p tensor 1. No flatness of B_n over R is used.

Step 4 uses exact countable products for any commutative ring sheaf, then clause 2 of derived-limit-existence for their termwise computation. Derived-limit and inverse-system supply the transition endomorphism and triangle. Abstract-derived-category supplies cones and shifts. The existing strict Roos comparison explicitly identifies a strict augmentation with zero shifted-product component with the canonical total-derived-limit map, so no uniqueness of a triangulated cone is assumed. I checked d(x,y)=(dx,(1-s)x-dy): its square is zero and it sends (c(p),0) to (c(dp),0). This agrees with the standard shifted cone after interchanging coordinates and negating the shifted-product coordinate.

Step 5 cites the extracted K-flat Roos invariance. Its exact-product hypothesis is step 4, compatible coefficient maps are step 1, and flat-term K-flat representatives are step 3. Its commuting augmentation square is expressly part of the cited statement. To check truth: a quasi-isomorphism a of K-flat representatives remains one after tensoring with each B_n by derived extension. Exact products preserve this and the cone cohomology sequence proves L(a) is a quasi-isomorphism. Its unit square commutes on pure tensors. A roof for an arbitrary derived isomorphism, resolved in the middle K-flatly, gives this square for both legs. This extracts the general comparison hidden in old step 3 without replacing the definition by an arbitrary isomorphism of limit objects.

Steps 6-7 retain normalization. K-flat change-of-rings expressly preserves K-flatness and flat terms for any ring-sheaf map. The second tensor is over B_(n+1); no flatness of its quotient is assumed. The balanced inverse formulas ((p tensor a) tensor b) to p tensor bar(a)b and p tensor b to ((p tensor 1) tensor b) commute with differentials. For a longer chain both composites send an iterated pure tensor to p tensor the product of its reduced coefficients. This is the elementary tensor calculation retained in the item, not a new node.

Step 8 retains the counterexample. The pullback statements give exact inverse image and the condensed finite ring is constant. The bounded-flat criterion applies to [R --ell--> R] in degrees -1,0. At ell=2 and n=1, the nonzero kernel {0,2} in Z/4 maps to zero in Z/2; both kernels after ordinary quotient tensor are F_2. Thus the complexes normalize while cohomology need not. Empty X and K=0 cause no problem for the construction; the counterexample expressly takes X nonempty.

I tested the first new lemma at the zero ring, zero module and empty site: the equivalence and tensor assertions persist. The existing lem-c2-internal-section-module-flatness only states the flat-module predicate comparison, not the tensor, total complex and K-flat identifications. The second new lemma also works for zero P and identity coefficient maps, and for non-flat quotients: it needs exact products, not flat coefficient maps, boundedness or surjectivity. The existing integral reduction tower well-definedness has completed integral coefficients and only levelwise comparisons; the fixed-tower strict Roos lemma is reused directly and does not compare changing K-flat inputs.

Before creating either node I searched the whole DAG by tags and statements, source Lean by tag/concepts, and blueprint_refs for derived completion, internal abelian, Roos, K-flat, tensor.*section, K-flat.*representative, internal.*module.*tensor, 0GMW and 06YY. Mathlib searches were all run by msearch.py; exact queries and results are preserved in searches.jsonl and node records. Each new node has two semantic phrasings, Loogle and grep. LeanSearch for the first was rate-limited and is recorded unavailable. I read the candidate files: Mathlib/CategoryTheory/Sites/Monoidal.lean:160-205, Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:25-100, RingTheory/Flat/CategoryTheory.lean:30-90, Algebra/Homology/Localization.lean:350-420 and QuasiIso.lean:150-225. Their monoidal sheaf/presheaf constructions, ordinary module flatness, localization for functors already preserving homology, and two-out-of-three do not state these full comparisons. Neither new node is a Mathlib leaf.

B1-B10: both nodes are self-contained statement-only lemmas with sites, rings, universe assumptions, definitions, source tags, exact search records and blueprint ancestry. C1-C8: every non-elementary step has statement citations, all 25 complete-statement quotes are verbatim, and off-unit generic tools are declared in split_report. D1-D5: the item's construction and normalization proof remain; only the hidden general comparisons were extracted. E1-E6: arbitrary scheme, commutative coefficient ring, unbounded complexes, exact products and smallness were checked where used. Coherence and representative independence are explicit. The eight step lengths are 891, 778, 1185, 1549, 614, 522, 1049 and 1330, all below 2000. No SGA source is used. The unit has no proof paragraphs, and its realization still names this item. No statement dispute or weakening.

Resumption audit, 2026-10-17: I began with the required retained-work dry run; the server returned OK at 73e0e75e88. I compared the sandbox item with the current shared item: the statement, chapter, unit, import flags, Lean audit, existing review and maintainer-owned tool uses are unchanged. I reopened all direct proof-dependency statements and checked all 25 citation quotes against the current statements. In particular, the exact-products node applies to arbitrary commutative ring sheaves, the K-flat resolution has flat terms, and the strict Roos comparison explicitly covers the specified zero-homotopy augmentation. I reopened the Stacks source labels for 03EK, 0GMW, 06YS, 06YY, 0G7E, 0D6D, 06YQ, 08TC and 07KC. These support the quoted ingredients; the two extracted comparisons are correctly identified as agent arguments, not verbatim Stacks theorems. I read the retained search log and candidate source files rather than repeating unchanged searches. The source declaration search still gives no blueprint-tag match, and CategoryTheory/DerivedCategory/Complete/Defs.lean works with sheaves valued in ModuleCat of a constant ring, so it cannot attach this pulled-back condensed-coefficient item. The counterexample at ell=2, n=1 still has the zero transition from the kernel in Z/4 to the nonzero kernel in Z/2. I corrected only the stale step-number reference in step 3: the sectionwise presentation is now step 2. Both returned hidden arguments remain extracted, all eight steps are shorter than 2000 characters, and no source-route or coefficient change is needed.

## Not duplicates

lem-pe-internal-section-tensor-comparison vs lem-sc-hom-tensor-comparison-natural: Existing statement concerns Naturality of the sheaf tensor comparison isomorphism; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sites-module-sheafification-bilinear-extension: Existing statement concerns Bilinear maps extend through module sheafification; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-balanced-sheaf-tensor-original-sections-ext: Existing statement concerns Original-section extensionality for restricted balanced sheaf tensors; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-hom-tensor-summand-restriction-ext: Existing statement concerns Internal Hom maps determined by total tensor summand restrictions; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-internal-hom-coproduct-fan: Existing statement concerns Internal Hom of a coproduct is a product; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-balanced-sheaf-tensor-contraction: Existing statement concerns Balanced contraction on sheaf tensors; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sheaf-modules-tensor-closed: Existing statement concerns Sheaves of modules on a site form a symmetric monoidal closed category; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-balanced-sheaf-tensor-comparison-isIso: Existing statement concerns Invertibility of the canonical balanced sheaf tensor map; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-hom-tensor-section-natural: Existing statement concerns Naturality of the canonical presheaf-to-sheaf tensor map; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sites-module-sheafification-tensor: Existing statement concerns Tensor and sheafification for modules over a presheaf of rings; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sites-module-sheafification-bilinear-extension-existence: Existing statement concerns Existence of bilinear sheafification extension; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-local-bilinear-sheafification-tensor: Existing statement concerns Local bilinear presheaf pairings extend to sheaf tensor products; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sites-module-sheafification-bilinear-extension-uniqueness: Existing statement concerns Uniqueness of bilinear sheafification extension; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-hom-tensor-summand-localized-ext: Existing statement concerns Localized pure-tensor extensionality for a sheaf tensor; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pc-sites-sheaf-tensor-bilinear-universal: Existing statement concerns Universal property of sheaf tensor product; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-internal-hom-product-fan: Existing statement concerns Internal Hom preserves integer-indexed product fans; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-sc-hom-tensor-reverse-pair: Existing statement concerns Reverse currying for one pair of module sheaves; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-continuous-module-encoding-scalar-extension: Existing statement concerns Scalar extension under the continuous integral and rational module encodings; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs def-weil-pbc-ringed-tensor-section-calculus: Existing statement concerns Section calculus for the actual sheaf tensor and scalar extension; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-tensor-local-bijection-universes: Existing statement concerns Tensoring a local module bijection commutes with sheafification in independent universes; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-w2-inverse-image-change-of-rings-unit-smul: Existing statement concerns Scalar compatibility of the inverse-image change-of-rings unit; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-scalar-extension-tensor-comparison: Existing statement concerns Scalar extension preserves the normalized sheaf tensor; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-continuous-module-encoding-lattices: Existing statement concerns Local freeness and lattice compatibility of the explicit continuous encodings; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-free-sheaf-flat: Existing statement concerns The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-scalar-tensor-comparison-universes: Existing statement concerns Scalar-extension tensor associativity on underlying abelian sheaves in independent universes; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-pbc-sheaf-tensor-closed: Existing statement concerns A-valued sheaves on an essentially small site: Grothendieck abelian, symmetric monoidal closed under the sheafified tensor product; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs def-pur-kummer-module-coefficients: Existing statement concerns Kummer sheaves with module coefficients and their scalar actions; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs def-pur-sheaf-tensor-product: Existing statement concerns Tensor product of sheaves of modules on a site; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-weil-sheaf-scalar-extension-ring-iso: Existing statement concerns Scalar extension along an isomorphism of ring sheaves; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-pur-change-of-rings-tensor-comparison: Existing statement concerns Natural comparison of restricted scalar extension and sheaf tensor; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs lem-exc-constant-field-sheaf-tensor-cohomology: Existing statement concerns Tensoring over a constant field sheaf commutes with cohomology; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-internal-section-tensor-comparison vs def-pur-presheaf-tensor-product: Existing statement concerns Presheaf tensor product of modules; it does not compare the internal/sectionwise relative tensor equivalence, unbounded total complexes and K-flat tests.

lem-pe-kflat-roos-representative-invariance vs lem-sbc-derived-scalar-extension-counit-shift: Existing statement concerns Counit-compatible shift structure of derived change of rings on a site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-scalar-extension-unit-triangles: Existing statement concerns Scalar-extension maps form morphisms of distinguished triangles; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-sf-integral-hom-reduction-comparison: Existing statement concerns Canonical integral internal Hom reduction comparison; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-inverse-image-pullback-comparison: Existing statement concerns Comparison morphism from the inverse image to the derived pullback along an isomorphism; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-coef-derived-system-evaluation-calculus: Existing statement concerns Coherent derived reduction, limit adjunction and fiberwise evaluation; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-coef-finite-adjunction-diagram-realization: Existing statement concerns Finite exceptional operations and enriched adjunction on coherent coefficient systems; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-coef-sheaf-flat-model: Existing statement concerns Monoidal flat model for unbounded complexes on a ringed site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-coef-ringed-sequence-site: Existing statement concerns Canonical ringed sequence site for the coefficient quotient tower; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-derived-limit-levelwise-iso: Existing statement concerns A map of derived limits induced by a levelwise isomorphism is an isomorphism; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-trf-finite-filtered-flat-resolution: Existing statement concerns Flat resolutions for a fixed finite filtration; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-single-tensor-representative: Existing statement concerns lem-pc-kflat-single-tensor-representative; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-model-shift-gauge: Existing statement concerns Local supplied-tensorator shift gauge on flat telescope models; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-flat-truncation-telescope-comparison: Existing statement concerns Quasi-isomorphism comparison for telescopes of truncation replacements; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-complex-hocolim-colimit: Existing statement concerns Telescope homotopy colimits are termwise filtered colimits; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-derived-tensor-upper-bound: Existing statement concerns Derived tensor with a module preserves an upper cohomological bound; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-bounded-flat-replacement: Existing statement concerns Bounded-above flat replacement on a ringed site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-resolution: Existing statement concerns Existence of K-flat resolutions on a ringed site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-sc-bounded-flat-shift-representative: Existing statement concerns Bounded-flat homotopy representatives and their translates; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-bounded-above-flat-tensor-acyclic: Existing statement concerns Tensoring bounded-above acyclic complexes with bounded-above flat complexes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-normalization-morphisms: Existing statement concerns Forward morphisms extending a bounded-flat normalization; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-kflat-localized-cone-presentation: Existing statement concerns K-flat cone presentation after homotopy localization; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-shift-gauge: Existing statement concerns Source shift gauge for flat telescope normalization; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-hocolim-truncations: Existing statement concerns Homotopy colimit of truncations; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-bounded-normalization-extension: Existing statement concerns Extend bounded normalization through telescope cones; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-arrow-diagram: Existing statement concerns Compatible flat tower diagram over a cochain arrow; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-bounded-above-flat-kflat-site: Existing statement concerns Bounded-above flat complexes on a ringed site are K-flat; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-normalized-flat-telescope-stage-comparison: Existing statement concerns Joint normalization natural on bounded-flat tower maps; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-pc-derived-tensor-cohomology-vanishes: Existing statement concerns Vanishing of derived tensor cohomology with an O_X-module; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-normalization-is-iso: Existing statement concerns Invertibility propagates from bounded-flat models to telescopes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-normalized-flat-telescope-comparison: Existing statement concerns Joint normalized pullback comparison on explicit flat telescopes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-tensor-counit-coordinate-equation: Existing statement concerns Raw tensor coordinate equation for the universal pullback counit; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-normalization-unshifted-is-iso: Existing statement concerns Invertibility on literal unshifted telescope cones; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-bounded-flat-model-normalization: Existing statement concerns Supplied-tensorator normalization on bounded flat stages; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-sum-comparison-is-iso: Existing statement concerns Invertibility of the restricted natural comparison on the sum of bounded-flat stages; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-pc-kflat-complex: Existing statement concerns K-flat complex of modules on a ringed site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-stage-map-refinement: Existing statement concerns Common flat-tower refinement of a homotopy morphism; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-cone-normalization-descent: Existing statement concerns Cone extension and descent of supplied normalized sum maps; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-sc-derived-tensor-augmentation: Existing statement concerns Derived tensor augmentation on a scheme; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-pc-derived-tensor-complex-cohomology-vanishes: Existing statement concerns Vanishing of derived tensor cohomology of two derived objects; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-sc-flat-telescope-stage-map: Existing statement concerns Concrete flat telescopes and their stage-induced morphisms; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-sum-models: Existing statement concerns Literal telescope models for a countable coproduct; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-closure: Existing statement concerns Closure of K-flat complexes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sc-flat-telescope-stage-naturality: Existing statement concerns Common-refinement cancellation extends stage naturality; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pc-kflat-cone-direct-sum: Existing statement concerns Cones and countable direct sums of K-flat complexes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sfb-divisible-extension-derived-reduction: Existing statement concerns Derived reduction of an extension by a divisible sheaf; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sfb-left-complete-heart-upper-bound: Existing statement concerns Upper bounds from the heart by left completeness; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-derived-limit-existence: Existing statement concerns Existence and computation of derived limits; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-category-product: Existing statement concerns Products of families of objects in a category; countable products; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-ringed-topoi-derived-pullback: Existing statement concerns Derived pullback on ringed topoi computed by K-flat resolutions; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-pbc-derived-normalization-arrows: Existing statement concerns Canonical derived coefficient normalization arrows; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-pbc-common-stage-cones: Existing statement concerns Common-stage cones and distinguished triangles; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-supplied-ringed-topos-kflat-pullback: Existing statement concerns Tensor pullback adjoint to a supplied ringed-topos module direct image; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs prop-weil-pbc-rlim-functoriality: Existing statement concerns Functoriality of the sequential derived inverse limit; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-derived-limit: Existing statement concerns Derived limit of an inverse system; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-rectangle-derived-limit: Existing statement concerns The rectangle passes to the derived limit; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-inverse-system: Existing statement concerns Inverse system indexed by the positive integers, and its morphisms; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-tower-transition-endomorphism: Existing statement concerns Transition endomorphism 1 − s of the product of an inverse system; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-site-derived-tensor-descent: Existing statement concerns Derived tensor and K-flat representative descent on a ringed site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs prop-weil-pbc-roos-triangle: Existing statement concerns Roos triangle and Milnor exact sequence; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-pbc-diagram-kflat-replacements: Existing statement concerns Objectwise K-flat replacements in strict diagram categories; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-pbc-constant-coefficient-scalar-extension: Existing statement concerns Constant coefficient scalar extension on a site; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-change-of-rings-acyclic-kflat: Existing statement concerns Extension of scalars of acyclic K-flat complexes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-integral-operations-well-defined: Existing statement concerns The towers defining integral pullback and completed tensor product are invariant under change of K-flat resolution; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-derived-change-of-rings: Existing statement concerns Derived change of rings along a morphism of sheaves of rings, computed by K-flat resolutions; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-change-of-rings-tensor-comparison: Existing statement concerns Natural comparison of restricted scalar extension and sheaf tensor; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-acyclic-kflat-tensor-arbitrary: Existing statement concerns An acyclic K-flat complex tensors acyclically with every complex; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-kun-flat-resolution-existence: Existing statement concerns Flat K-flat resolutions; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-sf-strict-roos-derived-limit-comparison: Existing statement concerns Strict Roos cone comparison with total derived inverse limit and evaluations; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-change-of-rings-tensor-acyclic: Existing statement concerns Change of rings of a universally tensor-acyclic complex; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-weil-derived-scalar-extension-restriction-adjunction: Existing statement concerns Derived reduction modulo varpi^n is left adjoint to restriction of scalars; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs lem-pur-change-of-rings-kflat-quasi-iso: Existing statement concerns Termwise change of rings preserves quasi-isomorphisms between K-flat complexes; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-kflat-roos-representative-invariance vs def-weil-integral-derived-reduction: Existing statement concerns Derived reduction of integral complexes modulo powers of the uniformizer; it does not give augmented scalar-extension Roos-cone invariance under changing a K-flat representative for a general coefficient ring-sheaf tower.

lem-pe-internal-section-tensor-comparison vs lem-c2-internal-section-module-flatness: the latter only compares flat-module predicates, without relative tensor, total tensor or K-flat comparison.

lem-pe-kflat-roos-representative-invariance vs lem-weil-strict-roos-comparison: the latter compares the Roos model of a fixed tower with total inverse limit and is reused in step 4; the new lemma compares augmented scalar-extension towers under changing their K-flat input.

lem-pe-kflat-roos-representative-invariance vs lem-weil-integral-reduction-tower-well-defined: the latter has completed integral coefficients and levelwise comparisons, rather than the specified augmented Roos comparison for general ring towers.
