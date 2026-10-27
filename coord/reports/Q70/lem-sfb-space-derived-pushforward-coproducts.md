# Worker report: lem-sfb-space-derived-pushforward-coproducts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-pushforward-coproducts.json: split the unchanged statement in seven steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-derived-pushforward-upper-bound.json: new statement-only node, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-higher-module-image-filtered-colimits.json: new statement-only node, unsplit, no Mathlib match.
- citations.json records verbatim statement quotes for every use in every step.

## Attachments

None. I searched WeilConjectures by the blueprint tag and by derived pushforward/direct sum/coproduct terminology. AlgebraicGeometry.derivedDirectImagePreservesDirectSums in AlgebraicGeometry/DerivedDirectImagePreservesDirectSums.lean concerns schemes on their ringed spaces, not all algebraic spaces on their small etale sites. It also does not state the preservation-of-quasi-coherence clause of this item. It is not an attachment. The generic coproduct and cohomology tools already have DAG nodes and are reused.

## Wanted

None: all sources needed for this split are present under literature/stacks-project/.

## What changed and why

The live item has no proof. Its statement correctly matches spaces-perfect.tex Tags 08FA(1), 08FB and 08F3, and is unchanged. The split localizes on affine etale charts, proves the bounded below quasi-coherence assertion by hypercohomology, removes the lower bound using a uniform upper bound, and proves coproduct compatibility using the canonical spectral-sequence comparison and the same cutoff for the entire family. There is no Noetherian hypothesis or global quasi-compactness assumption on either space.

The two new inputs are strictly smaller facts: the first is the uniform vanishing estimate of 08FA(2), which proves neither of this item's clauses on its own; the second is the underived higher-direct-image filtered-colimit theorem, which has no unbounded complexes in its conclusion. Neither is an elementary consequence of the existing definitions. Their sources are respectively spaces-perfect.tex 08FA(2) (shifted, with N enlarged to at least 1) and spaces-cohomology.tex 07U6 with sites-cohomology.tex 03FD for module coefficients. Both remain statement-only, with no inline proof or proof dependencies.

I retained and read the saved searches and results from the interrupted attempt. All newly recorded search queries have corresponding entries in searches.jsonl. Both phrasings of each LeanFinder query give only underived module pushforward, existence of colimits, t-structure support, or generic derived-functor statements; none specializes in one line to these algebraic-space results. The Loogle and grep hits similarly do not prove the new statements. The item retains the live node's earlier search records and the interrupted attempt's actual new searches. No search was invented or rerun merely because of the interruption.

I read the current blueprint/latest unit and direct-image proof. This item is a downstream general algebraic-space duality prerequisite in the recorded ancestor chain, not the key statement of the unit. The current blueprint's unit-level compactification/direct-image route is not replaced. The inherited unit JSON is older than the current blueprint and its chapter differs from the item's chapter; I did not edit that record or reinterpret it as a requirement that the spaces here be schemes. No repair note exists for this item. No unit realization fields are due from this non-key node.

## Unfinished

The two auxiliary statements are intentionally unsplit and will enter the stage-1 queue. No Lean was written and no compiler, Lake command, or build was run.

## Review by Q70

I read spaces-perfect.tex at the proofs of 08F3, 08FA and 08FB, rather than treating the imported citations as proofs. I also read spaces-cohomology.tex 07U6 and 073G and sites-cohomology.tex 03FD. In 08FA the bounded below spectral sequence is used first, then the independent K-injective upper-bound argument, then the truncation triangle; the split preserves that order. The upper-bound node records the unbounded estimate, not just a bound for sheaves: a sheaf-only bound would not justify the unbounded cutoff. Its source explicitly proves that stronger estimate using nice K-injectives. The filtered-colimit node allows all module sheaves: 07U6 is for abelian sheaves and 03FD identifies cohomology with module cohomology on every slice; module colimits forget to abelian colimits. The resulting canonical comparison is linear because it is formed from linear injections, so bijectivity on underlying abelian sheaves gives a module isomorphism.

Step 1 uses the ringed-site Grothendieck theorem, the derived-coproduct theorem, the cohomology-of-coproducts theorem, the standard truncation definition, and the algebraic-space quasi-coherent kernel/colimit theorem. I checked the statements: the first assumes a small site, now supplied explicitly by the size convention. Exact sums commute with kernels and cokernels, so they commute with good truncations. This is a short computation, not an additional lemma to invent.

Step 2 uses the full derived etale-chart-calculus statement, which gives unbounded etale base change and detection of quasi-coherence, and the canonical module functor definition. Exact slice restriction and sheafified sums identify the comparison by its coprojections. Testing a base-changed morphism by an affine scheme is an affine test of the original map, and its diagonal is the pullback of the original diagonal. Thus qcqs hypotheses persist; the target is affine only locally, and N is chosen only after that localization. No global N on a non-quasi-compact target is asserted.

Step 3 uses thm-sp-truncation-e2 for a left exact additive functor of Grothendieck categories, the higher-direct-image quasi-coherence statement, kernel/cokernel closure and extension closure. I opened each statement: these are the actual conclusions supplied, with no finite type or Noetherian conditions. I added a direct verification of left exactness and additivity of f_* from its specified module limit/adjoint construction. A cohomologically bounded below object is replaced by its good truncation to meet the bounded-complex presentation in the spectral-sequence statement. There are finitely many positions in each total degree, so extension closure is used only finitely many times.

Step 4 uses the new unbounded upper bound, the truncation triangle, triangulatedness of right derived functors and the cohomology long exact sequence. I checked the indices: l=r-N, A=tau_(<=l-1)K, and its higher image vanishes in degrees >=(l-1)+N=r-1, so both degree r and r+1 vanish. This gives the claimed natural degree-r isomorphism. The target is affine at this point and hence quasi-compact, which is the added hypothesis of the upper-bound node.

Step 5 uses the new module filtered-colimit theorem, the module-colimit/forgetful theorem, and the additive right-derived functor. The finite-subset index poset is small and filtered, including the empty subset. Finite sums are biproducts, so additive derived functors preserve them. Taking the filtered colimit proves arbitrary sums with the actual injections. No assumption of quasi-coherence is needed in this input, and no false assertion that a right adjoint preserves arbitrary sums is used.

Step 6 uses the canonical coproduct truncation-couple lemma, thm-sp-truncation-e2, Grothendieck exactness, cohomology of sums, and the short five lemma. I additionally cited lem-sp-derived-couple-functoriality for the page maps. The coproduct-couple node specifies both the E2 comparison and the actual abutment map, avoiding a conclusion about some abstract isomorphism. The image-filtration and graded-isomorphism formulas in the truncation theorem are functorial in the couple structure maps. Exact sums commute with their images/quotients, giving the filtration comparison. For page index t>max(q-a+1,p), incoming and outgoing differentials vanish uniformly in the family; total degree r has filtration length at most r-a+1. Successive short five lemma applications give the specified abutment comparison, not a substitute map.

Step 7 uses cohomology of ambient sums and the localization definition of the derived category, together with the earlier steps. The same l works for every summand and the sum; its natural truncation maps commute with every coprojection, giving the commutative square explicitly described. The roof argument shows conservativity of all cohomology functors directly from the derived-category definition. I checked the empty family, the zero object, f=id (N=1 suffices), a finite family, an unbounded-below family, and a non-quasi-compact target covered by affine charts. All remain covered. For total degrees below the common lower bound, the spectral-sequence terms and abutments vanish. Negative cutoffs and enlarging N cause no sign change in the two required vanishings.

Against delivery-errors B--E, each new statement introduces its objects and coefficient category, every non-elementary input is a statement citation and not a mere tag or a definition used as a theorem, every quote is copied verbatim, and the smaller lemmas do not restate either conclusion. I checked all seven step lengths: none exceeds 2000 characters, and none hides a new comparison lemma. Generic off-unit tools are declared in split_report.tool_uses for maintainer approval; this is use of homological machinery, not an alternative unit route. I corrected the interrupted draft's implicit smallness, missing page-functoriality citation, and unused quasi-coherence dependency in the filtered-colimit node. No statement correction or source dispute was needed.

## Not duplicates

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-flat-space-derived-pushforward-base-change: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Flat algebraic-space derived pushforward and base change, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-proper-space-curve-qcoh-bound: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Quasi-coherent cohomological dimension of algebraic-space curve families, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-qcqs-space-pushforward-right-adjoint: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Right adjoint of quasi-coherent pushforward for qcqs algebraic spaces, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-space-affine-base-higher-image-sections: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Quasi-coherent cohomology over an affine base is higher-image sections, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-space-affine-derived-pushforward-conservative: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Affine derived direct image reflects isomorphisms for algebraic spaces, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-space-affine-pullback-perfect-detection: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Affine pullbacks of perfect objects detect isomorphisms on algebraic spaces, not this vanishing estimate.

lem-sfb-space-derived-pushforward-upper-bound vs lem-sfb-space-derived-pushforward-coproducts: the new node is a uniform upper-vanishing estimate for unbounded quasi-coherent inputs with quasi-compact target; the existing node states Quasi-coherent derived pushforward and its coproduct comparison, not this vanishing estimate.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pqf-open-module-cohomology-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Open module cohomology agrees with cohomology of the restricted abelian sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-abelian-ext-covariant-exact: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Covariant Ext exact sequence in an abelian category, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-external-cup-scalar-balance: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar balance of external cup products, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-external-cup-unit-coefficient-identities: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states External cup with one becomes scalar projection pullback under the unit coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-module-cup-flasque-acyclicity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module-valued flasque acyclicity, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-picard-external-cup-scalar-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar normalization of individual external cup products with unit coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-picard-external-cup-unit-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Unit-class external cup products compare with projection pullbacks, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-picard-qcoh-finite-cd: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite cohomological dimension on affine-diagonal schemes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-scalar-cup-unit-identities: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cup with one on one scheme is the identity on structure-sheaf H1, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-scalar-unit-class-pullback: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Structure-sheaf pullback preserves the degree-zero class of one, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-scalar-unit-cohomology-coordinates: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Normalized scalar coordinates on zeroth unit-module cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-scalar-unit-cohomology-pullback-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states A common module-to-abelian comparison intertwines structure-sheaf pullbacks, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-picard-derived-fibre-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Compatible geometric direct-image fibre comparisons, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-sc-scalar-abelian-ext-factorization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The explicit unit comparison factors through forgotten scalar Ext, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-sc-scalar-abelian-pullback-square: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Forgetting scalars commutes with inverse image and its unit coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-sc-scalar-unit-comparison-family: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Bijectivity of the explicit unit module-to-abelian comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-sc-scalar-unit-pullback-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Pullback compatibility of the explicit unit comparison map, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs pqf-lem-affine-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Vanishing of higher cohomology on affines, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sc-topological-abelian-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cohomology of abelian sheaves on a topological space, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-additive-cohomology-finite-dimensional: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite-dimensionality of the section-induced scalar action on first additive cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-additive-cohomology-scalar-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar-compatible comparison of derived additive etale and ordinary structure-sheaf first cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-etale-qcoherent-source-comparison-natural: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural comparison of lifted tensor-sheaf cohomology with ordinary H, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-etale-zariski-qcoh-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Etale and Zariski cohomology of quasi-coherent modules agree, naturally in the module, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-ga-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Etale and Zariski cohomology agree for quasi-coherent sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-injective-module-abelian-acyclic-zariski: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective module sheaves are acyclic after forgetting to abelian sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-module-abelian-zariski-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cohomology of a module sheaf agrees with that of its underlying abelian sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-module-cohomology-source-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural bridge from module right-derived sections to source ordinary H, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-noetherian-cohomology-above-dimension: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Quasi-coherent cohomology vanishes above the dimension of a Noetherian scheme, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-pic-lift-closed-immersion-dim-le-one: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Invertible modules lift along a closed immersion into a Noetherian space of dimension at most one, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-zariski-module-abelian-cohomology-agree: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cohomology of a Zariski module agrees with that of its underlying abelian sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-cohomology-filtered-colimit: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Filtered colimits of etale cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-etale-module-cohomology-forget: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural comparison of etale module cohomology with underlying abelian cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-etale-module-injective-forget-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underlying abelian acyclicity of injective module-valued etale sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective module presheaf cocycle lifting with larger coefficient universe, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-ringed-site-injective-module-cech-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective module sheaves have vanishing Cech cohomology on a ringed site, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-zariski-module-abelian-cohomology-components: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Componentwise comparison and naturality for module and abelian cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-per-ordinary-kummer-first-chern: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Ordinary derived Kummer first Chern class, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-per-affine-open-strict-local-cd: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Gabber bound for affine opens of an excellent strictly local scheme, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-per-open-closed-constructible-test: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Bounded constructibility detected by open and exceptional closed restriction, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-per-proper-finite-coefficient-bounded-preservation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Proper direct image preserves ordinary finite-coefficient bounded constructibility over a Noetherian base, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-fd-finite-ring-compact-support-finiteness: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Compact-support finiteness for arbitrary finite rings and a finite-type target, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-fd-qbar-cohomology-finite-level-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite-level comparison for constant Qbar-l cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-pc-module-cohomology-ext-resolution-equiv: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Resolution-normalized module/abelian cohomology comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pc-affine-higher-direct-image-cohomology-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine higher direct image cohomology vanishing, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pc-affine-open-higher-direct-image-sections-iso: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states AffineOpenHigherDirectImageSectionsIso, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pc-cohomology-sections-affine-base: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cohomology over an affine base is the global sections of the higher direct images, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pc-k2-leray-acyclic-additive-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Additive Leray comparison natural under coefficient endomorphisms, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pc-m1-leray-acyclic-pushforward-linear-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Base-linear Leray comparison for acyclic direct image, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-affine-basis-restricted-lower-tail-local-bound-aux: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Local vanishing on affine opens for restricted lower tails, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-affine-basis-restricted-lower-tail-local-bound: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Local bound zero for the restricted lower tail, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-ext-coherent-hom-injective-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclicity input for coherent sheaf Ext, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-open-derived-sections-truncation-tower-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Open derived sections respect the canonical truncation tower, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-thm-picard-duality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Serre duality, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-lem-bounded-continuity-direct-image: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Higher direct images commute with bounded-below filtered colimits, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-sf-comparison-affine-continuity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Pro-étale cohomology of a pro-étale affine, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pe-comparison-injective-left-modules-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Comparison pullbacks of injective left-module sheaves are acyclic for arbitrary rings, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pe-left-module-derived-evaluation-forget: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Derived evaluation of arbitrary left-module sheaves commutes with forgetting scalars, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pe-ringed-site-derived-evaluation-slice: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Derived module evaluation is abelian cohomology on the slice, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-lem-pe-injective-acyclicity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclicity of pulled-back injectives, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-pbc-canonical-coherent-etale-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical normalized coherent-etale comparison and transported additive action, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-pc-abelian-counit-cocycle-comparisons: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Fixed abelian counit comparison constructors, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-weil-pbc-etale-cohomology-presentation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical Ext to derived-sections cohomology presentation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-weil-pbc-site-cech-edge-normalization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Augmentation normalization of a chosen general-site Cech edge, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-pbc-conventions-module-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module cohomology is abelian cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pbc-coherent-etale-comparison-morphism: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Dimension shifting for normalized coherent cohomology maps, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pbc-coherent-etale-effacing-sequence: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Simultaneous acyclic sequences on the Zariski and etale sites, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pbc-coherent-etale-normalized-additive-map: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Existence of a normalized additive coherent comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-acyclic-cech-edge-compatibility: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical acyclic Cech edges commute with additive maps, site change, and forgetting module structure, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-affine-cohomology-raw-restriction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Normalized coherent raw evaluation commutes with affine etale restrictions, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-arbitrary-ring-torsion-sheaf-base-change: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective acyclicity gives sheaf-level base change for arbitrary coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-coherent-frobenius-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Frobenius compatibility of the canonical additive/coherent cohomology comparisons, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-cohomology-module-square-compatibility: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underlying abelian cohomology respects a module inverse-image square, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-derived-cohomology-continuity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Continuity for bounded-below etale complexes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-derived-module-underlying-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Derived coefficient-forgetting comparisons respect restriction, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-flat-base-change-affine-dictionary: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Normalized affine cohomology section identifications independent of the resolution lift, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-flat-base-change-resolution-affine-sections: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine-section dictionary for the resolution flat base-change map, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-henselian-finite-pushforward-h1-image: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite constant pushforward H1 classes have zero image in restricted injectives, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-henselian-finite-pushforward-h1-injective-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective module H1 vanishing, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-etale-module-cech-h1: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states First Cech cohomology of an injective ModuleCat-valued etale sheaf vanishes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-module-abelian-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective module sheaves are acyclic as abelian sheaves on every object, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-module-annihilator-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclicity of the annihilator of an integer in an injective module sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-module-direct-image-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Higher direct images of an injective module sheaf vanish, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-injective-module-sheaf-H-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Sheaf.H acyclicity of an injective ModuleCat-valued sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-killed-sheaf-module-lift: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Lift an annihilated abelian sheaf to constant-ring-valued module sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-module-abelian-derived-direct-image-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical derived direct image comparison for forgotten module coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-module-abelian-derived-exchange-compatibility: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical coefficient comparisons intertwine derived exchange, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-module-abelian-stalk-exchange: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Forgetting module coefficients in the stalk of derived exchange, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-module-acyclic-cohomology-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclic-resolution comparison for underlying abelian sheaves of prime modules, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-module-sheaf-constant-ring-equivalence: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states ModuleCat sheaves and sheaves of modules over the constant ring sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-p1-original-stalk-total-cohomology-exchange: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Original geometric-stalk exchange on total strict-local cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-p1-strict-local-stalk-exchange-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Stalk exchange under compatible pointed strict localization, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-prime-injective-cohomology-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Prime-module acyclic-resolution comparison criterion, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-qcoherent-comparison-degree-zero: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Degree-zero normalization of the fixed large module comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-qcoherent-normalized-comparison-exists: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Existence and uniqueness of the normalized comparison on a quasi-compact separated scheme, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-qcoherent-normalized-pullback-square: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The normalized comparison commutes with the canonical pullback cohomology maps, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-qs-scheme-cohomology-directed-colimit: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cohomology on a quasi-compact open commutes with directed colimits of modules (Stacks 01FF, for schemes), not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Direct image of an injective module is acyclic for object evaluation on a ringed site, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module and abelian cohomology over an object of a ringed site agree, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-site-module-sheaf-constant-ring-equivalence: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Constant-ring module sheaves and module-valued sheaves on a small site, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-weil-pbc-strict-local-total-cohomology-exchange: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Strict-local stalk exchange on total-space cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lemma-weil-pbc-gabber-effacement: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine Gabber effacement (Stacks 09ZE), not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-abelian-counit-cocycle-calculation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cocycle calculation with an abelian injective target, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-abelian-counit-resolution-calculation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Abelian Ext counit computed on a fixed abelian resolution, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-abelian-replacement-section-homotopies: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Two section-complex homotopies for a module replacement, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-abelian-resolution-comparison-evaluation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Evaluation of the target acyclic-resolution comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-affine-cohomology-section-equiv: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Normalized affine Leray section equivalence before scalar extension, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-coherent-etale-comparison-pullback: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical coherent-etale comparison respects structural pullback, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-coherent-frobenius-pullback: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Coherent structural pullback commutes with additive power maps, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-coherent-power-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Coherent power semilinearity and normalized etale power comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-flat-base-change-affine-canonical-comparisons: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical affine cohomology section comparisons without flatness, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-flat-base-change-affine-source: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Source affine dictionary, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-flat-base-change-affine-target: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Target affine dictionary, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-flat-base-change-target-leray-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Target affine Leray comparison compatible with a natural source Ext comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-acyclic-comparison-zero: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module comparison in degree zero without acyclicity, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-acyclic-effacement-ladder: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective effacement gives a right exact pullback ladder, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-acyclic-underlying-sections: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Forgetting coefficients preserves bijective section restriction, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-edge-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural module/Ext comparison for the direct-image edge map, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-pullback-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural module/Ext comparisons intertwining the scalar-extension unit, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-resolution-edge: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Edge compatibility of the concrete module/Ext resolution equivalence, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-resolution-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Coefficient naturality of the concrete module/Ext resolution equivalence, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-resolution-normalization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Resolution normalization for arbitrary module injective resolutions, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-section-diagram: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Abelian Ext map in the common section-complex diagram, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-sections-factorization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Ext source-change and site-sections cancellation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-ext-standard-resolution-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Evaluation of the fixed module/Ext comparison on its standard resolution, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-cohomology-standard-sections-factorization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module sections component on the standard resolution, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-module-valued-injective-cohomology-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Compare injective module-valued sheaves with constant-ring modules and derived evaluation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs new-standard-abelian-ext-section-diagram: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Standard-source abelian Ext section calculation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs prop-weil-pbc-p1-strict-henselian-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Strictly henselian $\mathbf P^1$ comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs prop-weil-pbc-projective-line: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Projective-line proper base change, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-def-pbc-conventions: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Conventions for proper base change, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-thm-properbasechange: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Proper base change on classical pro-étale complexes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-wf-finite-coefficient-cup: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical constant/roots cup on ordinary finite-coefficient cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-wf-ordinary-etale-cup: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Ordinary integral cup product on arbitrary abelian etale sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-geo-open-finiteness-ii-amplitude: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Bounded amplitude of open direct image on classical torsion sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-proper-heart-bound-lattice: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The lattice bound $2d+1$, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-proper-heart-bound-rational: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The bound for constructible sheaves with rational coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-closed-immersion-cokernel-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Linear cohomology sequence for a closed-immersion cokernel, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-closed-subcurve-dualizing-adjunction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Dualizing module of a reduced closed subcurve as an annihilator, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-coherent-regular-hyperplane-restriction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states A common regular hyperplane and twisted cohomology restriction sequences, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-etale-module-affine-bound: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Uniform affine étale cohomology bound for finite coefficient module sheaves, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-constant-unit-restriction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The finite constant-module open unit induces the actual abelian derived restriction, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-etale-open-uniform-tor-image: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Uniform finite-coefficient etale open-image Tor bound, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-normed-scalar-section-acyclicity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Sectionwise acyclicity of finite norm-topological scalar coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-proper-classical-neighborhood-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Classical torsion cohomology bound on proper weakly contractible neighborhoods, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-ring-injective-abelian-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite-ring injective module sheaves are abelian-cohomology acyclic, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-finite-subextension-derived-function-columns: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite-subextension-valued derived function columns with normalized scalar comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-free-functions-colimit-model-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Quasi-isomorphism criterion for colimits of free representable function resolutions, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-free-representable-derived-functions-model: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Derived functions on a free representable module as sheafified derived sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-module-resolution-derived-presheaf-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module injective resolutions compute derived abelian presheaf inclusion, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-norm-algcl-bar-augmentation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underived-to-derived procyclic bar augmentation for noncomplete norm scalars, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-normed-scalar-profinite-hom-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underived continuous functions compute derived internal functions of profinite parameters, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-profinite-derived-functions-filtered-colimit: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Filtered-colimit continuity of derived functions on profinite parameters, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-profinite-invariants-sheafified-cohomology: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Sheafified action-site cohomology computes higher internal invariants naturally, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-proper-wcontractible-closed-fibre-rigidity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Proper cohomology restriction to the closed-point scheme of a weakly contractible test base, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-qcoh-cohomology-etale-pullback-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Etale-pullback naturality of the canonical quasi-coherent cohomology comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-ringed-site-cohomology-fmap-calculus: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Resolution-normalized cohomology maps for coefficient maps on ringed sites, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-space-affine-base-higher-image-sections: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Quasi-coherent cohomology over an affine base is higher-image sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-space-affine-module-higher-image-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine space morphisms are acyclic for quasi-coherent module direct image, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-space-surjective-qcoh-limit: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Limits and affine sections of surjective quasi-coherent towers, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-split-thickening-picard-cocycle: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Infinitesimal line bundles on a split thickening and their cocycles, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-square-zero-picard-obstruction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The Picard obstruction exact sequence for an arbitrary square-zero thickening, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-torsion-open-test-devissage: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Cyclic open units give arbitrary bounded-primary torsion restriction on contractible tests, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-unbounded-site-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Unbounded comparison: full faithfulness and sums, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-zariski-square-zero-scheme-realization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Zariski square-zero ring-sheaf extensions with quasi-coherent kernel are schemes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sfb-zero-dimensional-base-affine-global: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine-to-global pro-etale cohomology bound over a zero-dimensional affine base, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sbc-etale-complex-cohomology-presentation-data: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Single-constructor existential data of a complex cohomology presentation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sbc-etale-complex-cohomology-presentation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Abelian complex presentation of a cohomology cocone, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sbc-higher-image-raw-diagram: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The raw cohomology diagram and cocone, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sbc-raw-class-native-morphisms: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Native derived morphisms represented by raw cohomology classes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-sbc-raw-module-abelian-hom-map: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The explicit scalar-forgetting map of raw derived Hom, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-canonical-restrict-scalars-functor-comparisons: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical inverse- and direct-image coefficient comparisons, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-coefficient-higher-direct-image-zero: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Restriction of scalars detects vanishing of higher direct images, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-constant-module-higher-direct-image-cyclic-reduction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Transfer higher-direct-image vanishing from cyclic groups to constant module coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-constant-module-higher-direct-image-local-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Vanishing for constant module coefficients from local cyclic cohomology annihilation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-derived-hom-comparison-surjective: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Surjective derived Hom comparison by effacement, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-derived-source-comparison-injective: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Derived source comparison detects classes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-higher-direct-image-forget-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underlying abelian sheaf commutes with higher direct image, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-higher-image-raw-complex-presentation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Raw cohomology admits an abelian complex presentation, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-higher-image-raw-pullback-functorial: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Functorial additive raw cohomology pullback, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-injective-module-forget-evaluation-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Existing evaluation acyclicity for large constant coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-prime-cyclic-detection: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Prime cyclic detection after forgetting geometric-point coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-prime-quotient-detection: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Prime cyclic coefficient is a retract of a nonzero ring quotient, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-qcqs-higher-images-prime-torsion: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Qcqs higher direct images preserve a fixed set of torsion primes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar forgetting for raw derived Hom before restricted cohomology, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-map-injective: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Injective fixed raw scalar comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-map-is-iso: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The fixed raw scalar comparison is invertible, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-map-naturality: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The fixed raw scalar comparison intertwines pullback, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-map-surjective: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Surjective fixed raw scalar comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-source-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module source and class factors after scalar forgetting, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-abelian-hom-target-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Abelian expansion of the scalar raw class, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-free-source-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclicity for the pulled-back free abelian source, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-free-source-hom-bijective: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Explicit underived free-source comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-restricted-abelian-natural-iso: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Natural scalar-forgetting comparison for raw derived Hom, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-restricted-abelian-negative: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar-forgetting comparison (negative), not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-restricted-abelian-nonnegative: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar-forgetting comparison (nonnegative), not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-module-scalar-hom-composite-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Scalar Hom map after module raw pullback expansion, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-scalar-hom-evaluation: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Evaluation of the explicit additive scalar Hom map, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-scalar-pullback-abelian-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Abelian factorization component, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-scalar-pullback-formulas: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Factorization of the two explicit raw pullbacks, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-raw-scalar-pullback-module-formula: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Module factorization component, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sbc-restrict-scalars-injective-direct-image-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Restricted injective module sheaves are acyclic for étale direct image, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-algclosed-extension-injective-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Acyclicity of injective finite-torsion coefficients after scalar extension, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-sc-qcqs-algclosed-extension-invariance: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Qcqs constant-coefficient invariance assembled by dimension shifting, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-affine-class-descent: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Stage representatives for affine higher-image sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-affine-class-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Eventual zero of affine higher-image sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-affine-continuity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine evaluation of the higher-image limit cocone, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-colimit-comparison-epi: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Local surjectivity of the canonical higher-image sheaf-colimit comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-local-class-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Local eventual zero of higher-image sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-raw-affine-class-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Raw affine cohomology classes eventually vanish, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sbc-lem-higher-image-raw-affine-image-rep: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Affine raw module-cohomology classes have stage representatives after comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-thm-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Vanishing in the universal curve test, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs cor-fin-deligne-open-finite-coefficients: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Open direct images with arbitrary finite allowable coefficients, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-kun-scalar-restriction-comparison-maps: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Canonical ambient derived scalar restriction comparison maps, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs def-pur-etale-module-abelian-forget: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Underlying abelian etale sheaf of a module sheaf, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-sp-tower-injective-components: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Components of injective towers are acyclic, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-exc-open-complement-known: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The open-complement condition from the direct-image input, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-kun-0f1j-prime-torsion-coefficient-reduction: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Prime-torsion coefficient reduction for the punctual tensor comparison, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-kun-flat-coefficient-tensor-exchange-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Flat coefficient tensor exchange commutes with restriction of scalars, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-compact-point-source-normalization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Section-one normalization of compact cohomology of a closed rational point, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-etale-arbitrary-field-open-complement-control: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Arbitrary-field control of complementary-open module direct images, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-etale-finite-tor-direct-image-coefficients: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite-Tor direct image and scalar projection over an arbitrary field, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-kummer-additivity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Kummer additivity, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-module-restriction-kernel-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Forgetting constant module coefficients compares derived restriction kernels, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-origin-class-projective-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Comparison of the supported affine-origin class with the projective Chern generator, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-relative-kummer-coefficient-normalization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Finite Kummer coefficients and normalization of scalar-forgetting maps, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-relative-kummer-site-normalization: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Etale/pro-etale comparison normalized on scalar Kummer classes and mates, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-strict-local-constant-unit-criterion: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Strict-local criterion for constant module direct-image units, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-pur-supported-root-scalar-site-comparison: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Supported root-class scalar extension and site comparison with normalized units, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs prop-sf-comparison-bound-zero: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states The comparison bound on coefficients of étale origin is $M=0$, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-lem-sp-tower-levels: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Levels of the tower direct image, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs thm-pur-with-support-exactness: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Long exact sequence for cohomology with support, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs det-tf-transverse-corner-vanishing: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Vanishing at the transverse corner, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-trf-integral-filtration-euler-difference: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Euler differences evaluated along an integral-ideal filtration on a proper curve, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-trf-module-pullback-injective-section-acyclic: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Pulled-back injective modules are acyclic for object sections, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-trf-oriented-derived-cohomology-continuity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Continuity of bounded-below cohomology of oriented etale products, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs lem-trf-smooth-source-constructible-local-acyclicity: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Smooth source local acyclicity for constructible complexes, not this comparison.

lem-sfb-space-higher-module-image-filtered-colimits vs sk-lem-tf-transverse-boundary: the new node concerns higher module direct images under qcqs algebraic-space maps and arbitrary filtered diagrams; the existing node states Transverse boundary calculation, not this comparison.

The whole-DAG tag and keyword searches and blueprint_refs searches found no node stating either new assertion. Scheme-only direct-image bounds and cohomology/colimit lemmas do not cover algebraic spaces without an additional comparison argument; the existing algebraic-space chart, quasi-coherence and closure statements are cited directly instead of duplicated.
