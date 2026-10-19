## Worker report

Files written:

- `dag/nodes/sec-six-functors/lem-pur-frobenius-trivialization-pullback.json`: repaired statement node; no Mathlib leaf.
- `dag/nodes/sec-six-functors/lem-sf-proetale-tensor-composition-unit.json`: new statement-only dependency; Mathlib searches found no exact match (the abstract `SheafOfModules.conjugateEquiv_pullbackComp_inv` candidate does not state the explicit tensor formula).
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

Attachments: none.

WANTED: none.

The maintainer returned the earlier delivery because step 4 had 2981 characters and hid several lemmas. I kept the item's statement, Lean record, route, source, and steps 1–3 and 5–6 unchanged. I replaced step 4 with a 1579-character argument that cites the existing site-composition unit normalization, a new statement-only lemma for the explicit inverse-image/tensor comparison, and the existing mate-pasting and conjugation statements. The new lemma is strictly smaller than the item: it concerns only the ordinary module pullback comparison and its adjunction-unit equation, with no Frobenius trivialization or pullback naturality conclusion. I searched the DAG and blueprint for existing statements before creating it; the related site-composition, inverse-image, module-adjunction, and mate nodes state neighboring general facts but not this explicit tensor comparison. I ran all required searches for the new node and recorded their actual results in its `mathlib_searches`; no SGA source is used.

## Review by Q02

I read the retained item against the current repository node and the source material in Stacks `more-morphisms.tex` Tag 0F6W and the current blueprint proof files for `lem-trf-absolute-frobenius-site` and `def-pur-scheme-geometric-frobenius`. The item statement and its Lean record are byte-for-byte unchanged. I read every statement cited by the repaired step and verified that each says the fact taken from it: `lem-weil-pbc-site-morphism-composition` gives the inverse-image comparison carrying the composite unit to the direct unit; `def-weil-proetale-inverse-image` supplies the site base-change functors; `lem-sf-proetale-tensor-composition-unit` states the explicit tensor comparison and its module-unit equation; `def-weil-pbc-composite-adjunction` supplies the composite adjunction; `lem-weil-pbc-conjugate-iso-unit-equation` supplies uniqueness by the right-adjoint comparison; `lem-weil-pbc-mate-pasting` computes the pasted mates; and `def-weil-pbc-adjunction-conjugate` gives injectivity and composition of conjugation. The remaining proof steps retain their prior citations and quotes, and `citations.json` contains a verbatim quote for every use in all six steps.

For the new node I checked the hypotheses: arbitrary composable scheme maps with the specified small pro-etale sites, compatible ring-sheaf maps, and the exact tensor pullback from `def-weil-pbc-proetale-operations`. Its local formulas use only inverse-image composition, scalar associativity/balancing, and the fibre-product universal property, and the displayed unit equation is exactly the needed normalization. I tested identity maps and zero coefficient rings conceptually; the formula reduces to the identity comparison in both cases. Mathlib searches were run with `leanfinder`, `leansearch`, `loogle`, and Mathlib-source `grep`; the only relevant hits define an abstract adjoint comparison and do not state this explicit construction, so the node remains unsplit. The new step is below the 2000-character review threshold, and no cycle is introduced because the new node depends only on pre-existing definitions and lemmas.

The repair addresses the return directly: the formerly long step 4 is now a short proof using named statements for each hidden argument, while the item's statement and other proof steps remain unchanged.

I also checked the unchanged steps with the cited statements open:

1. `def-weil-proetale-inverse-image` supplies base change of site objects; `def-pc-fibre-product` supplies equality by projections; `def-weil-absolute-frobenius-scheme` supplies the sectionwise power map. The geometric input from `lem-trf-absolute-frobenius-site` explicitly includes Tag 0F6W for every weakly etale object, so the induction on the exponent uses its statement, not a construction hidden in its proof. No reducedness or perfectness is used.
2. `def-weil-pbc-proetale-operations` explicitly states the module adjunction; `prop-weil-pbc-proetale-constant-ring-map` identifies the structure map preserving constants, and `def-weil-pbc-proetale-site` defines constant coefficients by sheafification. Thus restriction along r is linear. The conjugate-unit lemma with the identity adjunction fixes the direction of s; the definition of composite/identity adjunctions gives the exponent-zero normalization. The elementary argument on constant sections also supplies compatibility of the coefficient maps for a composite.
3. The two projections in `def-pc-fibre-product` give the displayed j and equality with the base-changed r; applying the direct-image formula in `def-weil-proetale-inverse-image` contravariantly gives d_Y e = R(d_X). This is a direct calculation on morphisms, not an assertion that the Frobenius square is Cartesian.
4. For the new categorical citation I checked the actual specialization of pasting clause (2): paste s_Y:P→id with the identity square for L⊣R to obtain the conjugate d_Y^{-1}R of Ls_Y; paste the identity square for L⊣R with s_X:S→id to obtain R(d_X^{-1}) for s_XL. Composition of conjugates then gives e R(d_X^{-1}), so the inverted step-3 identity proves equality by injectivity. This is precisely the same two transposes as in the returned proof, without repeating their Hom calculation inline. The composition comparison is normalized by the new node, so this is the canonical comparison needed later, rather than an arbitrarily chosen one.
5. The addition law first checks the two projections of the iterated relative Frobenius, using exactly the fibre-product and absolute-Frobenius definitions. The composite-adjunction Hom bijection and the conjugate-unit equation then give H_2(d_1^{-1})d_2^{-1}, in the stated order. I checked the order against the contravariance of section restriction. This 1874-character step is a single explicit projection-and-adjunct calculation, with no additional independent comparison theorem hidden in it; the required normalization is now supplied by step 4.
6. `def-weil-pbc-proetale-operations` explicitly gives exactness and termwise derived pullback for identified coefficients. `lem-weil-pbc-localization-universal-property` clauses (2),(3) descend isomorphisms and detect their equality. `lem-weil-pbc-proetale-derived-pullback-composition` fixes the comparison on K-flat complexes with flat terms; `lem-pc-kflat-resolution` supplies exactly such a resolution of every complex. Naturality along that quasi-isomorphism identifies the descended comparison on every object. The fixed small-skeleton convention is in the cited site definition. This is a single resolution-and-naturality argument, with no extra existence assertion left uncited.

For the new node, I read Stacks `sites-modules.tex`, label `lemma-adjoint-push-pull-modules` (Tag 03D3), and the preceding module pullback construction; `sites.tex`, label `lemma-composition-morphisms-sites` (Tag 03CB), supplies the existing site-composition result. I also read the colimit coprojection and adjunction formulas around `lemma-recover` and `lemma-adjoints-u` (00VE), and `categories.tex` labels `lemma-transformation-between-functors-and-adjoints` (0B65) and `lemma-compose-counits` (0DV0). The source does not state the explicit tensor/composition unit comparison verbatim; the new node correctly labels it as an agent deduction. Its content is the compatibility between the inverse-image module action, extension of scalars, and the specified module adjunctions. Scalar balancing alone verifies only that the formulas are inverse; the adjunction normalization is an additional comparison theorem, which is why it is extracted rather than marked elementary. The tensor formula is compatible with restriction, so it is a sheaf map after sheafification, not merely a formula on global pure tensors.

Small cases checked further: an empty scheme (all relevant module sections are zero), a nonreduced characteristic-p base (r is an isomorphism by weak etaleness, not by invertibility of absolute Frobenius on the base), b=0, u=id, and either exponent zero in the addition law. For the new node I also checked a nonidentity ring isomorphism c_h: the intermediate scalar is carried by c_h in the multiplication formula, and insertion of 1 gives its inverse, so the statement does not silently assume c_h=id.

Before creating the child I searched the whole DAG by `03D3`, `03CB`, composition/unit/tensor and conjugate terminology, ran the blueprint searches `conjugate`, `pullback composition`, `mate`, `colimit composition unit`, and `tensor composition`, and searched the project Lean source for the item tag, Frobenius trivialization and composition normalization. No exact project declaration for the item or explicit tensor normalization was found. All same-tag nodes are distinguished below. In particular I reused the general site composition and mate-pasting statements, rather than creating the two proposed generic duplicates. Mathlib's `SheafOfModules.pullbackComp` at PullbackContinuous.lean:167 is defined by `Adjunction.leftAdjointCompIso`, while its `pullback` at :53 is an abstract chosen left adjoint. Its normalization theorem at :177 therefore does not by itself identify the different, explicit inverse-image/tensor presentation required here. That is recorded as a candidate, not a claimed finished leaf.

No statement correction was needed. No compiler, Lake, Lean-writing, direct repository git command, or agent delegation was used. The retained sandbox initially contained only the item JSON, so there was no earlier report, citation file or search log to discard. The initial dry run reported the missing report; this repair supplies it and will be validated by the required full dry run.

## Not duplicates

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-single-coefficient-composition: The existing statement concerns composition of restricted single-complex coefficient maps; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-composition-law: The existing statement concerns composition law for restricted single transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-abelian-raw-pullback-coherence-extend: The existing statement concerns cocone extension of raw pullback coherence; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-unit-lift: The existing statement concerns lift a restricted coefficient unit to its single complex; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-abelian-raw-pullback-coherence: The existing statement concerns coherent natural raw pullbacks for varying abelian coefficients; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-abelian-raw-pullback-composition: The existing statement concerns composition of varying-coefficient raw pullbacks; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-transition-laws: The existing statement concerns unit and composition laws for the explicit restricted transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-cone-naturality: The existing statement concerns naturality of the explicit restricted cone comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sc-etale-module-set-pullback-comparison: The existing statement concerns canonical module-to-set etale inverse-image comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-sc-cartesian-chart-class-pullback-core: The existing statement concerns canonical derived pullback of a class with pulled-back source; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-sbc-raw-module-abelian-hom-map: The existing statement concerns the explicit scalar-forgetting map of raw derived hom; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-raw-affine-complex-system-map-coherence: The existing statement concerns identity, composition and cone equations of canonical complex cohomology maps; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-raw-module-free-source-hom-bijective: The existing statement concerns explicit underived free-source comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-cone-leg: The existing statement concerns compatibility of the explicit restricted cone comparison with colimit legs; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-sbc-raw-module-scalar-pullback-comparison: The existing statement concerns canonical scalar forgetting and inverse-image comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-restricted-affine-single-identity-law: The existing statement concerns identity law for restricted single transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-sbc-restricted-affine-single-maps: The existing statement concerns explicit restricted single-complex transitions and cone comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-raw-triangle-pullback-composition: The existing statement concerns raw triangle pullback composition with arbitrary derived coefficient maps; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sc-cartesian-chart-class-pullback-zero: The existing statement concerns pullback of the zero chart class; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-abelian-raw-pullback-identity: The existing statement concerns identity of varying-coefficient raw pullback; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sbc-abelian-raw-pullback-coherence-base: The existing statement concerns base coherence of raw pullbacks; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-sc-cartesian-chart-lift-naturality: The existing statement concerns canonical chart cohomology lifts commute with stage transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-strict-local-module-sections-set-equiv: The existing statement concerns canonical module/set equivalence of strict-local terminal sections; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-section-comparison-laws: The existing statement concerns coherence of canonical etale section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-sets-sheaf-comparison: The existing statement concerns sheaf-level unit and composition comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-square-iso-pasting: The existing statement concerns identity and pasting laws of the sheaf-level square isomorphism; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-terminal-cone: The existing statement concerns terminal section transport commutes with a diagonal cone map; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-inverse-image-composition: The existing theorem is for abelian sheaves on small etale sites; the new one compares explicit tensor pullbacks for compatible ring sheaves on pro-etale sites.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-proetale-model-ring-presentation: The existing theorem presents one transported ring inverse-image unit; it has no module tensor comparison for a composite.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-inverse-image-action-adjunction: The existing statement constructs the underlying comparison for one site functor with a ring-unit presentation; it does not identify the two-map tensor composition comparison.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-fpqc-matching-sections-pullback: The existing statement concerns matching global sections remain equal along any cone; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-coefficient-product-composition-component: The existing statement concerns composition calculation at one outgoing-arrow factor; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-module-ring-iso-adjunction: The existing statement transports the linearity criterion across a ring isomorphism for one map; the new one identifies composition of explicit tensor pullbacks with the specified composite-adjunction unit.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-global-section-square: The existing statement concerns global inverse-image sections respect a commutative square; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-derived-module-underlying-comparison: The existing statement concerns derived coefficient-forgetting comparisons respect restriction; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-open-square-diagram-identity: The existing statement concerns identity coefficient law across a diagram of commuting restriction squares; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-affine-etale-restriction-composition-mates: The existing statement concerns unit-preserving affine composition mates and restriction coherence; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-inverse-image-module-linear-criterion: The existing statement concerns linearity is preserved and reflected by the etale abelian adjunction; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-coefficient-product-transition-laws: The existing statement concerns identity and composition laws for explicitly constructed outgoing-arrow product transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-etale-set-constant-pullback-comparison: The existing statement concerns constant comparison for constructed etale inverse image; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-geometric-module-transport: The existing statement restricts a single adjunction to linear maps and explicitly asserts no tensor adjunction; the new statement concerns composition of the tensor pullbacks.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-coefficient-product-identity-component: The existing statement concerns identity calculation at one outgoing-arrow factor; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-fpqc-agreement-sections-overlap: The existing statement concerns the two canonical equality predicates coincide on a double overlap; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-module-inverse-image-action: The existing statement concerns scalar actions on the constructed abelian inverse image; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-sets-terminal-transport: The existing statement concerns terminal section transport for a triangle of schemes; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-sets-terminal-restriction: The existing statement concerns terminal inverse-image restriction for an etale object; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-module-pullback-forget-naturality: The existing statement concerns naturality of etale module pullback under forgetting coefficients; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-terminal-transition: The existing statement concerns terminal section identifications commute with etale transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-weil-pbc-sites-and-cohomology: The existing statement concerns sites, morphisms of sites and cohomology on an object of a site; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-inverse-image-module-counit-linear-lift: The existing statement concerns the transported abelian counit lifts to a module map; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lemma-weil-pbc-etale-pullback-forget-modules: The existing statement concerns étale pullback commutes with forgetting constant-ring module coefficients; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-module-inverse-image-transport: The existing statement concerns transport of the module lift along a constant-ring comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-section-comparison-equal-open: The existing statement concerns agreement open for canonical etale inverse-image section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-mayer-vietoris-module-exact-segment: The existing statement concerns exact mayer--vietoris segment for module-sheaf pullbacks; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-mayer-vietoris-module-vanishing: The existing statement concerns two-open mayer--vietoris vanishing for inverse images of module sheaves; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-affine-etale-restriction-composition-gamma: The existing statement concerns affine base-change composition lifts through full affine inclusion; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-cartesian-unit-equality: The existing statement concerns equality of unit sections on a cartesian etale object; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-strict-local-module-sections-set-transport: The existing statement concerns representative compatibility of strict-local coefficient and symmetry transport; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-site-system-finite-coverings: The existing statement concerns finite covering transport across evaluation equivalences; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-set-constant-transport-generators: The existing statement concerns compositional transport on constant generators; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-site-morphism-composition: The existing statement gives composition and unit compatibility on sheaves of sets/abelian groups and is reused in the item; the new statement identifies the explicit module tensor formula with that adjunction normalization.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-section-comparison-naturality: The existing statement concerns restriction naturality of canonical section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-abelian-underived-exchange: The existing statement concerns coefficient forgetting respects underived exchange; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-inverse-image-unit-comparison: The existing theorem compares a single chosen module pullback with its underlying abelian inverse image; the new statement normalizes the explicit tensor comparison for a pair of composable maps.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-section-comparison-identity: The existing statement concerns identity for a canonical etale section comparison; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-direct-image-composition-coherence: The existing statement concerns associativity and unit laws of the composition isomorphisms of direct images; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-constant-pullback-identity-coherence: The existing statement concerns constantpullbackidentitycoherence; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-proetale-module-specialization-unit: The existing statement concerns module unit on an affine weakly contractible closed specialization neighbourhood; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-pullback-section-comparison: The existing statement concerns underlying sets of module pullback section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-affine-local-acyclic-open-restriction: The existing statement concerns affine-local acyclicity is inherited by open restriction; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-compatible-pullback-sheaf-system: The existing statement concerns compatible pullback sheaves form a system and become constant on a cone; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-affine-etale-restriction-composition: The existing statement concerns composition coherence of unit-preserving affine etale restriction comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-flat-ringed-diagram-restriction: The existing statement compares restriction of scalars with derived operations on a diagram for one geometric morphism; the new statement is an underived composition comparison for two geometric morphisms.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-etale-inverse-image-composition-units: The existing statement concerns composition isomorphisms of etale inverse images of sheaves of sets, with units; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-constant-pullback-composition-coherence: The existing statement concerns constantpullbackcompositioncoherence; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs new-lem-weil-pbc-proetale-module-inverse-image-unit-comparison: The existing statement says the abelian adjunct of a single module unit is invertible; the new statement equates the two-map tensor comparison with the normalized adjoint comparison.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-set-constant-transport-identity: The existing statement concerns identity transport of arbitrary constant-sheaf maps; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-abelian-inverse-image-comparison: The existing statement concerns canonical module-to-abelian inverse-image comparison is invertible; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs new-strict-henselian-stalk-sections-comparison-functor: The existing statement concerns same-universe abelian etale inverse-image adjunction; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-local-stage-image-equations: The existing statement concerns etalesetlocalstageimageequations; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-directed-etale-section-identifications: The existing statement concerns identification of section comparisons on an etale upper tail; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-proetale-module-inverse-image-comparison: The existing theorem compares the underlying sheaves and scalar graphs for one module inverse image; the new theorem identifies the explicit two-map tensor comparison with its conjugate normalization.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-proetale-module-inverse-image-underlying: The existing theorem asserts a natural underlying-abelian comparison for one chosen module inverse image, without the two-map explicit tensor composition unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-abelian-pullback-global-sections-comparison: The existing statement concerns abelian inverse-image global sections and set section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs new-lem-weil-pbc-proetale-module-canonical-unit: The existing statement asserts a canonical unit comparison for one module inverse image; it has no explicit tensor composition map or composite-unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-module-inverse-image-action-of-presentations: The existing statement concerns constructing an inverse-image module action from two unit presentations; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-sets-section-comparison-composition: The existing statement concerns composition for canonical etale section comparisons; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-limit-scalar-section-map-laws: The existing statement concerns coherence of descended scalar section maps; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-site-system-finite-sheaf-transport: The existing statement concerns continuity and exact sheaf pullbacks for finite coverings; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-etale-coefficient-product-embedding-compatibility: The existing statement concerns compatibility of explicit product embeddings with the coefficient transitions; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-inverse-image-module-adjunction: The existing theorem supplies the etale module adjunction for a single inverse image; the new theorem compares explicit tensor pullbacks along two composable pro-etale maps.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-proetale-module-inverse-image-scalar-graph: The existing theorem gives scalar graph compatibility for one inverse image, not the composite tensor map and its adjunction-unit normalization.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-inverse-image-module-unit-linear-lift: The existing statement concerns the transported abelian unit lifts to a module map; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-cbc-comparison-matching-transport: The existing statement concerns matching families give the fpqc compatibility equation; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-pullback-finite-locally-constant: The existing statement concerns pullback of a finite locally constant etale sheaf; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-derived-unit-leray-id: The existing statement concerns derived unit and leray identity; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-derived-unit-leray-comp: The existing statement concerns derived unit and leray composition; it does not identify the explicit module tensor comparison for two composable pro-etale maps with its composite-adjunction unit equation.

lem-sf-proetale-tensor-composition-unit vs def-sfb-module-upper-star-comp: The existing definition concerns condensed coefficient module objects and defines its comparison as a conjugate. The new node proves that the explicit ordinary ring-sheaf inverse-image/tensor comparison has that normalization.

lem-sf-proetale-tensor-composition-unit vs lem-weil-pbc-mate-pasting: The existing generic categorical theorem computes pasted mates and is reused; it contains no comparison between the tensor construction and adjunction-normalized module pullback.

