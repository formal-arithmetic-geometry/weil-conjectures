# Q116 stage-1 delivery

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-finite-etale-generic-field.json`: statement, split in seven steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: one entry for every step/node pair, quoting the entire cited statement verbatim so its hypotheses remain visible.
- `searches.jsonl`: searches actually run with the authorized msearch.py command. The sandbox also contains prepare.py, which produces only the sandbox JSON and citations.

## Attachments

None. Searched the project under lean/WeilConjectures for the blueprint tag and for generic fibres, functionField with etale, and related finite morphism declarations. FunctionFieldLimit, Curve.DivisorPullback and Morphisms.FiniteEtaleOpenGenericAlgebra provide related constructions but no declaration states the full item. In particular exists_finiteEtale_open_generic_algebra gives an embedding into some finite etale algebra, not the identification with the source's own function field and its two projections.

## WANTED

None for this split. All Stacks sources used are present locally. The inherited ancestor's wanted de Jong PDF is unnecessary for this elementary algebraic-geometric input, whose statement is independent of the alteration construction.

## Corrections and provenance

The item arrived statement-only. Its mathematical statement is correct, and no hypothesis or conclusion has changed. I added definition references for the tensor product and localization already appearing in its statement and the matching statement dependencies. I did not change its maintainer-owned source, created, chapter, unit or blueprint provenance fields.

The item and its parent already carry blueprint.from.node = null. Running tools/blueprint_refs.py ancestor on this item confirms None. Its inherited place precisely names det-thm-sf-ctf-stability-direct-images proof (3), de Jong section 3.5, and the returned parent's hidden generic-field step. I retained that existing place and via list and recorded the limitation in split_report.blueprint. The chapter is sec-six-functors-basics while its inherited unit record sk-thm-sf-ctf-stability belongs to sec-six-functors; I read both records and preserved their ownership. This input completes the parent's chosen normalization/component route and does not replace a unit step.

I searched the whole DAG by titles and statements, by Tags 01RV, 02GL and 0CC1, and the blueprint with blueprint_refs searches for finite etale generic, generic fibre, fraction field, and finite separable. The existing function-field-affine-fraction leaf and etale residue-field leaf prevent unnecessary new nodes. The more general dominant-affine-chart-data result assumes a locally Noetherian target and cannot be applied here. The parent's finite-etale-normal-generic-components result depends on this item and is not used, so there is no circular shortcut. The flat-curve-pullback-function-field and birational-generic-localization nodes concern different hypotheses and are unnecessary.

New Mathlib searches used both semantic services, Loogle and source grep, with a second phrasing. LeanSearch returned Algebra.Etale.iff_exists_algEquiv_prod, Scheme.functionField, and fibre definitions; LeanFinder returned the proper-over-field and field-base etale statements, and on the second query Algebra.IsAlgebraic.isBaseChange_of_isFractionRing. I read Mathlib/AlgebraicGeometry/FunctionField.lean:148, RingTheory/Algebraic/Integral.lean:505-533 and RingTheory/Etale/Field.lean:271. These are ingredients, not one-line matches for the full scheme-level statement. No unavailable service was represented as a negative search.

## Review by Q116

I read Morphisms Tag 02GL (lemma-etale-over-field, both clauses and its direct proof), Tag 01RV (lemma-integral-scheme-rational-functions, statement and proof), the generic-point comparison Tag 0CC1 (lemma-dominant-between-integral, proof), and the etale restriction assertion Tag 02GJ. I also read Schemes Tags 01I4 and 01JQ for the affine tensor fibre product, and 01JR for its open restrictions; Algebra Tag 00CP for localization's universal property, the fraction relation preceding 00CO, and Tag 00DK for the tensor/localization formula and its common-denominator proof. Algebra 00U3 and the following etale-at-prime lemma explain the finite separable residue-field input. The assembly is marked agent-written because the sources do not contain this exact combined theorem. There are no new node sources to audit.

For step 1 I opened def-weil-finite-integral-morphism: it expressly gives affine inverse images and a finite module on every affine target open. Surjectivity, from def-weil-surjective-morphism, makes this inverse image nonempty. The statement of lem-sc-integral-function-field-affine-fraction explicitly covers arbitrary integral schemes, not only curves, and supplies both domain rings, generic-point membership, injective germ maps and the complete fraction-field description. Thus all its hypotheses hold for the two nonempty opens.

For step 2 the affine-spectrum definition identifies points with primes and affine morphisms with ring maps. A prime over (0), supplied by surjectivity, proves injectivity directly; no reduced-kernel or dominant-map lemma is silently assumed. The zero prime of B then contracts to zero. The function-field-map definition specifies the actual generic stalk map for a dominant integral-scheme morphism; surjectivity supplies dominance here. Its germ formula is the definition of the induced map on stalks. This removes the possibility of choosing an arbitrary embedding of L over F. All claims in this elementary step are written out as prime contractions or fraction formulas.

For step 3 lem-a1-etale-open-restriction says exactly that compatible source and target opens retain etaleness, without quasi-compactness, separatedness or Noetherian assumptions. Its application is to W and V. I checked that lem-weil-pbc-etale-algebra-residue-field-separable asserts both finite dimensionality and separability for the residue fields of any prime of the source affine ring and its contraction. Taking both primes to be zero is justified by step 2. Identifying these residue fields with Frac(A) and Frac(B) gives exactly the canonical embedding already fixed, not a different extension. This is the only use of etaleness beyond restriction.

For step 4 the localization-universal-property leaf explicitly gives a unique ring map and the fraction formula, so it supplies all required maps to C and L. The denominator images are nonzero, because the ring map is injective and B is a domain. The kernel computation embeds C in L. Finite A-module generators of B span C over F by the displayed b/s expansion. Thus C meets every hypothesis of the cited finite-dimensional-domain-is-field leaf; neither normality nor Noetherianity is needed. Once C is a field, the localization universal property extends B to Frac(B), and the two maps are inverse on every fraction. This proves the localized ring identification in the item rather than moving it into another node.

For step 5 I opened algebra-tensor-pushout-universal-property and checked that it asserts the commutative algebra structure, its product formula, existence of the map to a commutative algebra from two compatible maps, and uniqueness. The maps B to C and F to C agree on A. The inverse from C exists because the images of S are units in the tensor ring. Both composites are explicitly calculated, with the balancing relation and the pure-tensor spanning assertion from def-weil-pbc-module-tensor-product. These calculations prove multiplicativity as well as the requested F-linearity, so an isomorphism of modules has not been mistaken for an algebra isomorphism.

For step 6 def-pc-fibre-product states the universal property and uniqueness with both projections. The open-preimage-fibre-product leaf gives exactly W = Z times_X V, not merely an inclusion of point sets. Pasting that universal property with Spec F to V identifies the desired pullback over X with the affine pullback over V. The affine-spectra fibre-product leaf expressly states the tensor algebra and BOTH projection ring maps. The ring map of h is the already proved j alpha; its values on B and F are the respective generic-point and extension maps. Thus Spec of its inverse proves the scheme isomorphism with the correct variance and both projections.

For step 7 uniqueness in the same fibre-product definition compares maps from Spec L to the fixed global pullback. The two prescribed projections are chart-independent generic stalk maps, so all constructed morphisms are literally this h. I also wrote the restriction-of-fractions equation and used a smaller affine open in an overlap. I did not assume that an intersection of affine opens is affine, or assume separatedness of X or Z.

I tested identity covers, finite separable field spectra over a field, positive-degree integral finite etale covers, and the zero-dimensional base. The statement includes no empty integral scheme: integrality supplies nonemptiness, and surjectivity excludes an empty inverse image of a nonempty chart. Purely inseparable field extensions fail the etale hypothesis as required. Reducible finite etale covers are excluded by integrality of Z and are handled by the parent through its component decomposition; no claim about a product being a field is used. The finite generation proof works for arbitrary non-Noetherian domains. The maps preserve structural scalars throughout.

Against delivery-errors B--E: all objects are introduced, existing definitions are cited, no statement-only child or duplicate is created, every non-elementary input is a node citation, the quoted statements actually give the properties taken from them, proof dependencies are exactly the union of step citations, and compatibility is established by explicit equations and the universal property. No non-elementary proof step exceeds 2000 characters (the longest is about 1131). No SGA source, Lean edit, compiler or local preflight was used. Nothing remains unfinished mathematically; dry run and delivery are the remaining mechanical checks.

## Not duplicates

No new nodes were created.

## Unfinished work

None in the split.
