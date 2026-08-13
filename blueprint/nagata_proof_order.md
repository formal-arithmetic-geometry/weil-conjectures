# Nagata Blueprint: Proof Order and Key Dependencies

This is the recommended order for formalizing the arguments in
nagata_new-3.tex. Each row names the blueprint label, states the mathematical
role, and records the main input/output relation. The order is by proving idea,
not by the shortest source-file path.

## 1. Compactification and scheme-theoretic images

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 1 | def:nagata-compactification | Bundles an open immersion, a proper map, and the factorization over the base. | Data -> compactification structure |
| 2 | def:nagata-compactifiable | Defines existence of the bundled structure. | compactification structure -> predicate |
| 3 | lemma:nagata-scheme-image-ideal-qc | Gives the affine kernel description of the scheme-theoretic image for qc maps. | qc/qcqs map -> quasi-coherent image ideal |
| 4 | def:nagata-scheme-theoretic-image | Defines the closed subscheme cut out by that ideal. | Image ideal -> closed subscheme |
| 5 | lemma:nagata-scheme-image-universal | Characterizes the image by its factorization universal property. | Image definition -> unique factorization |
| 6 | lemma:nagata-scheme-image-restrict-open | Identifies image formation after restriction to an open target. | Affine localization -> open restriction isomorphism |
| 7 | lemma:nagata-scheme-image-flat-base-change | Identifies image formation after flat base change. | Flat kernel calculation -> base-change isomorphism (Stacks Tag 081I) |
| 8 | lemma:nagata-dense-compactification-characterization | Converts scheme-theoretic density into the image-isomorphism formulation used later. | Image universal property -> dense compactification criterion |

## 2. Relative Proj, Rees algebras, and blow-ups

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 9 | def:nagata-relative-proj | Specifies the relative Proj construction and its chart data. | Graded algebra -> relative Proj interface |
| 10 | lemma:nagata-relative-proj-exists | Separates existence and chart properties from the definition. | Relative Proj interface -> scheme and standard opens |
| 11 | prop:nagata-relative-proj-functoriality | Supplies maps induced by graded algebra morphisms. | Graded map -> Proj morphism |
| 12 | def:nagata-sheaf-rees-algebra | Forms the sheaf Rees algebra of a finite-type ideal. | Ideal sheaf -> graded algebra |
| 13 | def:nagata-global-blowup | Defines the global blow-up by relative Proj of the Rees algebra. | Rees algebra + relative Proj -> blow-up |
| 14 | thm:nagata-global-blowup-proper | Establishes properness of the global blow-up. | Projective/finite-cover charts -> proper morphism |
| 15 | thm:nagata-global-blowup-complement | Identifies the blow-up with the original scheme where the ideal is the unit ideal. | Unit ideal on an open -> canonical complement isomorphism |
| 16 | thm:nagata-blowup-universal-property | Provides the lift when the pulled-back center becomes invertible. | Invertible pullback ideal -> unique blow-up lift |
| 17 | thm:nagata-blowup-flat-base-change | Makes blow-up formation compatible with flat base change. | Flat map + Rees localization -> pullback blow-up |
| 18 | thm:nagata-blowup-product-ideal | Replaces a finite composite by one blow-up of a product/dominated ideal. | Two blow-ups -> common dominating blow-up |
| 19 | def:nagata-admissible-blowup | Records the preserved open and its chosen blow-up datum. | Unit ideal on U -> U-admissible blow-up |
| 20 | lemma:nagata-admissible-blowup-preserves-density | Proves scheme-theoretic density survives admissible blow-up. | Dense U + unit ideal on U -> dense inverse image |

## 3. Strict transforms and flattening

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 21 | def:nagata-strict-transform | Defines the scheme/module strict transform by removing center-power torsion. | Blow-up pullback -> strict transform |
| 22 | lemma:nagata-strict-transform-over-complement | Identifies the strict transform with the original object over the preserved open. | Admissible blow-up -> complement comparison |
| 23 | lemma:nagata-module-strict-transform-exact | Shows strict transform preserves the required exact finite-data sequences. | Universal exact sequence -> transformed exact sequence |
| 24 | lemma:nagata-cartier-boundary-preparation | Produces an admissible blow-up whose boundary supports an effective Cartier ideal. | Quasi-compact open complement -> Cartier boundary |
| 25 | lemma:nagata-finite-data-flattening-package | Supplies the finite-data flattening step (Stacks Tag 0815). | Finite type module, fp/flat over U -> finite admissible flattening sequence |
| 26 | thm:nagata-module-flattening-by-blowup | Packages flattening as one admissible blow-up. | Finite-data package -> fp and flat strict transform |
| 27 | lemma:nagata-flattening-after-cartier-boundary | Applies module flattening to closed pieces of a separated finite-type morphism. | Cartier boundary + module flattening -> flat fp strict transform |
| 28 | lemma:nagata-flattening-ideal-exists | Selects the flattening ideal and records its universal specification. | Previous flattening lemmas -> chosen ideal |
| 29 | lemma:nagata-dense-open-dimension-package | Extends finite presentation and fibre-dimension bounds from a retrocompact dense open (Stacks Tags 081P and 081L). | Flat lft map + dense open -> lfp and dimension bound |

## 4. Boundary preparation, common modifications, and graphs

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 30 | lemma:nagata-elimination-indeterminacy | Makes a partial section extend across an admissible blow-up. | Scheme image + blow-up -> open strict-transform section |
| 31 | lemma:nagata-scheme-image-strict-transform | Transports scheme-theoretic images through an admissible blow-up. | Image + lifted map -> strict-transform image |
| 32 | lemma:nagata-common-modification | Constructs a common modification of two compactifications (Stacks Tag 0F3X). | Two separated finite-type models agreeing on U -> glued separated model |
| 33 | lemma:nagata-graph-extension | Extends a compactification of V to a proper map over U (Stacks Tag 0F3Z). | Graph image + elimination -> proper V-gr -> U |
| 34 | def:nagata-two-open-dense-compactifications | Chooses dense compactifications of the two opens. | Compactifiability of U_i -> dense C_i |
| 35 | lemma:nagata-two-open-graph-extensions | Records the proper graph-extension data for both pieces. | C_i + graph lemma -> V_i -> U |
| 36 | def:nagata-two-open-prepared-boundaries | Applies the boundary-separation blow-ups. | Four boundary loci -> prepared ambient schemes |
| 37 | lemma:nagata-boundary-disjoint-persists | Preserves the required disjointness and density after the preparations. | Admissible transforms -> disjoint prepared boundaries |

## 5. Valuative criterion

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 38 | lemma:nagata-dense-valuation-probe-exists | Produces a valuation probe centered at any point of a scheme-theoretic image (Stacks Tag 02JQ). | qcqs schematically dominant map + point -> valuation diagram |
| 39 | lemma:nagata-composite-valuation-ring | Composes a valuation ring with a residue-field valuation ring. | Two valuation rings -> composite valuation ring |
| 40 | lemma:nagata-valuation-intersection | Computes the intersection with a dominating extension valuation ring. | A subset K subset L, domination -> K cap B = A |
| 41 | lemma:nagata-valuation-ring-extension | Extends a valuation ring to a field extension (Stacks Tag 00IA). | A subset K subset L -> valuation ring in L dominating A |
| 42 | lemma:nagata-dense-source-valuative | Turns unique valuation lifting from a dense source into universal closedness and separatedness. | Dense source + valuative uniqueness -> universally closed/separated |

## 6. The two-open compactification theorem

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 43 | def:nagata-two-open-intermediate-schemes | Forms the separated intermediate models after boundary preparation. | Prepared pieces -> W_1, W_2 |
| 44 | lemma:nagata-proper-separated-valuation-extension | Produces a lift to a proper separated intermediate model. | Properness + valuation criterion -> extension |
| 45 | def:nagata-two-open-final-modification | Applies common modification to W_1 and W_2. | Two intermediate models -> W'_1, W'_2, glued W |
| 46 | lemma:nagata-two-open-density-transport | Propagates density and quasi-compactness through the finite diagram. | Admissible-density lemma + finite gluing -> dense qc U_1 cap U_2 -> W |
| 47 | lemma:nagata-final-density | Records density for the final candidate. | Density transport -> final dense open |
| 48 | thm:nagata-two-open | Assembles the proper separated compactification from two compactifiable opens. | Final density + valuative lifting -> compactification of U |

## 7. Affine compactification and finite-coordinate reduction

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 49 | prop:nagata-affine-compactification | Compactifies an affine finite-type scheme by a finite projective target. | Relative affine charts + projective target -> compactification |
| 50 | lemma:nagata-dense-affine-cover-exists | Chooses a finite affine cover with dense total intersection. | Finite-type scheme -> finite dense affine cover |
| 51 | lemma:nagata-partial-union-overlap-dense | Supplies the induction invariant for partial unions. | Dense total intersection -> dense partial overlap |
| 52 | thm:nagata-noetherian | Inducts over the finite affine cover using the two-open theorem. | Affine compactifications + dense overlaps -> Noetherian compactification |

## 8. Noetherian approximation and separated descent

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 53 | prop:nagata-noetherian-inverse-system | Constructs the filtered affine Noetherian base system and its limit comparison. | qcqs base -> inverse system |
| 54 | lemma:nagata-diagonal-finite-presentation | Establishes finite presentation of the separated diagonal from affine ring data. | Separated finite-presentation stage -> fp diagonal |
| 55 | lemma:nagata-finite-presentation-descends | Descends finite presentation to a sufficiently large stage. | Finite affine presentations -> descended fp model |
| 56 | lemma:nagata-closed-immersion-stage-exists | Descends the diagonal/closed immersion to a common stage. | fp diagonal + limit comparison -> closed stage |
| 57 | lemma:nagata-separated-descent-stage-exists | Chooses a stage where the descended model is separated. | Closed diagonal stage -> separated model |
| 58 | lemma:nagata-separated-eventually | Records separatedness, finite presentation, and base-change comparison. | Selected stage -> separated fp model over the limit |

## 9. Final assembly

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 59 | def:nagata-final-compactification | Packages the selected descended Noetherian compactification. | Descended model + Noetherian compactification -> final candidate |
| 60 | thm:nagata-compactification | Main theorem: every separated finite-type morphism in scope is compactifiable. | Final candidate data -> Compactification f |

## Remaining implementation notes

The mathematical chain above is complete at the blueprint level, and the two
former API markers are now discharged at the interface level in
`nagata_new-3.tex`.  `lemma:nagata-relative-proj-current-api` maps the relative
Proj construction to Mathlib's affine Proj charts and
`Scheme.Cover.RelativeGluingData`; `lemma:nagata-noetherian-current-api` maps
the Noetherian approximation argument to the affine-transition-limit and
relative-gluing APIs.  What remains is ordinary Lean packaging of the finite
coefficient, generator, and relation lists in those named wrappers, rather
than an unproved mathematical dependency.
