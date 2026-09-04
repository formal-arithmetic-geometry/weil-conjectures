# Nagata Blueprint: Proof Order and Key Dependencies

This is the recommended order for formalizing the arguments in
nagata_new.tex. Each row names the blueprint label, states the mathematical
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

> **Route revision (formalization, 2026-08-28, superseding the earlier note of
> the same day).** Items 25-29 (the module-flattening chain, Stacks Tags
> 0815/081R/081P/081L) are **not** on the formalized route.  They are the
> Stacks Project's proof of item 30 (Tag 081S), but that chain bottoms out in
> the dévissage sections of Stacks §§38.4-38.10, which exist neither in Mathlib
> nor in this blueprint.
>
> Item 30 (Tag 081S) is formalized instead via **Conrad's Theorem 2.4 and
> Zariski's Main Theorem** — items 61-75 below, the chapter "Elimination of
> indeterminacy after Deligne and Conrad" of `nagata_new.tex`.  Both external
> inputs are available: ZMT is in Mathlib
> (`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`), and Stacks Tag 04II
> is already formalized here as `exists_immersion_affineSpace_of_quasiAffine`
> (`WeilConjectures/Mathlib/AlgebraicGeometry/AffineSpace.lean:291`).  Item 30
> is formalized and `sorry`-free, as
> `AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`
> in `WeilConjectures/Compactification/EliminationOfIndeterminacy.lean`.
> Item 23 is so far formalized only in its affine
> algebraic layer (`Submodule.powTorsion` and `Submodule.torsion'QuotientMap`
> in `WeilConjectures/Mathlib/Algebra/Module/Torsion.lean`).
>
> What is unchanged: the **two-open** theorem (items 43-48) does not go through
> flattening either way.  It uses the boundary-separation route — item 36's Tag
> 0F3V separation blow-up, common modifications, and the dense-source valuative
> criterion (item 42).
>
> **Route revision (formalization, 2026-08-26): Tag 080E.** The identification
> of the strict transform with the blow-up of the pulled-back ideal
> (`thm:nagata-strict-transform-is-blowup`, Stacks Tag 080E — a prerequisite
> for the common-modification construction of item 32/Tag 0F3X, where it
> identifies the strict transforms of the two projections with blow-ups of
> the graph image) is formalized as
> `Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`
> (`Compactification/StrictTransformBlowup.lean`), **not** via the blueprint's
> original chart-cocycle gluing but via a comparison morphism
> `Bl_{I·O_Y}(Y) ⟶ Y ×_X Bl_I(X)` (components: the structure morphism and the
> Tag 0806 lift) which is a closed immersion by a chart-wise surjectivity
> computation (`AffineBlowup.closure_range_awayAlgebraMap_union_range_awayMap`,
> `AffineBlowup.isClosedImmersion_pullbackLift`,
> `Scheme.IdealSheafData.isClosedImmersion_pullbackLift_blowup_comap`) and has
> the kernel of the open `U`-locus because the exceptional complement is
> schematically dense in the `Y`-blow-up
> (`Scheme.IdealSheafData.ker_pullbackLift_blowup_comap`).  No finiteness
> hypotheses are needed.  `nagata_new.tex` was updated in step
> (`def:nagata-strict-transform-blowup-comparison`,
> `thm:nagata-strict-transform-is-blowup`, and the formalization-route remark
> after `def:nagata-strict-transform`).

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

## 10. Elimination of indeterminacy: the Conrad/ZMT route to Tag 081S

The chapter "Elimination of indeterminacy after Deligne and Conrad" of
`nagata_new.tex`, following Conrad, *Deligne's notes on Nagata
compactifications*, §§1-2 (pp. 10-19).  These items are numbered after item 60
so that the numbering above is unchanged, but logically they all precede item
30: they are the formalized route to it, replacing items 25-29.  This section is
formalized: the culminating item 74 is
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` in
`WeilConjectures/Blowup/PartialSectionExtension.lean`, with item 75 the
corollary `AlgebraicGeometry.exists_admissibleBlowup_extend_section` in the
same file.

| Order | Label | Role | Main inputs -> output |
|---:|---|---|---|
| 61 | def:nagata-conrad-quasi-domination | Defines a quasi-domination: a map on a dense open whose graph stays closed in the ambient product (Conrad Def. 2.1). | Dense open + map to a separated target -> closed-graph datum |
| 62 | lemma:nagata-conrad-morphism-is-quasi-domination | Any map on `U` to a separated target is a quasi-domination of `U` (the `U = V` case of Remark 2.5). | Separated target -> quasi-domination |
| 63 | lemma:nagata-conrad-quasi-domination-proper-target | A quasi-domination over a proper target is defined everywhere. | Proper target + closed graph -> domain is all of `X` |
| 64 | lemma:nagata-conrad-dense-in-admissible-blowup | A dense quasi-compact open stays dense in any admissible blow-up, and is schematically dense when the centre is its exact complement. | Invertible exceptional ideal -> density transport |
| 65 | lemma:nagata-conrad-schematically-dense-blowup | One admissible blow-up makes the preserved open schematically dense (Stacks Tag 01PH + Tag 080L). | qc open -> blow-up with schematically dense `U` |
| 66 | lemma:nagata-conrad-strict-transform-in-charts | Deligne's Lemme 0.2 / Conrad Lem. 1.4: the strict transform of one centre lives in the charts of the other; strict transforms of `n` centres are mutually disjoint. | Blow-up chart algebras -> chart-wise disjointness |
| 67 | def:nagata-conrad-disjointness-setup | Records the hypotheses of Conrad Lem. 1.5: the square, the thickening `T₁ = V(I₁²)`, the auxiliary `T₂`, and the scheme-theoretic factorization hypothesis. | Diagram + two centres -> disjointness situation |
| 68 | lemma:nagata-conrad-disjointness-blowup | Deligne's Lemme 0.3 / Conrad Lem. 1.5: after blowing up `I₁ + I₂`, the closure of the image of `Y` no longer meets the part over the closure of `V ∖ U`. | Disjointness situation -> separating function `h` on each chart |
| 69 | lemma:nagata-conrad-affine-space-extension | Case 1 with `Y = 𝔸ⁿ_X` (pp. 14-15): a map `U -> 𝔸ⁿ_X` over an affine base extends to `Bl_I(X) -> ℙⁿ_X` for an explicit centre built from the transition data. | Affine cover of `U` + homogeneous coordinate formulas -> extension |
| 70 | lemma:nagata-conrad-quasi-affine-affine-base | Case 1 in full: quasi-affine finite-type target over an affine base, `U = V`. | Tag 04II immersion + item 69 + schematic density -> quasi-domination |
| 71 | lemma:nagata-conrad-quasi-affine-equal-opens | Case 2 (pp. 15-16): quasi-affine target over a qcqs base with `U = V`, by gluing the affine-base solutions along a product centre. | Item 70 on an affine cover + finite-type ideal extension + product blow-up -> glued quasi-domination |
| 72 | lemma:nagata-conrad-quasi-affine-general | Case 3 (pp. 16-17): quasi-affine target with `U ⊆ V`, by first separating `p(im f)` from the closure of `V ∖ U`. | Item 68 + item 71 on the shrunken base `X ∖ closure(V ∖ U)` -> quasi-domination |
| 73 | lemma:nagata-conrad-graph-closure-quasi-finite | The general case, first half (pp. 17-19): after one `V`-admissible blow-up the scheme-theoretic image of the graph is quasi-finite and separated over the blow-up. | Affine cover of `Y` + item 72 on each `closure(U_i)` -> finite fibres |
| 74 | thm:nagata-conrad-elimination | **Conrad Thm. 2.4** (Deligne Thm. 1.2, Nagata Thm. 3.2): a quasi-domination of `V` over a separated finite-type `Y` extends to a quasi-domination of a `V`-admissible blow-up of `X`. | Item 73 + Zariski's Main Theorem (quasi-finite separated => quasi-affine) + item 72 -> the theorem |
| 75 | cor:nagata-conrad-proper-target-extension | **Conrad Rem. 2.5**: for `U = V` and `Y` proper, a map `U -> Y` extends to a morphism on a `U`-admissible blow-up. | Items 62, 63, 74 -> everywhere-defined extension |

> **Route to item 30.** The remark closing the chapter records the derivation of
> item 30 (Tag 081S) from item 74: make `U` schematically dense (item 65), apply
> item 74 with `V = U` to the section `U ≅ q⁻¹(U) ↪ Z`, enlarge the centre so
> that its complement is exactly `U`, and observe that the strict transform of
> `Z` — the scheme-theoretic closure of the graph — is a closed subscheme of the
> closed graph `Γ` containing `U` as a schematically dense open, hence equals
> it.  That derivation is carried out in Lean in
> `WeilConjectures/Compactification/EliminationOfIndeterminacy.lean`.

## Formalization status by PR (stack nagata-01 … nagata-09, 2026-08)

**Current status (2026-09).** The whole chain is formalized and `sorry`-free on
`slopmaster`, up to and including item 60 (`thm:nagata-compactification`):
`AlgebraicGeometry.NagataCompactification` in
`WeilConjectures/Compactification/NagataCompactification.lean`, which — together
with `AlgebraicGeometry.nagataCompactification_of_locallyOfFinitePresentation`
and `AlgebraicGeometry.nagataCompactification_of_isNoetherian` — carries a
`#print axioms` census in the build checking that it depends on
`[propext, Classical.choice, Quot.sound]` only.  In particular item 30
(Tag 081S) is unconditional, and the "depends on `sorryAx` through Tag 081S"
qualifications in the dated rows below are superseded.

The table is a historical log: it records where each core node (and its Stacks
tag) was first realized in the Lean development, and the state of the work at
that date.  Labels not listed are upstream (items 1-2, PR #18).
"Formalization route" remarks in `nagata_new.tex` record where the Lean proof
deviates from the written route.

| PR | Items / results | Status |
|---|---|---|
| #19 | 3-8 (scheme-theoretic image; Stacks 081I) | proved |
| #20 | 14 (`isProper_blowupMap`) + principalization `extendedToBlowup_isEffectiveCartier` (now `Scheme.IdealSheafData.isEffectiveCartierCenter_subschemeι_comap_blowupMap`) | proved; projective-embedding chain bypassed via Mathlib Proj properness |
| #21 | 21, 22 (`StrictTransform`, now `AlgebraicGeometry.strictTransform`; over-complement), 23 affine layer, Tags 01PE/01PF | proved; chart model of the strict transform bypassed |
| #22 | Tag 0803 (`exists_finiteDegree_center_le_blowup`) | proved, ideal-sheaf form |
| #23 | 16 (Stacks 0806, `exists_lift_blowup` + `hom_ext_of_isInvertible_comap`) + effective-Cartier kit (07ZV) | proved, chart-local route |
| #24 | 18 (080A), 19 (080K), 24 (080Y), Tags 080B/080L/01PH/01PF, 0F3V (`disjoint_range_strictTransformMap_separationBlowup`, now `disjoint_range_strictTransformMap_sup`) | proved; the one remaining `sorry`, Tag 0807 (`exists_blowup_mul_isEffectiveCartier_iso`, now `Scheme.IdealSheafData.exists_blowup_mul_isInvertible_iso`), is closed in PR #26 via the Tag 0806 universal-property kit; 0F3V by direct sum-ideal chart argument, 080P bypassed |
| #25 | 34, 36, 37 + partial-section lemma, dense refinement | proved; items 30-33 (Tags 081S/0F3Y/0F3X/0F3Z) stated with `sorry`; 0F3W not yet stated |
| #26 | 38-41 (Tags 02JQ/052K/00IA) + Tag 0807 | proved; item 42 (Tag 0894) stated with `sorry`, split into `universallyClosed_of_isDominant` (now `UniversallyClosed.of_valuativeCriterion_of_isDominant`) and `isSeparated_of_isDominant` (now `IsSeparated.of_valuativeCriterion_of_isDominant`); the valuation-theoretic items 39-41 (`comapResidue`; `comap_eq_of_le_comap`, now `ValuationSubring.comap_eq_of_toLocalSubring_le`; `exists_comap_eq`) and the topological core of 02JQ (`exists_specializes_of_mem_closure_range`) live in `WeilConjectures/Mathlib/` helper files |
| (2026-08-26, integration branch) | Tag 080E (`thm:nagata-strict-transform-is-blowup`): strict transform = blow-up of the pulled-back ideal | `exists_blowup_comap_iso_strictTransform` proved from four obligations (affine chart generation, affine + global closed immersion, kernel identity via schematic density of the exceptional complement); universal-property route, chart-cocycle gluing of the blueprint bypassed |
| (2026-08-27, integration branch) | 32, Tag 0F3X (`lemma:nagata-common-modification`): existence of a common modification | `nonempty_commonModification` proved along the blueprint route (scheme-theoretic image of the graph; Tag 081S on both projections; Tag 080E to identify the two strict transforms with blow-ups of the pulled-back centres; the product centre `K₁ * K₂` to dominate both; `IsAdmissible.exists_extend`/`exists_comp` to extend it, packaged as `IsAdmissible.exists_isOpenImmersion_blowup`; gluing along the common open). Depends on `sorryAx` only through the still-open Tag 081S (item 30) |
| (2026-08-27, integration branch) | 43-48, Tag 0F40 (`thm:nagata-two-open`): the two-open compactification theorem | `HasCompactification.of_two_open_cover` (`Compactification/TwoOpen.lean`) proved on top of the comparison layer (`Compactification/TwoOpenComparison.lean`, support for items 43-46). The intermediate schemes `Wᵢ = U ⊔_{Oᵢ} Xᵢ°` (item 43) are pushouts of open immersions (`TwoOpenSide.intermediate`); their overlap is a closed immersion by the exact range description `range υ = ψ⁻¹(O)` (`isClosedImmersion_intermediateGraph`, the constructibility detour of the blueprint bypassed), whence separatedness by Tag 0F3U (`IsSeparated.pushout_desc`); density of the copy of `U` is `dense_range_intermediateU`. The final model is the common modification of the two intermediate schemes (Tag 0F3X, `nonempty_commonModification`; item 45), density transports through it by `IsAdmissible.dense_preimage_blowupMap` (items 46-47), and properness is the dense-source valuative criterion Tag 0894 (`UniversallyClosed.of_valuativeCriterion_of_isDominant`; item 48). Depends on `sorryAx` only through Tag 081S (item 30); the improved-comparison obligation `exists_admissibleBlowup_comparisonBoundary_subset_selfBoundary` is now proved, from Tag 0F3W alone (Tag 0F3Y is not needed: the improved comparison space is a closed subscheme of the strict transform, which is all the argument uses), and the intermediate-scheme layer itself is sorry-free |
| (2026-08-16) | 34-48 (two-open theorem; Stacks 0F3U/0F40) | **items 43-48 proved**: `HasCompactification.of_two_open_cover` (`Compactification/TwoOpen.lean`) assembles the two-open theorem from `TwoOpenSide`/`TwoOpenPreparation` (`TwoOpenSetup.lean`, `TwoOpenComparison.lean`); the intermediate schemes are pushouts of open immersions (`Mathlib/AlgebraicGeometry/Gluing.lean`), separatedness via Tag 0F3U (`IsSeparated.pushoutDesc`, now `IsSeparated.pushout_desc`), overlap-closedness without the constructibility detour (`isClosedImmersion_intermediateGraph`), density via `AdmissibleBlowup.dense_preimage` (now `IsAdmissible.dense_preimage_blowupMap`), properness via Tag 0894. Item 35-37 packaging `exists_prepared_twoOpenSide` proved from the (sorried) Tag 0F3Z. Tag 0F3W newly stated (`exists_admissibleBlowup_strictTransform_isIso_near_closure`, now `exists_admissibleBlowup_isIso_strictTransformMap_near_closure`; `sorry`). One new `sorry`: `exists_prepared_keyDisjoint_twoOpenSide` (the improved-comparison chain, items comparison-restriction/0F3W/0F3Y/boundary-density/key-disjointness), blocked on Tags 0F3W/0F3Y |

## Remaining implementation notes

The mathematical chain above is complete at the blueprint level, and the two
former API markers are now discharged at the interface level in
`nagata_new.tex`.  `lemma:nagata-relative-proj-current-api` maps the relative
Proj construction to Mathlib's affine Proj charts and
`Scheme.Cover.RelativeGluingData`; `lemma:nagata-noetherian-current-api` maps
the Noetherian approximation argument to the affine-transition-limit and
relative-gluing APIs.  The Lean packaging of the finite coefficient, generator,
and relation lists in those named wrappers has since been carried out, so
nothing in the chain is outstanding.
