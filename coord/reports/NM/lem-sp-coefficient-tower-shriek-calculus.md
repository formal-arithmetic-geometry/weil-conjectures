## Worker report

Item: `lem-sp-coefficient-tower-shriek-calculus` (NM, stage 2).
Module: `Sheaf.Paper.CoefficientTowerShriekCalculus`.
Namespace: `AlgebraicGeometry.ProEtale.SpTowerCalculus`.
Main declaration: `coefficient_tower_shriek_calculus`.

The module states all three clauses on the recorded **ordinary** derived category of
strict varying-coefficient towers. Its sole theorem has proof `sorry`; all definitions
have real data. The supporting structures are the data and equations of this same
calculus, not alternative definitions of towers, constructibility, Tor amplitude,
scalar extension, or compact support. No node statement or dependency record changes.
No new independent notion or dependency module is needed.

### Hypotheses and category

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is
  `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`, as in the coefficient-extension dependency.
- The theorem binds `(pchar : ℕ) (hp : 0 < pchar) (hne : pchar ≠ l)` and
  `(k : Type u) [Field k] [CharP k pchar]`. There is no finite-field or
  algebraically closed base-field hypothesis.
- Every scheme in the geometric clauses carries `Over (Spec (.of k))`,
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` on its structural map.
  Each map carries `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact`, with `Etale` or `IsOpenImmersion` in the respective clauses.
  The last two finiteness conditions together mean finite type.
- `SpTowerShriek.R l E n` is the dependency's actual quotient
  `O_E/(ell)^(n+1)`. The inherited indexing convention represents all positive
  exponents by `n : ℕ`; level zero means exponent one, never the zero quotient.
  `quotient` is the actual `Ideal.Quotient.factor` for every `m ≤ n`.
- `C` is exactly `spConstructibleTorTowerCategory`; `inclusion` is its full
  inclusion into `spDerivedCoefficientTowers`. In particular it is not
  `spNormalizedConstructibleTorTowerCategory`. The recorded property includes
  intrinsic constructible cohomology at every level and common, level-independent
  cohomological and Tor bounds. No normalized reduction-isomorphism assumption occurs.
- `compactSupport`/`F` is the recorded `SpTowerShriek.F`, namely derived proper
  pushforward after open extension, transported through `realization` to the original
  strict tower category. The latter is the exact derived equivalence of the recorded
  section-preserving ordinary equivalence. No family of finite derived morphisms is
  substituted for a derived tower morphism.
- `Preservation` states exactly the assumption that these functors take the full
  constructible finite-Tor tower categories into one another. `restrictedSupport`
  is the actual `ObjectProperty.lift`, with this proof. The theorem concludes
  `Nonempty (Calculus ... h)` for every such preservation proof `h`.

### Clause (1)

- `CompositionOperations.composition` is a natural isomorphism
  `inclusion ⋙ F c ⋙ F d ≅ inclusion ⋙ F e` for every pair of composable
  morphisms and every compactification of each map and its composite. The auxiliary
  `fg` and equality binder allow the identity and associativity cases to have the
  literal desired composite without an opaque transport of compactifications.
- `CompositionOperations.identity` and `.refinement` supply the identity and
  compactification comparisons on the same full categories.
- `CompositionCoherence.refinement_identity`, `.refinement_transitive`,
  `.identity_left`, `.identity_right`, `.associativity`, and
  `.refinement_composition` give the corresponding equations, including the complete
  four-scheme associativity diagram. The equations are equations of actual derived
  tower morphisms, not just of their evaluations.
- `.triangulated` gives the commutation with shift and triangulated exactness of
  the ambient compact-support functor. Together with its genuine full-subcategory
  restriction, this says the restricted functor preserves the induced distinguished
  triangles of the full ordinary derived subcategory.
- `Evaluation.normalization` fixes the evaluation isomorphism to the explicit word
  in `SpTowerShriek.Fcomparison`, `levelComparison`, and realization counits.
  The ordinary coordinate changes fix every section.
- `CompositionCoherence.composition_finite` equates the evaluated compositor with
  `finiteCanonicalComposition`, with all evaluation-coordinate maps written out.
  `fixedComposition` conjugates the published `originCompositionAmbient` by the
  published normalized compactification comparisons. `fixedRefinement` is their
  unique preimage through the etale-origin equivalence, and `.refinement_finite`
  identifies the evaluated refinement with this exact comparison.
  `FiniteNormalization.finite_origin` gives the bounded etale-origin witnesses for
  these finite evaluations; this is a conclusion, not an extra hypothesis on a tower.
- `Calculus.open_normalization` identifies the compositor, for `c.precomp j`,
  with the explicit `openComposition` after the etale-to-open comparison.
  `sequenceOpenComposition` is the left-adjoint uniqueness comparison for the
  ordinary composite open extensions against `o.ordinaryComp`. Its exact derived
  image and the realization counits define `openComposition`. Thus the normalization
  uses canonical open adjunction counits rather than an arbitrary open isomorphism.

### Clause (2)

- `finiteEtaleExtension` is the actual left Kan extension followed by sheafification
  along the functor between the small pro-etale sites, in fixed `ModuleCat` coordinates,
  transported by the existing intrinsic module equivalences. This is the localized
  sheaf extension, not an arbitrary adjoint or a property assumed of an unspecified map.
- `finiteEtaleAdjunction` uses Mathlib's sheafification/Kan-extension adjunction.
  Its right-coordinate change is the published inverse-image/localization comparison
  followed by the left-adjoint uniqueness comparison against the section-normalized
  direct image. This pins the finite counit to the sum counit: a section in a summand
  indexed by a lift goes to its image in the target section module. On geometric
  fibres this is precisely the sum over lifts, including an empty sum. The construction
  is the one used by Stacks 03S5; `EtaleSumStalks` is imported for its geometric-stalk
  description in the proof.
- `EtaleOperation` is ordinary exact extension on the actual strict semilinear system
  category: its `additive`, `limits`, and `colimits` fields say it is exact, and
  `ordinaryAdjunction` makes it left adjoint to the recorded exact inverse image.
  `evaluation`, `unit_evaluation`, and `counit_evaluation` identify its ordinary
  finite evaluations and adjunction maps with the specified finite sheaf constructions.
- `derivedAdjunction`, `unit_termwise`, and `counit_termwise` give the adjunction
  on the unbounded ordinary derived category, and fix its maps as the localization
  of the ordinary tower maps. `etaleExtension`, `etalePullback`, and
  `etaleAdjunction` transport this actual adjunction to the original tower category.
  Coefficient-quotient compatibility is retained because the ordinary unit/counit
  are morphisms of strict semilinear systems and the derived maps are their termwise
  localizations. They are not assembled from independent finite adjunctions.
- `EtaleCalculus.etale_shriek` identifies `F_e` on `C_U` with this exact extension.
  `.etale_preserves` gives preservation of the recorded full tower properties for
  both functors. `restrictedEtaleAdjunction` explicitly restricts the ambient
  adjunction by the fully faithful inclusions, using precisely these preservation
  proofs. Its units and counits are the restrictions of the ambient ones.
- `.finite_etale_constructible` preserves the intrinsic bounded constructible,
  finite-Tor property. `.finite_etale_intervals` preserves each specified pair of
  integer endpoints, separately for cohomology and Tor and for both functors, at
  every finite level. Thus a single uniform interval remains the same uniform
  interval; the conclusion does not merely assert the existence of new bounds.
- `openEtaleCoordinates` is the exact derived image of the unique ordinary
  left-adjoint comparison with `o.openOp j`. It identifies the open case with the
  recorded extension by zero and preserves its normalized open counit.

### Clause (3)

- `ScalarCoordinates.restriction` identifies the recorded strict-system coefficient
  restriction with restriction along the actual quotient-ring sheaf map. Its
  `restriction_sections` fixes the identity on all sections. `scalar` compares
  the two existing derived scalar functors, and `unit` fixes the comparison by
  the normalized scalar adjunction. This prevents a scalar automorphism or
  arbitrary comparison from changing the reduction formula.
- `reduction` is exactly the recorded `a.reduction`, with this scalar-coordinate
  isomorphism applied inversely to its source. It therefore uses the actual
  strict semilinear transition of the tower, including non-normalized towers.
- `ReductionCalculus.reduction_formula` writes the displayed identity as an
  explicit commuting square under `Evaluation.comparison`. The middle arrow
  is literally `reductionDirectImageComparison (quotient ...) c.i c.g`.
  `.reduction_comparison_isIso` gives the isomorphism assertion on each finite
  evaluation of a constructible finite-Tor tower.
- That imported comparison is, by definition, the proper scalar-counit adjoint
  transpose followed by the canonical extension-by-zero tensor comparison.
  This delivery does not replace it by a merely isomorphic unspecified map.
- `.reduction_naturality`, `.reduction_identity`, and `.reduction_composition`
  specify naturality and compatibility for all iterated quotient maps.
  `scalarUnit` and `scalarAssoc` are explicit words in the dependency's normalized
  tensor unitor/associator and the adjunction-normalized scalar coordinate changes.
  No flatness of the quotient is assumed.

### Dependencies and sources read

All recorded statement-dependency signatures and docstrings were read, including:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `ProEtale.CondensedRing.compactificationOverField` and bounded constructible setting.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the actual quotient coefficient types.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers`, `spEllIdeal`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spDerivedCoefficientTowers`,
  `spDerivedCoefficientEvaluation`, `spFiniteConstructibleTor`,
  `spConstructibleTorTowers`, and `spConstructibleTorTowerCategory`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, `spCoefficientCommRings`,
  `spCoefficientEvaluation`, ordinary/derived reduction and their unit/associator laws.
- `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`,
  `Geometry`, `Open`, `Operations`, `F`, `Ev`, `Fcomparison`, and `tower_shriek_levels`.
- `Sheaf.SecSmoothPurity.ReductionDirectImage` and its comparison module:
  `reductionCompactSupport`, `reductionDirectImageComparison`,
  `reductionDirectImage_isIso`, and `reductionDirectImage_cocycle`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `Scheme.IsConstructibleProEtaleModuleSheaf`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`:
  `Scheme.HasProEtaleTorAmplitude`, `Scheme.HasFiniteProEtaleTorAmplitude`.

The finite-coordinate words additionally use `sfIntrinsicDerivedEquivalence`,
`sfIntrinsicCompactSupportComparison`, `fixedCompactSupportOriginIso`,
`originCompositionAmbient`, and the actual scalar-extension and intrinsic
restriction-of-scalars adjunctions. The canonical composition modules and their
signatures were read. All already-recorded proof-dependency modules are imported;
proof dependencies without a Lean declaration remain references in the full seven-step
proof docstring (`det-pe-finite-tor-comparison-noetherian`,
`lem-sp-compactification-refinement-coherence`,
`lem-sp-et-proet-coefficient-compatibility`, `lem-sp-varying-ring-graph-summand`,
`lem-sp-varying-ring-proper-open-pasting`, `lem-weil-pbc-mate-pasting`). They are
not assumptions in the statement and are not needed to elaborate it.

Source places opened: the current `main-20261015` smooth-purity tower geometric
blueprint proof (Local pairs and Levels); the local Stacks `more-etale.tex`
`lemma-shriek-composition` (0F7J), and `etale-cohomology.tex`
`proposition-describe-jshriek` (03S5). The existing compactification-comparison
interfaces supply the finite normalization without imposing an extra origin
hypothesis on the input towers.

### Searches

- `msearch.py ... leanfinder` with query
  `Composition and etale adjunction and coefficient reduction for compact support on varying coefficient towers`:
  returned unrelated ring-etale composition lemmas, no matching calculus.
- `msearch.py ... loogle` with query
  `Functor.mapDerivedCategory, Adjunction, IsTriangulated`:
  no match; the remote Mathlib index does not contain the project-derived-functor name.
- `msearch.py ... grep` with regex
  `coefficient.*tower.*shriek|tower.*shriek.*calculus`: zero hits.
- `grep -rn` of the exact item id in upstream `WeilConjectures`: zero hits.
  `rg` of the id and tower-calculus terms in upstream and shared `lean/Sheaf`:
  no statement of the combined calculus. Searches for scalar, compact-support,
  localized-extension, and finite-origin names found the reused declarations above.
- Mathlib source searches for derived functor comparisons, adjunction restriction,
  natural-isomorphism transport, and localized sheaf pullback found the existing
  constructions used in the helper definitions; no duplicate construction was made.

### Edge cases and verification

Checked: level `0` means the first positive quotient; `m = n` gives the canonical
unitor; three arbitrary ordered indices give the balanced associator; no derived
reduction is assumed invertible for an input tower. Zero towers, empty schemes,
empty geometric fibres, identity maps, arbitrary compactifications of identities,
open immersions, and a ramified finite coefficient extension are included. The
interval clauses allow any integer endpoints, including the vacuous interval of
a zero object. No quotient flatness, field finiteness, or perfectness was added.
All variables and universes are explicit (`autoImplicit false`).

The returned delivery had an immutable-head sandbox timeout. I repaired the elaboration cost by lowering the file-local `synthInstance.maxSize` from 4096 to 2048; this leaves all declarations and statement fields unchanged. The repaired file compiled with the prescribed `scompile.py` wrapper, with no errors or warnings (sandbox 42.4 s; library 63.8 s in the validation run).
The interface structures are separated by their mathematical role, with unused
constructor-injectivity and SizeOf equations disabled locally to keep elaboration
and serialization within the standard per-file limit. Every map definition is
an explicit functorial construction; the only postponed proof is the named main
DAG theorem, whose docstring includes the complete seven-step DAG proof.

No `STATEMENT-DISPUTED` finding and no statement correction.

## Second reading by NM

The dispatcher requests a single worker delivery, prohibits additional agents,
and assigns independent review to the maintainer. This section records my own
second pass, not an independent worker review.

I reopened the node and checked its three clauses against the final structures.
The check caught missing explicit open normalization and a missing explicit
restricted adjunction in the earlier draft; both were supplied by canonical real
constructions and the `Calculus.open_normalization` equation. It also led to the
explicit same-endpoint finite cohomological/Tor interval fields and the quotient
identity, composition, and naturality equations. The source hypotheses occur in
every geometric clause; there is no normalization assumption, no etale-origin
input hypothesis, and no finite-field assumption. The coefficient comparison is
the recorded proper-counit mate, and the finite compositor is the canonical
published compositor conjugated by its published compactification comparisons.
All supporting declarations belong to this calculus and reuse the existing
category and scalar-extension notions. Independent acceptance remains the
maintainer's review of this delivery.

Delivery validation after the timeout repair: `deliver2.py NM lem-sp-coefficient-tower-shriek-calculus --no-push`
printed `OK (dry run): commit 024f73ae70 passes the preflight and compiles; nothing pushed`.
