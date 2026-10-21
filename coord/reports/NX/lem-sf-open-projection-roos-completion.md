## Worker report

The module `Sheaf.SixFunctors.OpenProjectionRoosCompletion` states
`WeilConjectures.OpenProjectionRoos.openProjectionRoosCompletion`. Its only
postponed proof is this theorem, whose docstring gives the complete nine-step
argument in the node. The node statement, dependencies and proof are unchanged.
All helper definitions have real data; `CompletionData` is an explicit proposition
asserting simultaneously normalized comparison data, not a chosen tensor or map.
`Completion` existentially supplies the exactness witnesses used by that predicate.

### Hypotheses and coefficient conventions

- `D : FiniteFieldDatum.{u}` is exactly the recorded algebraic closure of the
  finite field, and `hl : l ≠ D.p` is the required characteristic exclusion.
- `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` give the coefficient datum.
  The valuation ring, its fixed uniformizer and its positive quotients are the
  existing `Padic` coefficient constructions, not extra parameters.
- `U X : Scheme.{u}`, their `Over (Spec (.of D.k))` instances, the two
  `LocallyOfFiniteType` and `QuasiCompact` structure-map instances, and
  `[j.IsOver (Spec (.of D.k))]` express finite-type schemes and a k-morphism.
  `[IsOpenImmersion j]` is the open immersion hypothesis. There is no
  separatedness hypothesis and no finite-Tor-amplitude hypothesis.
- `scalarReductionSource l E W` is the existing category of sheaves of modules
  over `completedIntegralCommRingSheafUnrestricted l E W`, the recorded limit of
  constant positive quotient coefficients on `W.ProEt`. Its `DerivedCategory`
  is the ordinary unbounded derived category, not a category of coefficient
  systems or an independently introduced adic category. The small site retains
  object universe `u+1` and morphism universe `u`.
- The fixed `o`, `SX`, `SU`, `AX`, `AU`, `st`, `m`, `c`, `q` are the concrete
  presentations of open functors and simultaneous strict quotient data supplied
  by `openTensorQuotientAugmentation`. They are precisely the data the node says
  to let be given by that dependency. No arbitrary map replaces its canonical
  construction. `q` is the recorded `OpenTensorQuotient.Comparison`.
- `pairs` includes exactly `sfIntegralConstructibleCategory l E U` and
  `sfIntegralConstructibleCategory l E X`. Thus each component of the natural
  conclusion quantifies precisely over the stated K and P, including their
  derived completeness, all constructible positive reductions and common finite
  cohomological bounds. No bounds are imposed on their resolutions.

### Clause-by-clause correspondence

| Node clause | Lean rendering |
| --- | --- |
| Exact termwise ringed-slice extension and restriction | The recorded `IntegralOpenReduction.extension`, `restriction`, `shriek`, `star`; the conclusion also supplies exactness instances for restriction in `Completion`. These are conclusions, not new assumptions. |
| Flat-term K-flat representatives | The existing `integralOperationsGoodComplex`, with `flat`, `extendGood`, `restrictGood` in `Completion`. The independent-coefficient K-flat and flat-term predicates are reused; `flat` compares the existing representative presentations. |
| Strict finite tensor towers T and S and their augmented gamma | `integralOperationsTensorTowerFunctor` at `(extensionComplex.obj Q,F)` and `(Q,restrictionComplex.obj F)`, and the recorded `OpenTensorQuotient.StrictSquare` z, its `gamma`, `upper`, `lower` and `RoosNormalization`. No tower is redefined. Lean index n corresponds to exponent n+1, so it covers exactly all positive quotients. |
| Ordinary H, H_U and section-normalized gamma^B | `leftInputs ⋙ q.tensorX.ordinary.tensor`, `rightInputs ⋙ q.tensorU.ordinary.tensor`, and the natural isomorphism `ordinary`. `_ordinary_representative` identifies it with `m.totalComparison.chain` on all good representatives, through the actual exact-functor and tensor representative comparisons. That chain map is normalized on section generators by the dependency. |
| Specified natural lambda_j | `extension : RoosComparison (IntegralOpenReduction.extension l E j o)`, and `extension.derived` on S. `products` and `projections` identify the actual product comparison by every projection; `iso` is natural on strict towers. `first` and `shifted` impose this same product comparison on both signed Roos coordinates. |
| Every strict augmentation is preserved | `RoosComparison.augmentations`, universally quantified over every strict natural transformation from a constant complex. It asserts both first-coordinate formulas, both zero shifted coordinates, and the equality after applying the Roos comparison. This does not infer equality from projections out of a derived limit. |
| Total right derived inverse limit, normalized Roos model | `integralOperationsRoosFunctor`, `integralOperationsRoos` and `integralOperationsRoosMap`, the recorded signed mapping-cocone model. `RoosComparison.derived` composes the actual `mapDerivedCategoryFactors` comparison with `DerivedCategory.Q.mapIso`, giving the representative of the derived-limit comparison. The strict-Roos and exact-product-limit dependencies identify this model with total right derived limit. |
| Definition Gamma = lambda_j inverse after Rlim gamma | `_representative` is the equality `Gamma ≫ j!(tensorComparison) ≫ lambda_j = tensorComparison ≫ Q.map (integralOperationsRoosMap z.gamma.hom)`, with the necessary actual representative comparison factors. This pins Gamma to the specified construction and is equivalent to the displayed inverse formula. It is required for every normalized strict square of the supplied dependency. |
| Recorded completed tensor functors, natural isomorphism | `gamma : completedLeft l E j o ≅ completedRight l E j o`; these helpers use exactly `integralCompletedTensor`. Naturality is part of the natural isomorphism, not separate objectwise choices. |
| Actual completion-unit equality | `_units` is the homogeneous equality `(q.tensorX.chi l E).app (...) ≫ gamma.hom.app K = ordinary.hom.app (...) ≫ shriek.map ((q.tensorU.chi l E).app (...))`. `OpenFactorCoherence.Tensor.chi` is the actual completion unit followed by the recorded completed tensor comparison; its chain normalization is part of q. |
| Both actual chi maps are invertible | `_invertibleUnits` asserts `IsIso` of precisely those same two components for every constructible pair. |
| Canonical open units | `moduleUnit` and `unit` are isomorphisms whose homs are required to equal exactly `ordinaryAdjunction.unit` and `openAdjunction.unit`. They are not arbitrary identifications. |
| Canonical completed tensor/restriction comparisons from the same systems | `restriction : RoosComparison restriction`, plus `tensorRestriction`, with its final representative equation through `restriction.derived` and the Roos map of delta. Delta is an isomorphism of the same strict tensor towers; its components are explicitly `restriction.map z.gamma` followed by `moduleUnit.inv`, in every quotient and every degree. |
| Restriction of Gamma is identity through those comparisons | `_restriction_identity` says `star.map (gamma.hom.app K) ≫ unit.inv.app (completedInside.obj K) = tensorRestriction.hom.app K`. The final representative equation pins `tensorRestriction` to the system-derived comparison, so this equality does not introduce a comparison merely to make the conclusion hold. |
| Integral open projection datum, its finite reductions and actual units | Gamma has the exact constructible source/target for the integral open tensor component of `ExchangeProjectionStage`. Its `_representative`, `_units`, normalized finite delta and restriction clauses give the specified simultaneous finite comparison and unit normalization. As the node says, this supplies that component, not the independent proper or other coefficient-stage data of the larger structure. |

The ordinary representative equality uses `HEq` solely to compare the two existing
presentations of the signed tensor total (`coefficientTotalTensor` versus
`constructibleTensorTotal`) without forcing their large instance expressions to
unfold during elaboration. Both sides are the specified localized chain maps.
The displayed completion-unit square and every completed-tensor equation use
ordinary equality of morphisms with identical endpoints.

### Dependency declarations read and used

All statement dependencies are publicly imported. In particular:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and the reexported coefficient rings.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the reexported completed sheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`:
  `SheafOfModules.localizedSystemExtension`, `localizedSystemRestriction`,
  `localizedSystemExact` and `localizedSystemAdjunction`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the convention
  node `def-weil-scheme-morphism-properties` is represented by the corresponding
  Mathlib `LocallyOfFiniteType`, `QuasiCompact` and `Scheme.Over` declarations.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`:
  `canonicalIntegralReductionTower`, `unrestrictedTowerComplex`,
  `unrestrictedTowerTransition`, `unrestrictedTowerUnit`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; the flat-term notion is the
  recorded `exactFunctor`/`SheafOfModules.IsFlatOnSite` interface publicly
  imported from `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.ExactProductFunctorStrictLimit`:
  `CategoryTheory.exactProductFunctorStrictLimit` (canonical product comparison,
  signed coordinates, naturality and all strict augmentations).
- `Sheaf.SixFunctors.OpenTensorNormalization`:
  `SheafOfModules.openTensorNormalization` and its normalized data.
- `Sheaf.SixFunctors.OpenTensorQuotientAugmentation`:
  `OpenTensorQuotient.openTensorQuotientAugmentation`, `Comparison`,
  `StrictSquare`, `RoosNormalization`. Its public interfaces include
  `IntegralOpenReduction.Operations`, `extension`, `restriction`, `shriek`,
  `star`, their adjunctions; `OpenSemilinearTensor.Comparison` and
  `TotalComparison.chain`; and `OpenFactorCoherence.Tensor` and `Tensor.chi`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: the reexported original
  global `integralCompletedTensor`, `integralCompletedTensorComparison`,
  `integralOperationsTensorTowerFunctor`, `integralOperationsRoosFunctor`,
  `integralOperationsRoosMap`. Its slice specialization is unnecessary for the
  global U/X endpoints here; the actual slice transport is already in o.
- `Sheaf.SixFunctors.ConstructibleTensorCompletion`:
  `constructibleTensorCompletion`, `constructibleTensorTotal`.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionStage`.

Proof-only imports include the ringed open product result, pro-etale exactness
of countable products, strict Roos comparison, sectionwise module limits and
Mathlib's Noetherian/quasi-separated facts. They do not add assumptions to the
statement. Every dependency's recorded interface was sufficient; no dependency
module or new definition node is needed. Helpers in this module only express
this node's comparisons using the existing notions.

### Edge cases and source reading

Checked before writing: empty U or X (zero categories/comparisons), the identity
open immersion (actual canonical units rather than selected identity maps), zero
K or P, exponent one (Lean index zero), and unbounded flat-term representatives
of bounded constructible objects. None requires a nonempty scheme, positive
complex degree, finite Tor dimension over a quotient ring, separatedness, or a
uniform bound on representative terms. The characteristic exclusion remains
explicit even though the completed coefficient constructions themselves can be
formed without it. No false or ill-typed statement was found.

Read the local source `literature/stacks-project/proetale.tex`, Tag 09BP,
`lemma-j-shriek-limits`, and Bhatt--Scholze Lemmas 6.5.5 and 6.5.8 (pp.49--50).
Also read the current `main-20261015` blueprint's open-factor proof of
`prop-sf-pf-coherence` and `def-exchange-projection`. The specified comparison is
the node's explicit augmentation-normalized refinement of those sources, as its
source/proof-origin records say; it is not claimed verbatim in Stacks.

### Searches and validation

- `msearch.py NX lem-sf-open-projection-roos-completion leanfinder` with
  `Open projection completed tensor derived inverse limit strict quotient augmentation Roos canonical units`:
  eight ordinary `AdicCompletion` tensor lemmas (including `ofTensorProduct`,
  `tensor_map_id_left_eq_map`) and no sheaf/strict-Roos open comparison.
- `msearch.py ... loogle 'preservesLimitIso, Functor.mapIso, mappingCocone'`:
  no results; `preservesLimitIso` unknown in that search interface.
- `msearch.py ... grep 'openProjectionRoos|open_projection_roos|OpenProjectionRoos'`:
  no Mathlib result.
- `rg` searches for open projection, completion and Roos names in the project's
  `lean/WeilConjectures` and `lean/Sheaf` found the related tensor normalization,
  quotient augmentation, completion and general strict-limit modules used here,
  but no declaration stating the simultaneous conclusion of this item.
- Searching the exact item id in those source trees and in the upstream-name
  records found no existing module for this item.

The file uses module mode, explicit universe/variable binders and
`autoImplicit false`. Compilation is through `scompile.py` only. The delivery
wrapper's server preflight and separate per-file compilation are the final
validation; the only permitted warning is the main theorem's `sorry` warning.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
