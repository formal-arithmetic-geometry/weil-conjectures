## Worker report

Item: lem-fd-pullback-common-strict-tower-models. The module
`Sheaf.Paper.PullbackCommonStrictTowerModels` states
`WeilConjectures.fdPullbackCommonStrictTowerModels`, with one postponed theorem
proof. All helper definitions contain actual constructions. The structure
`FdCommonStrictTowerModels` packages simultaneous comparison data and their
normalization equations; its existence is the theorem's conclusion, not a
hypothesis. No statement correction or dependency repair is made.

Sources read: the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-fourier-transform/sk-def-trace/def-fd-trace-function.md`,
including its final coefficient-category sentence; the node's six extracted
proof steps; Stacks `proetale.tex`, lemma-pushforward-Noetherian-case (099N),
clauses (2),(5) and proof; and `sites-cohomology.tex`,
lemma-derived-limit-is-ok (0941), proof. The detailed common-tower normalization
is the agent-written extraction recorded in the item's source and proof, rather
than an additional claim attributed verbatim to the short blueprint definition.

Hypothesis and clause correspondence:

- Prime ell: section parameters `(l : ℕ) [Fact l.Prime]`.
  Finite coefficient extension: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`. The theorem is uniform in every finite extension;
  the embedding in an algebraic closure is unused by every integral construction
  in this item. In particular it applies to the carrier of every finite
  subextension of any fixed Omega, with its induced algebra structure.
- Schemes: `{U T : Scheme.{u}}`; noetherian means
  `[AlgebraicGeometry.IsNoetherian U]` and its counterpart for T. Finite dimension
  is `_hdimU : ∃ n : ℕ, topologicalKrullDim U ≤ n`, and `_hdimT`.
  Invertibility in every local ring is `_hinvU : ∀ x : U,
  IsUnit (l : U.presheaf.stalk x)`, and `_hinvT`. These are the stated local
  hypotheses, with no base-field characteristic assumption.
- Scheme isomorphism: `(h : U ≅ T)`. The completed rings and quotient systems are
  precisely `pbcAdicCompletion W (pbcIntegralDatum l E)` and the recorded detailed
  completion. All tower indices are `n : ℕ`, representing exponent `n+1`.
- Fixed identity transports: `fdCoefficientTransport l E W` is the existing
  scalar restriction along `integralDetailedCoefficientComparison W l E`.
  On derived categories this is `integralDetailedTransport W l E`; the canonical
  localization comparison is `fdCoefficientTransportFactors`. No new choice of
  coefficient identification appears.
- Quotient-defined coefficient map invertible: structure field `coefficient_iso`
  is `IsIso (AlgebraicGeometry.Scheme.completedCoefficientMap h.hom ...)` for the
  existing limit-lift map, not an existential replacement ring map.
- Ordinary pullback is exact inverse image with transported action: fields
  `ordinary_exact` and `action` give preservation of finite limits and colimits
  and its natural isomorphism to `proEtaleModuleInverseImage` followed by scalar
  restriction through the inverse of this exact coefficient map.
  `ordinary_computation` requires the *actual* derived counit
  `pbcActualPullComplexCounit` to be invertible on every complex.
- The strict common tower: `fdCommonStrictTower` first transports coefficients,
  applies `completedReductionComplexTowerFunctor`, then applies the actual
  completed-module pullback termwise in the entire strict tower category.
  `tower` identifies it, as a natural isomorphism of strict diagrams of
  complexes, with the recorded `integralOperationsPullbackTowerFunctor` followed
  by the fixed target coefficient transport. Commutation with every quotient
  transition is therefore part of the natural-transformation type, not a family
  of unrelated level isomorphisms. `generators` fixes the isomorphism on the
  canonical tensor-unit generators: the input is `reductionTensorSection ... 1 x`
  followed by `pbcActualModuleUnitSection`, and the output is the actual finite
  pullback unit applied to `coefficientIntegralScalarUnitSection`. The `HEq`
  connects only the identical underlying sections under scalar restriction; it
  does not identify or replace the coefficient action.
- The framework realization is the actual shifted cone: `cone` compares
  `fdCommonStrictTower ⋙ roosF` to the actual
  `integralOperationsPullbackComplexFunctor` with target coefficient transport.
  `cone_product` specifies the unshifted coordinate through `roosEval` and
  `mappingCocone.fst`; `cone_shifted` specifies the shifted coordinate through
  `roosχ`, `biprod.fst`, and `mappingCocone.snd`. These two equations fix the
  cone comparison, not just an arbitrary isomorphism between its objects.
- PBC realization is Rlim of that same tower: `fdCommonDerivedTower` is the
  actual derived coefficient transport, reduction-tower functor and derived
  levelwise pullback. `tower_computation` says the actual levelwise derived
  counit is invertible on *every* tower complex. `derived_tower` compares the
  ambient derived tower on all good representatives to their common strict
  tower, and `derived_tower_counit` fixes that comparison to
  `fdCommonTowerCounit`, composed from the coefficient factorization, reduction
  counit and levelwise pullback counit.
- Product-cone versus Rlim: `roosDerived` and `roosDescent` give one natural
  descent of the actual `roosF`; `rho` is a natural isomorphism from that descent
  to `completedTowerRlim`. They are shared across all input towers.
- Resolution formula: `resolution` quantifies over *every* strict tower complex
  X, every q:X→I with `[QuasiIso q] [I.IsKInjective]` and injective tower terms.
  It requires `QuasiIso (roosF.map q)` and `QuasiIso (roosι I)`, and fixes e to
  the localized ordinary-limit inclusion. The actual `roosι` has coordinates
  `(0,z)`, by its imported definition and `roosι_χ`. The isomorphism d from
  `Q(limit I.asFunctor)` to Rlim(X) is fixed by
  `d.hom ≫ Rlim.map (Q.map q) = fdCommonRlimUnit ... I`.
  This uses the actual right-derived-limit unit, with its canonical
  termwise-limit transport. Finally the shared component `roosDescent ≫ rho`
  equals `Q(H(q)) ≫ e.inv ≫ d.hom`. Thus the stated arrow
  `[iota_I]⁻¹[H(q)]` is retained with the precise derived-limit identification.
- Independence of P, q and common refinements, and all-derived-map naturality:
  `ambient` is an isomorphism of ambient derived *functors*. Its equation
  `normalization` is imposed for every flat-term K-flat representative P, using
  the framework's defining `integralDerivedPullbackComparison`, fixed exact
  coefficient factorization, the normalized cone comparison, and the same
  Roos descent and rho. The expanded counit helper has the identical map as
  `fdCommonTowerCounit`, with expanded endpoints only to control elaboration.
  Naturality of these comparisons includes arrows between any representatives
  and their common refinements; the equation for every q fixes the same derived
  component for every K-injective resolution. This encodes independence through
  the canonical defining comparisons, rather than choosing isomorphisms
  separately for representatives or morphisms.
- Restriction to the named PBC completed pullback and integral full categories:
  `input_mem` is the recorded full-category identification; `actual_ambient`
  restricts the ambient comparison and uses `pbcActualCompletedPull`, the
  existing completion-reflector presentation. `actual_normalization` fixes this
  extra presentation change to the uniquely unit-normalized existing
  `pbcActualCompletedPullback_tower` isomorphism on intrinsically complete
  inputs. Thus this is not an unconstrained alternative completed functor.
  `source_mem` and `target_mem` give membership in the common integral full
  category. `integral` is the natural isomorphism between the corresponding
  `ObjectProperty.lift` functors. `lift` requires its underlying ambient
  component to equal `actual_ambient.hom.app K`. In the suppressed-identity
  notation this is exactly I_U F^s ≅ F^p I_T, with ambient lift `ambient` and
  its specified presentation change.
- No individual quotient complex is assumed K-flat over the completion.
  `integralOperationsGoodComplex` only constrains the original P; its definition
  is exactly K-flatness over the source completed ring and flat terms. The
  resolution formula applies to arbitrary strict towers, and the exact
  tower-pullback computation applies to every tower complex.

Dependency declarations used (recorded modules were opened and their relevant
signatures and docstrings read):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`; resolutions use `QuasiIso`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` reexports the actual
  `Padic.coefficientExtensionRing` and states its positive-level finiteness.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses` reexports the completed
  coefficient sheaf and its actual quotient projections.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`, as used by the recorded
  `integralOperationsGoodComplex` predicate.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices` publicly retains
  `IntegralDerivedOperations`: `integralDerivedPullback` and
  `integralDerivedPullbackComparison`. Its well-definedness module gives
  `integralOperationsPullbackLevel`, its generator-normalized transition,
  `integralOperationsPullbackTowerFunctor`, `integralOperationsPullbackComplexFunctor`,
  `integralOperationsGoodComplex` and `integralOperationsGoodLocalization`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded completed integral
  operations and `constructibleIntegralPullback` (restriction of the same
  ambient integral pullback).
- `Sheaf.Paper.PbcQbarCompletedPullback`: public retention of
  `completedCoefficientMap`, `completedModulePullback`,
  `completedTowerModulePullback`, `completedTowerPullback`, its actual counit,
  `pbcActualPullComplexCounit`, `pbcActualStrictCompletedPull`,
  `pbcActualCompletedPull` and `pbcActualCompletedPullback_tower`.
- `Sheaf.Paper.AdicCoefficientDatum`: `completedReductionComplexTowerFunctor`,
  `completedReductionTower`, `completedReductionTowerComplexCounit`.
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`:
  `integralDetailedCoefficientComparison`, `integralDetailedTransport`,
  `integralStratifiedPerfectDetailed`; the source's noetherian, dimension and
  stalk-unit hypotheses are retained exactly.
- `Sheaf.Paper.FdCoefficientComparison`: `fdCoefficientTransport` and
  `fdCoefficientTransportFactors`, not private copies. Its owning already
  landed definition node is added to stmt_deps.
- `Sheaf.CategoryTheory.StrictRoosModel`: `roosF`, `roosχ`, `roosEval`, `roosι`;
  its already landed definition node is added to stmt_deps.
- Proof imports retain `strictRoosComparison`,
  `Functor.exactFunctor_derivedFunctor`, `Functor.mapDerivedCategoryFactors`,
  `isoSectionwiseInverseImage_equivalence`, `SheafOfModules.exists_scalarExtensionRingIso`,
  `ProEt.countableProducts_exact`, `integralOperationsWellDefined`,
  `integralOperations_preserve_constructible`,
  `ProEtale.finiteCoefficientInverseImageMap_isIso`, and
  `Abelian.functorCategoryAbelian` from their recorded modules or Mathlib files.

Edge cases checked before finalizing: the empty scheme is allowed (its stalk
unit condition is vacuous, correctly); no nonempty base or base characteristic
condition is introduced. Identity isomorphisms and arbitrary scheme
isomorphisms are included. Zero and unbounded complexes are permitted; good
representatives have no boundedness condition. Index zero denotes the first
positive quotient, not the zero ring quotient. The minimal quotient and all
successor maps use the same existing functors. Zero-dimensional and empty
schemes satisfy the dimension binders; no positive dimension is required.
Coefficient/module universe is u+1, small-site objects u+1 and morphisms u;
these are not forced equal. All variables and universes are explicitly bound,
with `autoImplicit false`.

Searches for an existing statement (retained from interrupted work in
searches.jsonl):

- msearch.py / leanfinder: "Completed pullbacks along a scheme isomorphism have
  the same strict quotient tower, with natural normalized Roos comparison".
  Eight generic scheme pullback-isomorphism hits, including
  `Scheme.OpenCover.pullbackCoverAffineRefinementObjIso`; none is this statement.
- msearch.py / loogle: `CategoryTheory.Functor.mapDerivedCategoryFactors`.
  Twelve generic exact-functor factorization results; used its canonical
  coefficient factorization, but none states this completed comparison.
- msearch.py / grep in Mathlib CategoryTheory: `Roos|completedPullback|strict.*tower`.
  No hits.
- msearch.py / leansearch: "The cone of one minus shift computes the derived
  inverse limit of a strict tower of sheaf complexes". Eight generic limit and
  complex-cone hits, including `HomologicalComplex.isLimitOfEval`; none matches.
- rg in project Sheaf and upstream WeilConjectures for the item id,
  `fdCommonStrictTower`, `fdPullbackCommonStrict`, and strict/common tower phrases:
  related Roos, reduction, scalar-comparison and augmentation modules occur;
  no existing declaration states this item. In particular the augmentation
  matching theorem cites these common models as a prerequisite, so is not used
  to define them. Existing coefficient and Roos constructions are reused.

No STATEMENT-DISPUTED flag. The original node statement, proof and source are
unchanged. No new nodes and no dependency modules are included.

## Second reading by Q92

This is a separate self-review pass after resumption; no independent subagent
was started, as the dispatcher prohibits it. The maintainer's independent review
remains required. I reopened the node and final module and checked all fields
against the clauses above. The initial draft failed to fix both cone coordinates
and to connect the intrinsic PBC completed functor to the strict-tower
presentation; the final draft contains `cone_product`, `cone_shifted`,
`actual_ambient` and its unit-normalized equation. I also checked the actual
right-derived-limit unit in `fdCommonRlimUnit`, not an arbitrary isomorphism
from the ordinary limit. `resolution` quantifies over every q and uses one
shared rho, while `normalization` quantifies over every good P. This fixes the
resolution and representative independence through their specified maps.

Compiler repair: the ambient normalization needed an explicitly typed expanded
endpoint presentation of its existing counit; this is a genuine definition
returning `fdCommonTowerCounit`, not another assumed map. Explicit scheme
noetherian qualification and the explicit `(U := U) (T := T)` application avoid
expensive incorrect elaboration paths. The two long lines were shortened.
No hypothesis or conclusion was changed in these elaboration repairs.
