## Worker report

The delivery states `AlgebraicGeometry.ProEtale.SpTowerShriek.strictCompactificationComparisonRealization` in `Sheaf.Paper.SmoothPurityStrictCompactificationComparisonRealization`. Its proof is `sorry`; all helper definitions contain actual data. The conclusion simultaneously constructs the normalized tower calculus and its comparison laws. No assertion that a proper projection or proper exchange is invertible occurs.

### Hypotheses and coefficient conventions

* Prime ell: `(l : ℕ) [Fact l.Prime]`.
* Finite E/Q_ell: `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, using the recorded valuation ring and quotient constructions.
* Positive level n of the paper is index `n-1` in Lean: `SpTowerShriek.R l E n` is O_E/ell^(n+1). Thus Lean index zero is the first positive coefficient level, never exponent zero.
* `B`, `tau`, `S`, `D`, `ev`, `Ev` are the existing actual ring sheaves, actual quotient transitions, strict sequence-site category, ordinary unbounded localization and evaluations. Small pro-etale objects have universe u+1 and morphisms universe u. No equality of those universes is imposed. The fixed-scalar derived presentation has smaller Hom universe than intrinsic derived modules; `ComparisonAdjunctionCoordinates` explicitly permits this.
* The theorem has no hypotheses named Base, Operations, OpenExchange, normalization, cartesianness, origin coherence, or invertibility: these packages are existential conclusions. `Base` fixes the equivalence by HEq on actual sections, restrictions, actions and morphisms, and fixes the ell-power versus uniformizer-power identification by the actual ideal equality. The ramification data are conclusions, not extra assumptions on E.
* Separated finite type f is rendered by `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`; `c : Compactification f` is supplied. The arbitrary base-change map g occurs inside `sq : IsPullback h f' f g`. There is no smoothness, field-base, or invertibility hypothesis on g.

### Every clause of the statement

1. **Actual towers and simultaneous realization.** `comparisonTowerEquivalence` is the ordinary derived equivalence induced by the recorded identity-section equivalence `b.realization`. It uses the exact functor and inverse, not diagrams of derived objects. `comparisonTowerTensor`, `comparisonTowerPullback`, `comparisonTowerDirectImage`, and `comparisonTowerOpen` explicitly conjugate the recorded operations to `DerivedCategory (spCoefficientTowers l E T)`. The normalized sequence-site coordinates in the conclusion therefore give operations on the actual tower categories. No map is recovered merely from its evaluations.
2. **Derived tensor evaluates to the level tensor.** `Base.calculus.tensorEvaluation` is the specified natural isomorphism. Its `levelTensorModels` and tensor-evaluation model fix it on signed K-flat total complexes. `StrictSystemComparisons.semilinear` identifies this very calculus with a complete `SemilinearDerivedSectionsData`, rather than choosing a new tensor.
3. **Tensor reduction formula.** `StrictSystemComparisons.tensorReduction` displays the equality of actual reduction maps. The right side first applies coefficient extension to tensor evaluation at m, then `scalarTensor h`, then the tensor of the two actual input reductions. This includes noncartesian inputs and nonflat quotient maps.
4. **Direct-image transition and its specified counit mate.** `Operations.geometry f` includes the recorded `generic` geometric calculus, with `transitionFormula` and its actual `push`, `ordinaryAdjunction`, and evaluation identifications. `comparisonCoefficientMate` is that calculus's existing `coefficientMate` with the actual source and target coefficient systems; its definition is the specified adjunction transpose, not an arbitrary map. Thus the transition is G_n(t) after b_mn.
5. **Composition coherences.** `StrictSystemComparisons.tensorCoherence` and `directImageCoherence` explicitly include both scalar composition isomorphisms for three indices. Identity/reduction cocycles are also part of the recorded `Data` and actual strict-system operations. No b_mn is required to be invertible.
6. **D+ comparison.** `StrictPlusComparisons` asserts an adjunction-evaluation square whose left comparison is exactly `mapDerivedCategoryPlusCompatibility` and whose right comparison is exactly `rightDerivedFunctorPlusCompatibility`, the canonical comparison with injective-resolution derivation. The square includes both unit and counit equalities. `StrictPlusEvaluation` supplies the evaluation square and pins it by the component equation involving the canonical plus/unbounded comparisons and `Geometry.pushEvaluation`. Enough injectives is a conclusion of this package; evaluation of an injective is never claimed injective.
7. **F^c and the actual projection composite.** The existing `F` is literally `openD c.i ⋙ push c.g`. The existing `projection` is the proper adjunction transpose of tensor-pullback followed by `(counit, identity)`, then proper direct image of the open tensor hom and the compactification pullback compositor. `comparisonLevelProjection` writes that same word at a finite level, including the last compositor along `c.comm.symm`. `StrictWordComparisons.projectionNaturality` makes it a natural transformation in both arbitrary unbounded inputs.
8. **The actual exchange composite.** The existing `exchange` and `comparisonLevelExchange` both instantiate `SuppliedExchangeProjection.compactificationExchangeFromData`. This definition is the unit--square--counit proper mate followed by the open exchange, with the actual base-changed compactification. Its type is a natural transformation on ordinary unbounded derived categories.
9. **Open-unit normalizations.** `Operations.openTensor_mate`, `OpenExchange.inverse_mate`, and their finite analogues `ComparisonLevels.openTensor_mate/openExchange_mate` specify the inverse maps by the open adjunction transposes of the actual open unit. `tensorPullback_normalized` fixes the finite pullback-tensor comparison to the geometric calculus's normalized comparison. `comparisonLevelOpenAdjunction` is derived by exact localization of `finiteOpenAdjunction`; no arbitrary adjunction or sign is introduced.
10. **Evaluation of complete words.** `StrictWordComparisons.projectionEvaluation/exchangeEvaluation` are actual morphism equalities, including the specified F comparison, tensor evaluation and pullback evaluation at every endpoint. `Fcomparison` itself is the composite of open evaluation and right-derived direct-image evaluation. The geometric and open packages retain the evaluation of adjunction units and counits. These laws concern the whole word, not only isomorphic endpoints.
11. **Published finite-coefficient projection.** `StrictFiniteProjectionComparisons.projectionWord` compares the actual finite word with `ProEtale.projectionMapOfCompactification` through fixed scalar realization, the pinned tensor map, and `comparisonFiniteF`. It therefore includes in particular the finite-field finite-coefficient domain of `def-exchange-projection`. The statement actually compares the same word whenever the finite coefficient construction is defined; it does not infer its invertibility. `tensor_pin` uses the existing `FiniteRealization`, `TensorModel`, and `FiniteTensorPin` interfaces, fixing scalar actions, pure total summands, and resolving representatives. In addition to pinning `e.equivalence`, it now pins `e.underlying` by `HEq` to `comparisonFiniteUnderlying`, the canonical additive sheafification counit. This rules out the independent locally constant unit rescalings identified in the returned review.
12. **Etale-origin exchange.** `StrictFiniteExchangeComparisons.etaleExchange` compares `comparisonLevelExchange` with `compactExchangeTransportAtWitness` for every bounded-below etale object L, ambient object N, and specified comparison `alpha`. The latter definition literally applies the etale compactification exchange of `def-cbc-exchange-map` and the source/target comparisons from the finite-level compact-support theorem. `StrictFiniteCoordinates` pins the right-image coordinates by the normalized pull square and both adjunction equations. `comparisonFiniteF` is constructed from the canonical open coordinate square and this uniquely determined right-image square. The witnesses are quantified separately at each level; no compatible family is required.
13. **Twist towers.** Tensor evaluation and the tensor reduction equality quantify over every L in the actual tower derived category. They therefore apply to every specified coefficient-twist tower from `IntrinsicCoefficientTwistsUnrestricted`, on any scheme where ell is invertible. No arbitrary replacement for its transitions is introduced, and no extra global invertibility-of-ell restriction excludes the untwisted statement.
14. **Excluded extra assumptions.** All reductions are arbitrary quotients, all input objects are arbitrary ordinary-derived objects unless the explicit etale-witness clause restricts them. There are no quotient-flatness, normalization, cartesianness, finite-Tor, constructibility, compatible-witness or isomorphism hypotheses on these transformations.

### Dependency declarations and sources read

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`, together with `coefficientExtensionIntegers`, uniformizer, coefficient ideal and quotient definitions.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `Scheme.ProEt.topology`.
* `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`: `spCoefficientCommRings`, `spCoefficientTowers`, `SpCoefficientTowersAbelian`, `sp_coefficient_towers_abelian`.
* `Sheaf.Paper.SemilinearDerivedSections`: `SemilinearDerivedSectionsData`, `semilinearDerivedSections`, `AdjunctionEvaluation`, `evaluation_mate`; its public `SemilinearDerivedCalculus`, `SemilinearGeometryDerived`, `SemilinearGeometryOps` interfaces fix all actual operations and transitions.
* `WeilConjectures.Compactification.RefinementCategory`: `Compactification.Refinement` and its category. `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback` and `isPullback_i_ofIsPullback`.
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: `ExchangeProjectionStage`, `compactificationExchangeFromData`, `compactificationProjectionFromData`. The recorded dependency intentionally exposes this independently importable supplied-data API. The finite projection being compared is the original `ProEtale.projectionMapOfCompactification` from `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
* `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`: `Etale.rightDerivedLowerShriekOfCompactificationPlusBaseChangeMap`.
* `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`: `isIso_csAuxiliaryExchange`, and its public finite-level origin/comparison interfaces. We do not assume its invertibility conclusion for arbitrary inputs.
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`: the supplied intrinsic twists, including `sfQbarTwistingFunctor`, and its published coefficient tower conventions.
* Proof imports include `SystemTensorReductionFormula.tensor_reduction_formula`; Mathlib adjunction-mate pasting; Grothendieck enough injectives; `DerivedCategory.Plus.exists_injective_nonempty_iso`; `Functor.kInjective_computes`; right-derived plus uniqueness and compatibility; `SheafOfModules.openTensorNormalization` and its finite normalization data; `ProEtale.compactSupport_exchange_transport`; separated implies quasi-separated; and `QuasiCompact.of_comp`.
* Existing `SpTowerShriek.Base`, `Geometry`, `Open`, `Operations`, `F`, `projection`, `exchange`, `Fcomparison` are reused from `Sheaf.Paper.SmoothPurityTowerShriekLevels`. No use is made of the downstream theorem `tower_shriek_levels` or of its Laws package. These public helper definitions already own this notion, so they are not copied. Per stages/2-statements rule 7, the maintainer must omit the automatic reverse proof import of this item into `SmoothPurityTowerShriekLevels`, which would close an import cycle; its existing helper definitions are the reason for that exception.

### Edge cases checked

Equal coefficient indices give the actual identity scalar comparisons and identity reduction. Lean index zero is positive exponent one. Zero objects and zero/noninvertible reduction transitions are allowed; no cartesian-object field occurs. The quotient Z/ell^2 to Z/ell is not treated as flat. Empty schemes are covered by the existing site and adjunction constructions. Identity open immersions and identity base changes retain their canonical units and compositors; the finite witness clause allows arbitrary alpha, including the identity witness. Arbitrary base change is retained. Tensor specializes to any supplied twist object without asking for compatible etale origins. All source and target types of the displayed composite maps are checked by Lean.

### Searches

* LeanFinder via msearch.py: “Derived tensor and direct image for strict inverse systems of varying coefficient module sheaves, evaluation of compactification projection and base change adjunction mates”. Eight hits, mainly LightCondensed and general module/sheaf constructions; no exact theorem.
* Loogle via msearch.py: “CategoryTheory.Adjunction, CategoryTheory.DerivedCategory” returned no hits (the latter is not the root name). Corrected query `CategoryTheory.Adjunction.mkOfUnitCounit` returned the constructor and its two unit/counit lemmas; generic infrastructure only.
* Mathlib grep via msearch.py: `strict.*compactification|SpTowerShriek` in CategoryTheory returned no hits.
* rg in lean/WeilConjectures and lean/Sheaf for strict compactification/comparison and the node id located the existing tower-shriek helper interfaces and generic normalization modules, but no declaration with this simultaneous conclusion. The node id has no existing declaration in WeilConjectures. A final name search for the new main and coordinate-helper names in WeilConjectures, Sheaf and dag/lean_names_upstream.json found no collisions.

No new independent notion and no unusable dependency record was found: the additional canonical-coordinate helpers belong to this statement and are listed in lean.declarations. The accepted stage-1 statement, proof split, and dependency lists have been preserved. The stage-handoff paragraph added to brief-stage2 §0 on 2026-10-22 explicitly authorizes this stage-2 recording despite the previous stage-1 live-wins refusal. No STATEMENT-DISPUTED flag applies.

### Validation

Wrapper compilation initially exposed the 60-second elaboration limit. Diagnostic prefix compiles isolated generated structure code and comparison elaboration; proposition-only law packages are now declared in Prop, and bounded-below comparisons are pinned directly to the published canonical comparison. No file was split and no timeout was raised. The resumed compile isolated an unresolved universe in instance search for the constant-section map. The helper now supplies `integralCoefficientRingSheafify.{u, u}` and its `isRightAdjoint` explicitly to `toSheafify`; the coefficient sheaf, constant scalar map and mathematical statement are unchanged. The theorem signature in the node record was synchronized with the final Prop-valued package. Final wrapper compile and delivery results are recorded below.

Server validation on 2026-10-23: `deliver2.py Q10 lem-sp-strict-compactification-comparison-realization --no-push` printed `OK (dry run): commit 7034f1a8e47 passes the preflight and compiles; nothing pushed`. The module has only the expected declaration-uses-sorry warning, one postponed theorem, no overlength lines, and an exact signature record.

## Second reading by Q10

No independent second worker was started: the dispatcher brief explicitly forbids starting other agents and assigns the independent mathematical review to the maintainer. The report above is the author's clause-by-clause self-audit, not an independent review. In this repair I reread the node and the changed finite-projection law with its normalization interfaces open: the canonical sheafification counit is now fixed by an explicit HEq conjunct, removing the locally constant unit ambiguity without restricting any input or changing the main theorem signature.

## Repair of returned head 35971ea2f3ff

The saved packet was retained. Before editing, the prescribed dry run passed at
`9625519b5c9`; that mechanical pass does not resolve the mathematical H3 return.
The current shared node differs from the saved packet only in its `lean` field,
so the accepted natural-language statement, dependency lists and proof split
remain the base for this repair. No direct Git commands or live-source edits
were performed; the delivery wrapper refreshes its own worktree from current main.

**H3 repaired.** `StrictFiniteProjectionComparisons` previously fixed only
`e.equivalence`. A locally constant unit could rescale `e.underlying`, changing
the pure-total tensor comparison and therefore changing `tensor T n` independently
on different schemes. The new helper `comparisonFiniteUnderlying` constructs the
canonical comparison for `sfIntrinsicModuleEquivalence`: at a fixed-scalar sheaf
`M`, it is `asIso` of the additive sheafification adjunction counit at the
underlying additive sheaf of `M`; naturality is that of this same counit. This
is actual data, using the existing sheafification adjunction and its `IsIso`
counit instance. No existence choice or extra postponed proof is introduced.

The conjunction immediately following `HEq e.equivalence ...` now contains
`HEq e.underlying (comparisonFiniteUnderlying l E b T n)`. The forward comparison
is the sheafification counit, whose inverse is the sheafification unit on the
original sheaf. Thus the sections used on both sides of `finiteTensorPure` are
canonical; `finiteTensorModel` and the representative pin then fix the derived
tensor comparison with no free scalar factor. In particular the complete
`projectionWord` equation compares precisely the published projection map.
All other clauses and the main theorem signature are retained.

**Sources and searches for this repair.** Read the full canonical construction
`ProEtale.finiteCoefficientIntrinsicRealization` and its exactness theorem in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`, and
`Scheme.sfIntrinsicModuleEquivalence` in
`Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`. The former literally
uses `PresheafOfModules.sheafification` along the constant-scalar unit; the latter
is this functor's `asEquivalence`. Read `FiniteRealization`, `finiteTensorPure`,
`finiteTensorModel`, and `FiniteTensorPin` in
`Sheaf.SixFunctors.OpenTensorNormalizationData`. Mathlib's
`PresheafOfModules.sheafificationCompToSheaf` is `Iso.refl`, so the underlying
additive sheaf is precisely the additive sheafification, making its counit the
required canonical comparison. `msearch.py ... loogle
"PresheafOfModules.sheafificationCompToSheaf"` returned that exact declaration.
Targeted `rg` searches in `lean/Sheaf` and `lean/WeilConjectures` found no public
helper already giving this intrinsic comparison; the analogous `cUnderlying`
in `FiniteConstantCoefficientTransport` belongs to the different continuous
coefficient realization. No new independent notion is introduced. Read Stacks
00YV in local `literature/stacks-project/sites.tex` and the current blueprint
operations proof (2), which require the canonical underlying-sheaf recipe.

**Edge cases rechecked.** For a scheme with nontrivial constant unit `-1`,
replacing only `e.underlying` by its negative no longer satisfies the new HEq
pin. If `-1 = 1` this is already the identical automorphism. Nonconstant locally
constant units are excluded by equality of the entire natural isomorphism.
Empty schemes and zero sheaves remain included; their unique section maps give
the same counit. No restriction on coefficient index, scheme, quotient flatness,
input complex, or base-change map was added.

The earlier return's import-cycle advisory remains the maintainer handoff already
recorded above: the parent module supplies the existing helper definitions, and
its automatic reverse proof import must be omitted or split by the maintainer.
No downstream theorem is used in this repair. The independent second review
belongs to the maintainer; no additional agents were started.

The first repair compile found that the new helper must receive the existing
`b : Base l E` to supply `b.finite n` for `sfIntrinsicModuleEquivalence`.
The helper now has that argument, like the adjacent finite-comparison helpers;
this uses the finiteness already in the existential conclusion.

Repair validation on 2026-10-23: `scompile.py` passed both sandbox and library
module compilation with no errors or non-sorry warnings. The main signature
still matches the node record verbatim, the file has one `sorry`, and no line
exceeds 100 characters. The prescribed post-repair dry run follows.

Post-repair `deliver2.py --no-push` printed `OK (dry run): commit 39c689b070e
passes the preflight and compiles; nothing pushed`. H3 has a substantive Lean
change: the canonical underlying comparison helper and its HEq pin.
