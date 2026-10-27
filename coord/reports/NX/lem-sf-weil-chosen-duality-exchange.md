## Worker report

The module `Sheaf.Paper.WeilChosenDualityExchange` states
`WeilConjectures.WeilChosenDualityExchange.weil_chosen_duality_exchange`.
Its sole postponed theorem is this item. All helper definitions contain real data;
the conclusion records the missing lifts rather than assuming them. In particular,
there is no ambient exceptional-adjoint admissibility argument or perfectness assumption.

Hypotheses and clauses:

- `D : FiniteFieldDatum` supplies the finite field and its algebraic closure.
  `C : D.CoefficientDatum` supplies the prime, its inequality to the characteristic,
  and the algebraic closure of the l-adic field with its algebra structure.
- `X Y : PodConstructibleMate.Models D` are finite-type models over the finite field;
  their full-subcategory witnesses are precisely local finite type and quasi-compactness.
  `IsSeparated X.obj.hom`, `IsSeparated Y.obj.hom` give separatedness over the field.
  `f` is a model morphism, and its three property instances say separated finite type.
  `fiberModels D` gives exactly its geometric base change, including the base structures.
- `S : SixFunctorOperationDatum D C E 1 (Nat.le_refl 1)` supplies the recorded
  operation datum, with `A = S.closure` the common-stage part. `E : Type u` is an
  auxiliary finite coefficient field used only to name this existing datum; its
  common-stage portion ranges over all finite subextensions and does not depend on E;
  `W : CommonLifts D C S.closure.commonStage` is its already defined standard lift. The
  pull, support, direct and exceptional functors are their existing declarations.
  No replacement operation is introduced. `cf`, `cy`, `cx` retain compactifications
  of f and the two structure maps, and `geometricCompactification` is literal base change.
- `Carrier` is the existing common-stage bounded constructible category and `Pair`
  is the existing `IsoAlgebra` fixed-pair category for its named geometric Frobenius.
  `Data.homX`, `.homY`, `.homPoint` conclude full Hom-pair domains at X,Y,s.
  `HomLift.obj`, `.map` identify the exact previously partial common-stage Hom.
  `HomLift.closed` and `.evaluation` identify its ordinary tensor-Hom transpose:
  the latter is the original argument-first evaluation, with the recorded Koszul symmetry.
  This pins the standard Weil Hom structure by evaluation, including the inverse
  structure in its contravariant input. `Data.unit` is the constant coefficient pair;
  `Constant.normalized` is the standard Frobenius tensor-unit equation.
- `ordinaryAdjunction` and `exceptionalAdjunction` reuse
  `IsoAlgebra.mapOfNatIsoAdjunction` with the prescribed mate equations of W.
  `OrdinaryMaps` states preservation of the original ordinary unit, counit and both
  Hom bijections. No alternative adjunction is supplied as a hypothesis.
- `Data.composition_carrier` fixes the support compositor to
  `A.commonStage.composition`, inserting only the existing scalar-extension
  functoriality transport. `chosenComparison` applies `conjugateIsoEquiv` under
  the composite canonical exceptional adjunction and the X structure adjunction.
  This is exactly c_can. Its source is G J_Ycan and its target J_Xcan.
- `Data.Laws` quantifies over EVERY functor JX,JY and EVERY structure adjunction
  adjX,adjY on these pair categories. The coefficient-unit values are the two
  chosen dualizing objects. `chosenComparison` composes G(nY), c_can and nX inverse,
  where each n is `Adjunction.rightAdjointUniq` at that same coefficient unit.
  It has type Iso in the pair category, so it is an isomorphism of Weil pairs.
- `Data.projection_carrier` fixes projection to the specified
  `compactSupportProjectionComponent A.commonStageExchange`; `.projection` concludes
  that its standard lift is an isomorphism. The complete constructible second-input
  domain is used at field coefficients, without a first-input Tor assumption.
- `transposeComponent` starts with the INVERSE projection and the tensor-Hom
  evaluation counit for F(M),omegaY. It then applies exceptional.homEquiv,
  closedX(M).homEquiv and ordinary.homEquiv in precisely that order. This is tau_M.
  `Exchange.tau` has contravariant natural-transformation type and `tau_app` fixes
  every component to that formula. All its objects lie in the pair categories.
- `Exchange.exchange` is the natural morphism D_Y F to Q D_X, and `exchange_app`
  fixes its component to tau_M followed by Q(HX(1,c)). Thus it is exactly e_M.
  Its type retains the stated variance. Neither tau nor exchange has an IsIso field.

The structure arrow of X is written `f ≫ structureMap D Y`; in the over category
this is its structure map by the defining condition on f. This introduces no new
geometric hypothesis and allows the compositor to be expressed without an arbitrary
identification of functors.

Dependency declarations read and reused:

- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory` (literal common-stage pairs).
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilFrobeniusPullback`,
  `sfCommonStageWeilComplex`, `sfWeilPrimeInvertible`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedTensor`,
  `commonStageHomPairs`, `commonStageDerivedInternalHom` and their representative formulas.
- `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`,
  used through the normalized support operation datum rather than copied.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, likewise through
  the ordinary direct-image operation datum.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, used through the constructible
  exceptional operation datum, without the optional ambient interface.
- `Sheaf.Paper.SixFunctorOperationDatum` and its public stages module:
  `SixFunctorCommonStages`, `SixFunctorPushStage` (including composition and both adjunctions).
- `Sheaf.SixFunctors.CoefVerdierWeilEquivariance`:
  `coef_verdier_weil_equivariance`, `CoefVerdierWeil.commonUnit`, `.commonUnitor`,
  `.commonMu`, `.pointModel`, `.structureModel`.
- `Sheaf.Paper.CompactSupportProjectionFormula`:
  `compactSupportProjectionFormula`; its public `ConstructibleProjectionMates`
  gives `compactSupportProjectionComponent` (the exact map in the normalization).
- `Sheaf.Paper.ConstructibleMateCoherence`: the existing definition owner
  `def-sf-constructible-common-stage-data` records `CommonLifts`,
  `CommonLifts.pullFunctor`, `.directFunctor`, `.supportFunctor`, `.exceptionalFunctor`,
  `.tensorFunctor`, `CommonStage`, `commonStageCategory`, `commonFrobenius`,
  `commonModelTensor`, `commonModelTensorComparison`, and
  `commonModelPullbackComponent`. The model declarations remain owned by
  `def-pod-constructible-weil-model-squares`.
- `Sheaf.Paper.DerivedAutomorphismHomEvaluation`: `podArgumentFirstEvaluation` is
  recorded by the existing definition owner `def-sf-derived-argument-first-evaluation`;
  `podCommonClosed` is owned by `def-sf-adic-closed-reindexing-maps`.
  `DerivedPullbackTensorIso` supplies the signed braiding.
- Mathlib `CategoryTheory.Adjunction.rightAdjointUniq`, `conjugateIsoEquiv`,
  `Adjunction.homEquiv`; upstream
  `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction` supplies the
  normalized `IsoAlgebra.mapOfNatIsoAdjunction`.

Edge cases checked before writing: identity f and identity adjunction comparisons;
empty schemes (no dimension maximum or nonempty hypothesis); zero M and zero objects;
arbitrary, nonstandard chosen adjunction units/counits (nX,nY depend on the actual
adjunctions, not just their functors); arbitrary Weil structures and rational structure
maps with nonunit integral valuation (no invariant lattice or effective descent required);
all constructible inputs (no perfectness); no invertibility of tau/e is inferred.
The universe u is explicit throughout, as in the recorded `CoefficientDatum` and
`SixFunctorCommonStages` interfaces. No site object/morphism universes are identified.

Searches for an existing exact statement:

- `msearch.py leanfinder`: “Weil equivariant Verdier exchange from projection evaluation
  and three adjunction transposes for chosen dualizing objects”. Eight generic closed
  category hits, including tensorLeftHomEquiv; none has the geometric statement.
- `msearch.py loogle`: `CategoryTheory.Adjunction.rightAdjointUniq,
  CategoryTheory.Adjunction.homEquiv`. Found
  `Adjunction.homEquiv_symm_rightAdjointUniq_hom_app`, reused via rightAdjointUniq.
- `msearch.py leansearch`: “Verdier duality Weil sheaves exchange projection formula
  chosen right adjoint”. Eight ordinary sheaf-pullback/right-adjoint hits; none is the item.
- `msearch.py grep`: `dualityExchange|chosenDuality|rightAdjointUniq|homEquiv`
  in Mathlib CategoryTheory/Adjunction. Found the uniqueness and ordinary transpose API.
- `rg`: chosen.duality/chosenDuality/ChosenDuality/dualityExchange/duality_exchange in
  `lean/Sheaf`, `lean/WeilConjectures`; no exact statement. Searching the item ID in
  upstream Lean also found none. Further source inspection found the reusable standard common-stage lift interface in
  ConstructibleMateCoherence and its model category. The two new existing:true owner
  records in this delivery make those plain declarations explicit. The theorem nodes
  `lem-pod-constructible-mate-coherence` and `lem-pod-derived-automorphism-hom-evaluation`
  were removed from stmt_deps, while the existing owners `def-pod-weil-lift-interfaces`,
  `def-pod-partial-closed-interfaces`, `def-sf-adic-closed-reindexing-maps`,
  `def-sf-constructible-projection-mates`, `lem-pur-derived-pullback-tensor-iso`, and
  `def-a1-common-stage-coefficient-unit` were added. No theorem conclusion is used as a
  statement prerequisite.

Proof imports are retained for the DAG's stated proof dependencies. The generic
`lem-pod-verdier-composition-mate-normalization` has no recorded module locally;
its required composition-mate construction is given explicitly here by the existing
Mathlib `conjugateIsoEquiv`, with no further postponed theorem.

No statement correction or disputed statement is asserted.

## Second reading by NX

I reread the repaired item node, the exchange module, and each added owner record. The Lean theorem signature is unchanged and still renders the same hypotheses and existential `Data.Laws` conclusion. The two former theorem dependencies are no longer statement dependencies: every plain definition used by the statement is now covered by an existing definition owner (`def-sf-constructible-common-stage-data`, `def-sf-derived-argument-first-evaluation`, `def-sf-adic-closed-reindexing-maps`, `def-sf-constructible-projection-mates`, `lem-pur-derived-pullback-tensor-iso`, and `def-a1-common-stage-coefficient-unit`, together with the already landed lift/model owners). No mismatch was found; no Lean file changed.

## New nodes

`def-sf-constructible-common-stage-data` is an existing:true definition owner for the literal common-stage Frobenius, category/stage abbreviations, tensor and pullback component, and `CommonLifts` functors in `Sheaf.Paper.ConstructibleMateCoherence`; it cites the finite-field operation datum, model squares, algebraically closed coefficient category, and derived tensor/Hom definitions. Searches in LeanSearch, LeanFinder, `rg`, and Mathlib grep found no separate owner or Mathlib match, so the published declarations are recorded without a duplicate module.

`def-sf-derived-argument-first-evaluation` is an existing:true definition owner for the literal `podArgumentFirstEvaluation` construction in `Sheaf.Paper.DerivedAutomorphismHomEvaluation`; it cites `def-pod-partial-closed-interfaces`. LeanSearch, LeanFinder, `rg`, and Mathlib grep found only the published project declaration and no separate DAG owner, so no module is duplicated.

Validation: server compilation and delivery preflight are run through the prescribed
`scompile.py` and `deliver2.py` wrappers; final results are recorded below.

Repair validation: `scompile.py NX lem-sf-weil-chosen-duality-exchange` completed
successfully for the unchanged exchange module, in sandbox and named-module modes,
with no errors or warnings. `deliver2.py ... --no-push` compiled the module and
checked every existing declaration named by the two new owner records, then reported
`OK (dry run): commit b79f98324cf passes the preflight and compiles; nothing pushed`.
The node statement is unchanged; its Lean record and repaired stmt_deps are the only
changes to the item. The new records own existing declarations without new Lean files.
The signature stored in `lean.statement` is verbatim from the module. The delivery
wrapper refreshed the base and built the repaired commit on current main.

## Repair of return H2 (7970656dc970)

Added the two new definition-owner records requested above; removed only the two specified theorem nodes from stmt_deps. Added def-sf-adic-closed-reindexing-maps, def-sf-constructible-projection-mates, lem-pur-derived-pullback-tensor-iso, and the advised def-a1-common-stage-coefficient-unit. The latter theorem dependency is genuine: pullbackTensorCommonBraiding is constructed from its uniquely normalized existence theorem. Source reading used literature/blueprint/latest (main-20261024), lem-fix-weil-operations.proof.md and prop-weil-operations.proof.md, and Stacks 0GMX/08J9. The common lift owner reproduces the pull/tensor normalizations, direct and exceptional mates, the literal support map on the base-changed compactification, and comparison conjugation for arbitrary geometric compactifications. The evaluation owner records exactly beta followed by Hom-first evaluation for every permitted pair, with no extra naturality assumptions. No Lean data or theorem statement was changed.

Actual repair searches: LeanSearch returned 8 generic Frobenius/category hits; LeanFinder returned 8 generic tensor linear-algebra hits; Mathlib CategoryTheory grep for the five project names returned 0 hits. The exact query and result objects are in each new node and searches.jsonl. Blueprint searches for common-stage lift and argument-first evaluation each returned 0 nodes. The ancestor command reports None for this native item; new nodes retain that ancestor and the item-prefixed via chain.

## Repair of return H2 (aaa17dc65c4e)

Replaced `lem-pur-derived-pullback-tensor-iso` in the item `stmt_deps` by the landed definition owner `def-sf-rational-common-tensor-symmetries`, whose declarations include `pullbackTensorCommonBraiding_existsUnique` and `pullbackTensorCommonBraiding`. Added the landed definition owners `def-weil-frobenius-square-exchange` for `FrobeniusExchange.geometricCompactification` and `def-sf-operation-stages` for `SixFunctorCommonStages`. The Lean module and its theorem signature are byte-identical to the prior delivery; only the item dependency list and its explanatory note changed.
