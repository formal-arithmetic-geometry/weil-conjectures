## What changed

Replaced the proof hole of `AlgebraicGeometry.ProEtaleWeilSheaf.properOrdinaryProjection_isIso` by a proof from two separate finite-stage statements. The original signature and public imports are unchanged. Added proof imports of `CommonProperProjectionFiniteModel`, `RationalProperProjectionInvertible`, `CommonStagePullbackTensorNaturality` and `CompletedPullbackTensorNaturality`.

The proof lifts each ordinary bounded constructible input using the exact `R.image` clause, enlarges its common-stage representative to the compositum, applies the finite rational projection theorem, and transports invertibility through the tensor and counit comparisons. A generic adjunction calculation proves the required projection square; another calculation reverses the supplied tensor normalization; naturality handles both the stage and ordinary lifting isomorphisms. The three generic private calculations are reused verbatim from `NativeProperProjectionRealization`, without importing that parent or creating an import cycle. Two further proved generic corollaries cancel isomorphisms and transport invertibility along input isomorphisms. A private irreducible `projectionMate` wrapper fixes the endpoints before specialization; its API is proved by unfolding only in abstract categories. Applying the corollaries through this wrapper avoids expensive normalization of concrete coefficient-category expressions. The original public projection definitions are unchanged.

Added `RationalProperProjectionInvertible` and `CommonProperProjectionFiniteModel`, each with one sourced theorem. The first concerns the projection mate at a single finite coefficient field, with no ordinary realization or common-stage descent. The second concerns tensor/adjunction compatibility of finite-stage inclusion, and asserts no projection invertibility. The new rational projection definition is the actual counit transpose, with no postponed data construction. The proper finite-stage theorem needs only finite type over the field; it imposes no separatedness hypothesis on either structure map. Properness of the geometric map is proved by stability under base change.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtaleWeilSheaf.properOrdinaryProjection_isIso` by a complete Lean combination of the lower statements. There are no holes in the item module. This is a decomposition, not a net proof: one original hole closed and two lower holes added.

Remaining holes added by this delivery:

- `WeilConjectures.rationalProperProjection_isIso`, node `lem-sf-rational-proper-projection-invertible`.
- `AlgebraicGeometry.ProEtaleWeilSheaf.properCommonProjection_finiteStageComparison`, node `lem-sf-common-proper-projection-finite-model`.

Each remaining theorem has exactly `:= by sorry`, a source and a complete proof in words. No definition contains a hole. The final item file compiles cleanly through `lcompile.py` in 48.2 seconds. The two lower modules also compile separately within the 60-second limit. Diagnostic options, trace commands and temporary probe files were removed before delivery.

## No longer needed

No existing module is withdrawn and no original public import is removed. The proof uses the smaller common-stage and rational naturality interfaces instead of importing `DerivedPullbackTensorIso`; its higher coherence package is unnecessary for this calculation. The original mathematical route through finite coefficient models and the field projection formula is retained; its two separate lower obligations are now explicit. No global pruning is claimed.

The proved package theorem `compactSupportProjectionFormula_fieldStages` is not applicable directly: its signature requires a supplied `SixFunctorOperationDatum`, whereas this item supplies an arbitrary normalized ordinary proper comparison. The finite comparison theorem therefore makes the missing intrinsic finite-stage normalization explicit, without assuming an entire operation package. The adopted étale rational projection theorem likewise has different category coordinates; no adopted declaration or proof was modified or removed. The original direct dependency `thm-sf-pf-field` is therefore replaced in this item by the two explicit intrinsic finite-stage statements. Its integral-to-rational argument remains the source of the new rational node. `def-exchange-projection` and the finite-Tor reasoning occur below that node rather than as separate imports of this item. These changes do not assert that any adopted source module is globally unused.

## Where the brief, the DAG or earlier work was wrong

The original first proof step combines finite rational projection invertibility, common-stage tensor normalization, and descent of adjunctions. Those are distinct Lean obligations: the available public field-stage theorem carries an additional operation package and the ordinary comparison does not provide that package. The new statements separate these obligations. The second step now has an explicit tensor/counit mate calculation and uses only the normalization fields actually present in C.

Edge cases checked mathematically for the lower statements: zero objects, empty schemes, identity proper maps, repeated coefficient fields and enlargement to a common coefficient field. The finite-stage comparison is independent of the projection theorem, so it cannot assume the invertibility it is used to transfer. The finite rational theorem uses ordinary proper projection followed by localization, with uniqueness of the right adjoint handling the arbitrary supplied adjunction.

## New nodes

`lem-sf-rational-proper-projection-invertible` states the proper counit projection formula at one finite rational coefficient field, including arbitrary choices of right adjoint and adjunction. Its source is the rational-stage paragraph of `thm-sf-pf-field.proof.md` and the identity-open proper specialization. It is strictly a finite-field coefficient subargument, omitting both common-stage descent and ordinary realization.

`lem-sf-common-proper-projection-finite-model` states finite-stage tensor, pull and push comparisons together with their two normalization equations. Its source is the compatibility paragraph of the same proof and BS 6.7.2, 6.8.14--6.8.15. It includes no projection map or isomorphism assertion. Both new nodes inherit the item chapter and unit. Searches of the imported blueprint and project found the broader field-stage theorem and the coefficient-change mate theorem, but no existing declaration with these intrinsic normalized interfaces. No change record is needed: only the item, its node and new modules/nodes were changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonProperProjectionFiniteModel": "9d01322602207026f9caa9386325a22839328af8", "Sheaf.Paper.OrdinaryProperProjectionInvertible": "39dd0b4884aadb4d3476b5ba8146cd08ddfe51e6", "Sheaf.Paper.RationalProperProjectionInvertible": "bfdd65f4344d2f78ad9753455ba1372b730f5a40"}, "results": {"Sheaf.Paper.NativeCompactProjectionFormulaTheorem": {"hash": "025b2c528a43454080169e9ddb62d387c80eaa10", "status": "OK"}, "Sheaf.Paper.NativeProperProjectionRealization": {"hash": "a5224fc4ecf3b95c4c95e42ff8df633243877b25", "status": "OK"}}, "seconds": 99, "time": "2026-10-28T12:49:01+0800", "transitive": 1, "version": 1}
```

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
