## What changed

Repaired all three cycle findings from the return of `8a84392fd79`. Their common
return path ended at `lem-zl-field-shriek-composition-qcqs`'s proof dependency on
this item. Replaced that node's circular system-realization argument by a direct
completed-ring argument using its existing `sfCompositionLambda`,
`sfCompositionGamma` and `sfCompletedCompositionOnTower` definitions. The unclaimed
`Sheaf.Paper.FieldShriekCompositionQcqs` now privately imports
`RingedRestrictionExchangeOpenDescent` instead of this item, and its sourced
proof-in-words matches the revised node. Every signature, definition body, public
import, statement dependency and unit route remains unchanged. No new theorem
hole is added by this repair. The module compiles cleanly (16.7 seconds).

Full overlay graph traversal checks all three reported cases: none of
`lem-sf-integral-canonical-ambient-models`,
`lem-sf-integral-comparison-recursion-laws`, or
`lem-sf-integral-expression-coefficient-squares` reaches
`lem-sf-integral-compactification-system-realization`. The return's three edges
therefore have no return path. The changed proof dependency list is precisely the
union of its proof-step uses. See
`coord/changes/G2-field-shriek-direct-completed-route.md` for the route and all 354
consumer modules; no consumer needs adaptation.

Proved the existence theorem `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization` from three strictly separate assembly obligations. The proof constructs the natural reduction comparison from the actual normalized reconstruction counit, proves its normalization by functoriality and inverse cancellation, and transposes the whole-system coefficient square through the actual adjunction to prove the required realization intertwining equation. This is a decomposition, not a net closure of the mathematical obligations.

Extracted the 17 existing realization-data declarations verbatim to `Sheaf.SixFunctors.IntegralCompactificationRealizationData`, publicly reexported by the original module. Added `IntegralRealizationAssemblyData` with ambient-model and recursion-law interfaces consisting of unchanged existing field types. No existing signature, definition body, attribute or target statement changes. All 400 downstream modules retain the identical declarations through the reexport; none is adapted. See `coord/changes/G2-integral-realization-data-interface.md` for the full old block and consumer audit.

The three new theorem modules separately state ambient canonical models, explicit expression recursion, and coefficient squares/finite support projections. Their docstrings contain sources and complete proof plans. The final theorem contains no `sorry`. Compilation is through the required project-server launcher. The final entry module compiled cleanly (4.7 seconds); the extracted declaration module compiled cleanly with only its original public imports (55.1 seconds). The support modules also compiled in dependency order before the entry-module check; delivery reruns the complete server preflight.

## Proved and sorry left

Closed the one original hole by decomposition:

- `WeilConjectures.IntegralSystemRealization.integralCompactificationSystemRealization`, node `lem-sf-integral-compactification-system-realization`.

Proved private helpers `good_counit_isIso`, `reduction_normalization`, and `coefficient_intertwining`. The first applies the existing complete private theorem `normalizedSequence_counit_isIso` of `CoefficientExtensionReductionModel` through a private `import all`; its actual dependency node is `lem-pur-coefficient-extension-reduction-model`; the others are direct adjunction calculations.

Added three holes, each a named public theorem with proof exactly `by sorry`:

- `WeilConjectures.IntegralSystemRealization.integralCanonicalAmbientModels`, node `lem-sf-integral-canonical-ambient-models`.
- `WeilConjectures.IntegralSystemRealization.integralComparisonRecursionLaws`, node `lem-sf-integral-comparison-recursion-laws`.
- `WeilConjectures.IntegralSystemRealization.integralExpressionCoefficientSquares`, node `lem-sf-integral-expression-coefficient-squares`.

Actual counts: original item 1 hole; delivered item 0 holes; new modules 3 holes. Net mathematical hole change is +2, not a proof of the full underlying realization construction. There are no holes in definitions or private declarations.

The additionally adapted `FieldShriekCompositionQcqs` retains exactly its three
pre-existing holes, all owned by `lem-zl-field-shriek-composition-qcqs`:

- `WeilConjectures.sfFieldShriekCompositionIntegral_existsUnique`.
- `WeilConjectures.sfFieldShriekCompositionRational_existsUnique`.
- `WeilConjectures.sfFieldShriekCompositionQbar_existsUnique`.

Thus the packet has six holes in total: three new realization obligations plus
three unchanged field-composition obligations; the repair closes and adds zero
holes beyond the original decomposition.

## No longer needed

The edge `lem-zl-field-shriek-composition-qcqs` →
`lem-sf-integral-compactification-system-realization` and the corresponding
private import are no longer needed: that proof route works directly with the
specified completed-ring maps and the existing coefficient/refinement comparisons.
This removes a circular dependency, not a mathematical assertion or module.

No mathematical node or unit is pruned. The original stated proof dependencies remain needed in the separate assembly obligations. In particular semilinear sections, proper/open pasting, basic realization, generator coefficient coherence, expression recursion, contextual intertwining, ringed tensor coherence and compatible towers are retained in their appropriate obligations. `IntegralRealizationRecursion` is not used because it imports the original item and would create a cycle.

The entry module's original individual imports are replaced by a public import of the extracted data module, which retains the original public-import closure verbatim, and private imports of the three actual assembly lemmas plus the complete normalized-counit proof. The extracted data module also drops the original private proof imports: its complete declaration block compiles using only the five original public imports. The separate theorem modules import the proof dependencies their obligations actually require. This import cleanup does not claim that the mathematical nodes are pruned from the target closure. Experimental imports of `CoefficientSystemUnboundedComparison`, `RingedSiteGrothendieckCoefficientUniverse` and the direct-image existence helper were removed because the final assembly does not use them.

The removed original private import lines (from both the entry module and extracted declaration module) are:

- `Sheaf.Paper.NormalizedDVRTower`
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `WeilConjectures.Compactification.Refinement`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedComplete`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.Paper.SfIntegralReductionTower`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower`
- `Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.CoefficientSystemDerivedComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.SixFunctors.IntegralOpenReductionComparison`
- `Sheaf.SixFunctors.OpenTensorNormalization`
- `Sheaf.SixFunctors.SemilinearProperOpenMatePasting`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.SfCommonStageDirectImage`
- `Sheaf.SixFunctors.GeneratorReductionStatement`

## Where the brief, the DAG or earlier work was wrong

The returned packet checked Lean import acyclicity but missed a long DAG cycle
through the broad purity-conventions node and field-shriek composition. The repair
changes the field-shriek proof route itself; it does not erase necessary statement
edges or alter the landing tools. All three cycle findings had this same final
return edge, now removed with its argument replaced as described above.

The reviewed re-split dependencies do not directly supply the full record used by this Lean statement. Their interfaces use different presentations and need actual operation/adjunction/model normalization bridges. The new obligations make those gaps explicit rather than pretending that objectwise finite evaluation detects derived morphism equality.

`ExpressionRecursion.Reconstruction.reduction` asks for full `Good` reductions from constructibility alone. The published input domain separately assumes `Good`, including Tor bounds and compatible origins. The present assembly does not infer those extra conditions from constructibility and does not use that problematic closure field directly; the recursion obligation must use the recorded good intermediate domains. Its docstring explicitly preserves this restriction.

One transparency experiment made the coefficient-sequence ring sheaf irreducible and prevented Lean from identifying its two system-category presentations. It was removed from the extracted declaration module. The data block is verbatim original source. No source-library declaration is removed or changed.

## New nodes

`def-sf-integral-realization-assembly-data` owns the new `AmbientModels` and `RecursionLaws` structures, which separate existing realization fields without weakening them.

`lem-sf-integral-canonical-ambient-models` is precisely the ambient operation, section/compositor, mate-pasting and open reconstruction part; it contains no expression comparison family.

`lem-sf-integral-comparison-recursion-laws` is the finite-tree comparison construction with its six explicit formulas; it contains no generator intertwining, reduction normalization or finite support projection assertion.

`lem-sf-integral-expression-coefficient-squares` is the remaining coefficient/context and finite support projection result for a given recursively normalized comparison family. The main proof supplies the reduction normalization and converts its coefficient equation into the required realization equation by an independently proved adjunction calculation.

Updated the existing data-owner node's Lean attachment to the extracted module and the item's proof/dependency records to the actual assembly. Change record: `coord/changes/G2-integral-realization-data-interface.md`.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
