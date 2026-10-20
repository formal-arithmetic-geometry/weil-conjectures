## What changed

Proved `WeilConjectures.completedTensorHomTranspose` by constructing the signed transpose from the normalized closed data. The integral and rational assemblies use generic transpose laws; rational braiding naturality is proved by localization and tensor-product induction. Added three proof modules, with two lower lemmas split off as named results. Removed the item's unused private imports after compiling the complete sandbox module set.

## Proved and sorry left

Closed the original target hole `WeilConjectures.completedTensorHomTranspose`. The added lower holes are `WeilConjectures.completedTensor_map_smul_left` (node `lem-coef-completed-tensor-scalar-linearity`) and `WeilConjectures.normalizedRationalEvaluation_naturality` (node `lem-coef-normalized-rational-evaluation-naturality`). `WeilConjectures.localizedTensorBraiding_naturality` (node `lem-coef-localized-tensor-braiding-naturality`) is proved. No definition contains `sorry`. The item has zero remaining holes; this is a decomposition of its one original hole into two strictly lower holes (net closure change: minus one), not a claim that the dependency closure is sorry-free. The whole sandbox compiled with `lcompile.py --all`: scalar module 3.9 s, braiding module 8.8 s, rational evaluation module 4.0 s and item 16.5 s.

## No longer needed

The proof does not directly use the following former private imports of the item: `Sheaf.Paper.CoefficientRingedTensorHomModel`, `Sheaf.Paper.IntegralDerivedOperationsOnSlices`, `Sheaf.Paper.DerivedCompleteOnSlices`, `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`, `Sheaf.Paper.BasicOperationsCoefficientReduction`, `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`, `Sheaf.Paper.ConstantCompletionEquivalence`, `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`, and `Sheaf.Paper.WeilCompletedTensorReflector`; their required declarations arrive transitively through the retained public imports and the three proof modules. No DAG node is bypassed at unit level. The direct proof plan no longer needs `def-pur-integral-derived-operations`, `def-weil-derived-complete`, `lem-fix-operation-reduction`, `lem-pur-rhom-global-sections`, `lem-weil-pbc-constant-completion-equivalence`, `lem-weil-pbc-ringed-internal-hom-exact-restriction`, or `lem-weil-pbc-ringed-koszul-completion-reflector`: their work is already packaged by the recorded normalized closed structures and completion-unit comparison. They can remain transitive dependencies of those structures; no whole module is claimed to have left the target import closure.

## Where the brief, the DAG or earlier work was wrong

The item's existing plan treated rational braiding naturality as an inline step, but the localized tensor map is bilinear and requires a separate tensor-product induction in Lean. The completed-tensor scalar and normalized rational evaluation equations likewise need independent statements at the current declaration interface. No target statement or existing definition was changed.

## New nodes

Added `lem-coef-completed-tensor-scalar-linearity`, `lem-coef-normalized-rational-evaluation-naturality`, and `lem-coef-localized-tensor-braiding-naturality`, with matching modules and declarations. The first two are strict lower lemmas left for parallel proof; the third is proved in this delivery. A retained attempt at proving the rational evaluation lemma established the generic pure-tensor induction, but its specialization failed at endpoint transport and elaboration. That attempt is excluded from the delivered Lean files. The scalar lemma requires compatibility of the recorded constant-section action with completed tensor; generic linear-category instances alone do not state that compatibility.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
