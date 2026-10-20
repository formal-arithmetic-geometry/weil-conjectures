## What changed

Proved the three remaining assertions in `Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows` without changing any public signature or canonical comparison definition.

For arbitrary commutative coefficients, constructed a private equivalence from modules over the constant ring sheaf to sheaves of fixed modules by restriction along the constant-presheaf sheafification unit. Full faithfulness follows from local bijectivity of that unit; essential surjectivity uses an actual presheaf module and its sheafification. The sectionwise direct-image comparison and uniqueness of adjoints transport ordinary open base change and the clopen extension/direct-image isomorphism.

The specified inverse base-change map is invertible because its open-adjunction counit is evaluated on an object in the essential image of open extension. The specified clopen comparison is a composite of invertible adjunction units. Exactness of clopen direct image identifies its total derived functor with exact open extension.

For finite evaluation, verified the exact/right-derived adjunction unit formula and preservation of mates by localization, with no monoidal or flat-resolution assumption on tower categories. Identified `betaInv` with localization of the termwise `singleBetaInv`, then proved the evaluation identity using composition coherence of exact localization. All supporting lemmas are private and proved in this module. The existing open-unit theorem is moved before its new use and proved by transport of the ordinary open-unit result through the same equivalence.

Updated the node proof to describe this route. The assigned module and its node are changed. The private proof-theorem registrations and section scopes are recorded in `coord/changes/Y9-strict-tower-proper-open-proof-interface.md`, including the full consumer audit. No consumer is edited. Validation: the final module compiles through `lcompile.py` in 41.0 seconds; all 18 public signatures match the original, no forbidden declaration or hole remains, and all Lean lines satisfy the 100-character limit.

## Proved and sorry left

Closed 3 of 3 existing holes:

- `AlgebraicGeometry.ProEtale.StrictTower.betaInv_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.beta_evaluation`.
- `AlgebraicGeometry.ProEtale.StrictTower.openToR_isIso`.

No holes added or split off. No `sorry` remains in the delivered module.

## No longer needed

The proof uses the existing ordinary open-base-change and clopen-comparison theorems, transported to constant-ring modules. It does not introduce a separate stalkwise or componentwise theorem for either invertibility assertion. Removed the unused private import `Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange`: its ordinary derived interface is not used. The shared dependency node `lem-cbc-proetale-extension-zero-base-change` remains needed through `FiniteOpenBaseChangeNormalized` and the ordinary base-change theorem. Removed the direct private imports of `ProEtaleRingedOpenClosed` and `ProEtaleRingedOpenComparison`, and the direct proof dependencies `lem-weil-pbc-proetale-ringed-open-closed` and `lem-weil-pbc-proetale-ringed-open-comparison`, from the shortened open-unit proof. These existing modules remain available to their other consumers; no module is withdrawn. Removed redundant direct private imports of `ProEtaleOperations`, `StrictConstantTowerOperations`, and `StrictTowerOpenExtension`; their required interfaces are already supplied by the retained imports. All existing public imports remain.

## Where the brief, the DAG or earlier work was wrong

The earlier node proof recorded the three assertions as remaining obligations. The ordinary sheaf comparisons needed for invertibility are already proved in the source library. Their use for arbitrary coefficients requires an equivalence with fixed-module sheaves; the finite coefficient realization alone does not cover arbitrary `B`.

The derived adjunction needed for evaluation is the exact-left/right-derived construction used by `jAdj`. The older monoidal derived-adjunction mate theorem cannot directly be applied to tower categories. The private localization calculation proves the needed unit and mate formulas for the actual construction.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
