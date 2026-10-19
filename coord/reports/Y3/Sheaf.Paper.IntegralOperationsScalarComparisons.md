## What changed

Proved the additive Roos comparison from the two mapping-cocone coordinates, including
uniqueness. Proved preservation of good representatives by identifying the recorded
ordinary scalar functor with the concrete change-of-rings complex, applying the existing
general K-flat change-of-rings theorem, and transporting K-flatness and termwise flatness.
Proved ordinary internal-Hom comparison naturality by a general closed-adjunction argument:
uncurry, use tensor-comparison and evaluation naturality, and transpose back.
All public signatures and definitions are unchanged. The helper constructions and lemmas
are private and fully proved. Updated the existing node proof and dependencies to record
these arguments. The full module compiles through lcompile.py without warnings.

## Proved and sorry left

Closed 3 of the original 16 holes; added 0 holes and split off 0 statements.
All declarations below belong to DAG node
`lem-pur-integral-operations-scalar-extension`.

The axiom probe on the compiled sandbox module reports only `propext`,
`Classical.choice`, and `Quot.sound` for `scalarRoosMap_existsUnique`.
`scalarGood` and `scalarHomOrdinary_naturality` still inherit existing deferred
proofs through the recorded scalar-extension and closed-tensor data; their new
proof bodies contain no holes. The complete module compiles without warnings
(the last set compilation took 36.7 seconds).

Closed:

- `WeilConjectures.scalarRoosMap_existsUnique`
- `WeilConjectures.scalarGood`
- `WeilConjectures.scalarHomOrdinary_naturality`

Remaining, unchanged:

- `WeilConjectures.scalarPullbackLevel_existsUnique`
- `WeilConjectures.scalarPullbackTower_existsUnique`
- `WeilConjectures.scalarTensorLevel_existsUnique`
- `WeilConjectures.scalarTensorTower_existsUnique`
- `WeilConjectures.scalarPullbackOrdinary_existsUnique`
- `WeilConjectures.scalarTensorOrdinary_existsUnique`
- `WeilConjectures.scalarCompletion_existsUnique`
- `WeilConjectures.scalarOrdinaryTensorChain_existsUnique`
- `WeilConjectures.scalarClosedTensor_existsUnique`
- `WeilConjectures.scalarHomOrdinary_isIso`
- `WeilConjectures.scalarInternalHom_complete`
- `WeilConjectures.scalarOperationsOrdinary_tower`
- `WeilConjectures.scalarOperationsOrdinary_unit`

## No longer needed

No nodes or modules can be retired by this partial delivery: the thirteen remaining
obligations still require the node's finite-free, completion, and representative arguments.
The completed proofs use the two original public imports and the proof imports
`Sheaf.Algebra.Homology.ChangeOfRingsKFlat` and
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.
The unit-route import `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` remains
imported, as required by the fixed unit route. Other proof-dependency baseline imports
removed as unused by the completed proofs:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.CategoryTheory.StrictRoosComparison`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.DerivedCompleteKoszulReconstruction`
- `Sheaf.Paper.DerivedCompleteOnSlices`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.IntegralScalarExtensionUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.WeilCompletedTensorReflector`

The Roos comparison needs no preservation of products: its product comparison is a map,
and invertibility is a separate remaining question. Preservation of good representatives
needs general change of rings, without a finite-free basis calculation. Hom naturality needs
only closedness and the tensor comparison, without completeness or K-injective calculations.

Change record: `coord/changes/IntegralOperationsScalarComparisons.md`.

## Where the brief, the DAG or earlier work was wrong

No false statements or interface repairs were found. The original prose for scalarGood
specialized unnecessarily to finite-free extensions; the available generic coefficient-change
theorem proves its preservation assertion. The site object and arrow universes remain distinct.

Delivery-tool incident: the first required dry run crashed in sharedrepo.worktree,
before compilation or preflight, because git checkout of origin/sheaf-dag exceeded
its 600-second timeout. A retry was started without changing the tools. After more than eight minutes it
still had 183 worktree-capacity requests ahead and was canceled. No delivery was
pushed. All three completed proofs and the dependency update remain in the sandbox.

Continuation check: no delivery process for this item remained active and no delivery
was recorded. The saved Lean changes still match the current public interfaces. The
required dry run has been restarted without modifying any launcher tool.

The resumed dry run compiled the module but found the missing change-record path
in this report; that path is now included. It also identified CoefficientExtensionFinite
as a fixed unit-route import, which has been restored.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
