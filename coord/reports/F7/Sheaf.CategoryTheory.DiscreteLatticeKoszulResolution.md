## What changed

Filled three infrastructure proofs in
`lean/Sheaf/CategoryTheory/DiscreteLatticeKoszulResolution.lean`, preserving every public
signature and definition. Invariants preserve addition by limit extensionality. The action
category is Grothendieck: its diagram category has a separating family of evaluation-left-adjoint
images of a separator, pointwise exact filtered colimits, and the induced coproduct separator.
Transporting this structure along `Action.functorCategoryEquivalence` gives the existing
K-injective resolution theorem. Scalar-restriction naturality is exactly the naturality of
Mathlib's `preservesLimitNatIso`.

Only two private proof imports remain, for evaluation adjunctions and exact filtered colimits
in diagram categories. The final module compiled cleanly through `lcompile.py` (23.2 seconds).

## Proved and sorry left

Closed 3 of the 4 original holes:

- `Profinite.DiscreteLattice.invariants_additive`.
- `Profinite.DiscreteLattice.resolutions`.
- `Profinite.DiscreteLattice.restrictionInvariants_naturality`.

One original hole remains:
`Profinite.DiscreteLattice.discrete_lattice_koszul_resolution`, covered by
`lem-sfb-discrete-lattice-koszul-resolution` and its existing complete proof docstring.
No holes added, no statements split off, and no definitions or statements changed.

## No longer needed

Removed the following unused private proof imports:

- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.CategoryTheory.SheafTensor`.
- `Sheaf.CategoryTheory.InternalActionSitePresentation`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`.
- `WeilConjectures.CategoryTheory.DoubleComplexTotal`.
- `WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison`.
- `Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality`.
- `Mathlib.CategoryTheory.Abelian.Injective.Resolution`.
- `WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy`.
- `Sheaf.CategoryTheory.RingedSiteModules`.
- `Mathlib.Algebra.Homology.ModelCategory.Injective`.

These are not used by the completed infrastructure proofs. No DAG node or module is declared
mathematically obsolete: the unfinished main theorem retains its existing proof plan and
all its declared dependencies. No module withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

The planned dependency `LatticeInjectiveKoszulAcyclicity` publicly imports this item for
`KoszulModel` and the shared definitions. Thus it cannot be imported back into this item
without first separating the shared interface. Also, `CoefficientComparison.normalization`
quantifies over arbitrary K-injective resolutions, while the stated
`finite_model_restriction_comparison` supplies its resolution formula only for nonnegative
termwise-injective resolutions. The main theorem needs an additional transport argument
from those resolutions to arbitrary K-injectives. Neither issue affects the three proofs
completed here. The blueprint unit route and DAG proof dependencies remain unchanged.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
