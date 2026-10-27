## What changed

The original realization theorem keeps its signature and is assembled from four
strict components: geometric smooth reconstruction, reindexing and limit comparison,
smooth purity and Tate comparison, and completed compact-support exchange.
The unchanged definitions from PreservesKInjectives through Result move to
Sheaf.Paper.IntegralGeometricComparisonData, publicly reexported by the item, to avoid
cyclic imports between the component theorems and their common diagram definitions.
SmoothPart, ReindexingPart and PurityPart package literal subsets of Diagram.

The assembly constructs the exceptional natural isomorphism by full faithfulness
from the tower mate. Its reconstruction and limit formulas, the natural integral
image comparison, counit-preserving uniqueness, and preservation of K-injectives by
fixed-ring reindexing equivalences have complete Lean proofs. A separate transpose
calculation uses the recorded reduction and counit equations and mateEquiv_counit.
No existing statement, definition body, public name or target meaning is changed.

Validation: all seven modules passed the project lcompile service. The final transpose
and assembly checks passed without warnings and within the 60-second acceptance limit.
Static checks confirm that the original theorem signature and all original definition
blocks are unchanged, every node signature matches Lean, and the four holes are exactly
the named component theorems listed below.

## Proved and sorry left

The original hole in
AlgebraicGeometry.ProEtale.IntegralGeometricComparison.integral_geometric_comparison_realization
is replaced by a complete assembly proof. This is a decomposition, not a proof of
all underlying mathematics: one original hole is closed and four holes are added.
There is no sorry in a definition or private helper.

The remaining public theorem holes, each in its own module with its complete source
proof in the docstring and a matching node, are:

- geometric_smooth_reconstruction_setup:
  lem-pur-geometric-smooth-reconstruction-setup.
- integral_geometric_reindexing_realization:
  lem-pur-integral-geometric-reindexing-realization.
- integral_geometric_purity_realization:
  lem-pur-integral-geometric-purity-realization.
- integral_geometric_support_realization:
  lem-pur-integral-geometric-support-realization.

integral_geometric_transpose_identity is proved from the existing counit and
exchange-reduction equations, without a postponed step in its proof.

## No longer needed

No module or mathematical dependency is withdrawn: the remaining components still
need the original source lemmas, and unfinished parents still need this realization.
The following direct private imports are removed from the item because their uses
belong to the split component proofs; their dependency nodes remain in those plans:

- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
- Sheaf.CategoryTheory.CofinalRoosRestriction
- Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
- Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison
- Sheaf.Paper.PurCompletedReductionReindexing
- Sheaf.Paper.SemilinearDerivedSections
- Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
- Sheaf.Paper.AutomorphismConstructibleStageEquivalence
- WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint
- Sheaf.Paper.CompletedOperationTowerSubstitution
- Sheaf.SixFunctors.IntegralBasicOperationShift
- Sheaf.AlgebraicGeometry.SemilinearScalarDerivedComparison
- Sheaf.Paper.PurStrictIntegralExchangeNormalization
- Sheaf.Paper.SemilinearExchangeReindexing

All original public imports are preserved transitively by the data module. No unit
statement or unit proof step is bypassed. The existing fixed-ring K-injective
preservation theorem for equivalences replaces a fresh proof of that elementary step.

## Where the brief, the DAG or earlier work was wrong

The integral conclusion in tower_exceptional_base_change has a coefficient-rank-one
premise. It does not directly construct the general-E integral data required here.
The setup component instead states the construction from the general integral
adjunction theorem, preserving the original general coefficient setting.
The original single module owned both the comparison definitions and their existence
theorem; separating these owners is necessary for component modules to import the
same definitions without a cycle. Edge cases checked in the component statements
include empty schemes, dimension zero, and arbitrary finite extension coefficients.
No counterexample or target statement change is asserted.

## New nodes

- def-pur-integral-geometric-comparison-data owns the unchanged definitions and the
  three component records. Its module contains no holes.
- lem-pur-geometric-smooth-reconstruction-setup states construction of compatible
  integral adjunction and smooth reconstruction data, with the invertible tower mate.
- lem-pur-integral-geometric-reindexing-realization states only the reindexing,
  varying-coefficient K-injectivity and normalized limit comparison component.
- lem-pur-integral-geometric-purity-realization states the Tate and smooth-purity
  realization for already specified smooth reconstruction packages.
- lem-pur-integral-geometric-support-realization states the completed proper/open
  exchange and its whole-tower reduction for already specified integral adjunctions.
- lem-pur-integral-geometric-transpose-identity states and proves the resulting
  adjoint-transpose equation for an exchange whose reduction is already known.

The definition relocation is recorded in
coord/changes/integral-geometric-comparison-data-extraction.md.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
