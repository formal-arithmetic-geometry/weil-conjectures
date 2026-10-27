## What changed

Proved `WeilConjectures.rationalCoefficientCategoryComparison` in
`Sheaf.Paper.RationalCoefficientCategoryComparison` by assembling all five existing
DAG comparison dependencies. The finite datum is built field by field from the
integral identity and completion-inverse coherence results. Normalized descent
supplies its common-stage fields; whole-tower comparison supplies the simultaneous
system and its three scheme-coherence equations. The fixed-pair result supplies
the geometric-fibre instances and the finite/common Frobenius equivalences with
the exact required functor pins.

Added five private proof imports for those dependencies. Removed the redundant
private proof imports listed below. Public imports, declaration signatures,
definitions, docstrings, and target statements are unchanged. Updated the existing
node's proof order to match the Lean assembly: coefficient descent precedes
whole-tower comparison, whose Lean interface already supplies full pullback systems.
No definitions or other modules were changed; no change record is required.

Validation: the item compiled through lcompile.py; final delivery preflight also
checks compilation, declarations and propagated axioms. The proof is a reduction
to the existing stated dependencies, some of which remain unproved; it does not
claim that the entire target dependency closure is axiom-free.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.rationalCoefficientCategoryComparison`
(node `lem-fd-rational-coefficient-category-comparison`).

Added holes: zero. Split off: zero. Holes left in the delivered module: zero.
The five existing dependency nodes remain needed; their existing holes are not
new holes of this delivery.

## No longer needed

Removed these direct private imports (their necessary mathematics remains behind
the five retained dependency modules; no module is withdrawn or claimed globally
unreachable):

- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`
- `Sheaf.Paper.FiniteStagePairCategory`
- `Sheaf.Paper.PbcCommonStageCones`
- `WeilConjectures.Algebra.Homology.RoosComplex`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.IntegralOperationsWellDefined`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
- `Sheaf.Paper.IntegralPullbackComparisonRealization`
- `Sheaf.Paper.IntegralStratifiedPerfectCharacterization`
- `Sheaf.Paper.IntrinsicQbarCategory`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.PbcRationalCategory`
- `Sheaf.Paper.PbcScalarExtension`
- `Sheaf.Paper.SfRationalizationKaroubi`
- `Sheaf.Paper.SfScalarExtensionComposition`

All five declared proof dependencies are used; none is pruned. Cleared the old
parent-level `tool_uses` entries because the parent no longer directly invokes
those lower results: integral stratified-perfect characterization, triangulated
scalar localization, PBC scalar extension, finite-free completed scalar comparison,
scalar-extension composition, integral pullback realization, Roos complex,
pro-etale countable-product exactness, K-injective resolutions, constructibility
preservation, K-flat resolution, well-defined integral operations, finite type over
noetherian schemes and the finite-type dimension bound. Their role is retained
inside the five existing comparison nodes, whose dependencies are unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The file retained the older eleven-step
docstring and lower-level imports, whereas the current DAG already has five
extracted lemmas. Their current Lean interfaces suffice for a complete assembly.
In particular wholeTowerIntegralPullbackComparison accepts complete coefficient
data and returns full pullback systems, so coefficient descent is performed first.
No unit statement or unit route is bypassed.

Searches: LeanFinder found generic finite-category/Galois equivalences but no
replacement for these normalized sheaf coefficient comparisons. Loogle did not
know the project-specific IsoAlgebra.mapOfNatIso identifier. The msearch grep
query had no Mathlib match; repository rg found the five designated interfaces.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
