## What changed

Partial proof delivery for `Sheaf.Paper.SmoothPurityTowerReconstruction`.

Proved exactness of completed evaluation from the supplied exact level evaluation
and exact restriction of scalars. Constructed the ordinary completed transition
sectionwise from the original semilinear transition; the completed limit projections
commute with quotient maps, giving precisely the required linearity. Naturality is
the original strict-system morphism square; sectionwise extensionality proves uniqueness.

Proved the derived transition's existence using `Localization.liftNatTrans`, with
`spCompletedEvaluationFactors` as its two specified lifting comparisons. Its component
formula is `Localization.liftNatTrans_app`. Cancel the invertible target comparison and
apply `Localization.natTrans_ext` to prove uniqueness. Both transitions now come from
proved unique-existence theorems rather than postponed construction proofs.

Added two proved private helpers for coefficient projection compatibility. A private
`import all Sheaf.Paper.SmoothPurityCoefficientTowersAbelian` accesses the already proved
`coefficientRings_eq` identifying the two coefficient systems. Kept every public import,
public signature, definition body, and instance unchanged. Scoped elaboration options
to the two transition proofs. No source-library modules were edited.

Validation: the complete module compiled through `lcompile.py` without errors or
warnings. No new obligations or definition changes are introduced.

## Proved and sorry left

Original holes: 4. Closed: 3. Added: 0. Remaining: 1.
All four declarations are attached to `sk-lem-sp-tower`.

Closed (namespace `AlgebraicGeometry.ProEtale`):

- `spCompletedEvaluation_exact`.
- `spCompletedTransition_existsUnique`.
- `spDerivedCompletedTransition_existsUnique`.

Left unchanged: `AlgebraicGeometry.ProEtale.spTower_reconstruction`.
Its original named theorem, statement, complete natural-language argument and DAG
attachment remain. This delivery does not claim that reconstruction, completeness,
or integral constructibility has been proved. Nothing was split off.

## No longer needed

Removed the following unused private imports from this module's proof context:

- `Sheaf.Paper.SmoothPurityCoefficientTowers`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.CategoryTheory.SequentialTowerEvaluationFull`.
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`.
- `Sheaf.AlgebraicGeometry.ProEtaleReplete`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.
- `Mathlib.Algebra.Homology.BifunctorShift`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`.
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`.

The ordinary private import of `SmoothPurityCoefficientTowersAbelian` is replaced
by the private `import all` of that same module. Every public import is retained.
The proof dependencies of the remaining reconstruction theorem are retained in the
DAG: the six extracted results remain needed for that unfinished argument. Thus no
node or module is claimed pruned from the mathematical dependency closure, and no
node fields are changed. The removed private imports are either already supplied
through the public imports or are unnecessary for the three completed proofs.

## Where the brief, the DAG or earlier work was wrong

The six declared reconstruction dependencies are available; their postponed proofs
are not an obstacle. The remaining work is their actual assembly, including comparing
their chosen tensor/limit presentations with the displayed projection adjoint.

One concrete interface issue encountered while reading that assembly:
`Sheaf.Paper.EllCoefficientFiber` also declares
`AlgebraicGeometry.ProEtale.spCompletedEllProjection`, with independent site and
coefficient universes, whereas the item already owns the same name at equal base
universes. Its formula is the same normalized limit projection. A scratch import
test through `lcompile.py` confirmed that importing both modules fails because the
environment already contains `spCompletedEllProjection._proof_1` from this item.
The coefficient-fiber module must therefore share ownership of this definition
before the planned direct assembly can import it. This packet neither changes that
interface nor bypasses the coefficient-fiber step. The three completed infrastructure
proofs need no such import.

## Second reading by U7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
