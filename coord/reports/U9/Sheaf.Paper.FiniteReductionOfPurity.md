## What changed

Partial proof delivery for `Sheaf.Paper.FiniteReductionOfPurity`. Existing public
signatures, definitions and public imports are unchanged.

* Proved `finiteReductionOfSmoothTrace` from the main purity reduction square.
  A proved private helper `finiteReductionSupport_naturality` transposes the
  scalar-adjunction naturality square for the actual support comparison. The trace
  proof uses that square and the chosen exceptional comparison's counit equation,
  then maps the purity reduction equation through compact support.
* Proved `finiteReductionOfCompositionCoherence` by rewriting the three-arrow path
  using `smoothPurityCompositionCoherence`, applying the main reduction equation to
  `f ≫ g`, then expanding the smaller-coefficient composition formula.
* Proved `finiteReductionOfAffineOrientation` by the exact existing theorem
  `FiniteDiagonalReduction.affineOrientationReduction`, adding its proof import.
* Updated the existing DAG proof to distinguish these implemented arguments from
  the five retained open clauses. The existing normalized diagonal/unit route stays.

These are proofs from the stated library dependencies, which themselves can still
use sorry; this delivery does not claim those transitive axioms have been eliminated.
No new data, assumptions, theorem statements or split-off modules are introduced.

Validation: lcompile.py compiled the final module cleanly in 17.6 seconds.
All eight existing theorem signatures were checked textually unchanged.
The import-direction check accepts the new diagonal-orientation dependency.

## Proved and sorry left

Three of the original eight holes closed, all in
`WeilConjectures.PurityFiniteSetting`:

* `finiteReductionOfSmoothTrace`
* `finiteReductionOfCompositionCoherence`
* `finiteReductionOfAffineOrientation`

Five existing named public theorem holes remain unchanged, all attached to
`thm-pur-finite-reduction-of-purity`, with their existing source/proof docstrings:

* `WeilConjectures.PurityFiniteSetting.finiteReductionOfPurity`
* `WeilConjectures.PurityFiniteSetting.finiteReductionOfUnitSmoothTrace`
* `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource`
* `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`
* `WeilConjectures.PurityFiniteSetting.finiteReductionOfBaseChange`

Zero holes added and zero split off. Mathlib searches: LeanFinder returned
algebraic trace/reduction lemmas, Loogle returned the adjunction naturality API,
and pinned-Mathlib grep found no geometric purity/exceptional-reduction result. This uses the brief's allowance for a module
with several holes: proved clauses are delivered while other existing clauses stay
as their original named statements. The private helper is fully proved.

## No longer needed

The full composition clause needs neither `finiteReductionOfCompositionSource` nor
`finiteReductionOfCompositionExceptional`: rewrite the already stated composition
formula on both coefficient levels. Those separate clauses remain required parts
of the item, so their declarations and their planned dependencies are retained.
No module is withdrawn and no global reachability pruning is claimed.

Removed the following unused direct proof imports (some remain transitively available
through other dependencies; their public declarations are preserved):

* `Sheaf.Paper.FixedFinitePositiveCoefficientTwist`
* `Sheaf.Paper.ExchangeProjectionSuppliedDomains`
* `Sheaf.Paper.SmoothPurityMap`
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
* `Sheaf.AlgebraicGeometry.DiagonalRegularPureCodimension`
* `Sheaf.Paper.SmoothExceptionalBaseChangeStatement`
* `Sheaf.Paper.PurTwistSheafLocallyFree`
* `Sheaf.Paper.FiniteCoefficientFlatModel`
* `Sheaf.Paper.FiniteCoefficientReductionFlatModel`
* `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`
* `Sheaf.Paper.PurityAffineLineOrientation`
* `Sheaf.Paper.PurityDiagonalDualizingObject`
* `Sheaf.AlgebraicGeometry.CartierKummerMap`
* `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
* `Sheaf.Paper.BasicOperationsCoefficientReduction`
* `Sheaf.Paper.CohomologicalSmoothnessFiniteComparison`
* `Sheaf.Paper.CohomologicalSmoothnessTheorem`
* `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
* `Sheaf.Paper.PurityDiagonalBaseChangeCompared`
* `Sheaf.Paper.PurityDncInvariance`
* `Sheaf.Paper.PuritySectionInvariantIntrinsic`
* `Sheaf.Paper.VectorBundlePurity`

The new direct proof import is `Sheaf.Paper.FiniteDiagonalOrientationReduction`.
`Sheaf.Paper.PurityCompositionCoherence` remains a direct proof import. All original
public imports are preserved. No DAG dependency is declared globally unnecessary
while the retained open clauses still use its planned argument.

## Where the brief, the DAG or earlier work was wrong

The DAG labels the final composition assembly elementary, but following each of its
constituent coefficient squares is unnecessary for this particular clause. Rewriting
by the existing composition formula gives a shorter complete proof.

The existing diagonal-orientation reduction theorem already has the exact affine
orientation equation, including all positive levels and arbitrary ramification.
The old item imported many lower orientation-construction modules but did not import
this stated theorem directly. It is now used as intended by proof Step 2.

The current blueprint proof's fibrewise-equality inference is not used. The existing
reviewed DAG's normalized diagonal route is preserved for the still-open main square.
No false statement or required interface repair was found in the clauses proved here.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
