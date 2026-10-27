## What changed

Implemented `AlgebraicGeometry.ProEtale.SpIntegralOrientation.reduction_injectivity`
without changing its statement or the definitions `realizedRight`, `beta`, `delta`,
`targetComparison`, and `rho`. The proof explicitly expands the Hom bijection,
proves its identity/naturality formula, evaluates its composite to obtain `rho`,
cancels the finite comparison, and transfers equality to shifted single objects.
The private proved helper `shifted_single_hom_ext` lifts through the fully faithful
single-and-shift functor, uses the natural exact-evaluation comparisons, and
recovers strict tower maps from their components. It does not assume the input
morphisms are invertible.

Added `Sheaf.Paper.IntegralOrientationShiftedSheafModels` for the geometric
shifted-sheaf presentations used in Step 1 of the existing proof plan. This
statement contains no map variables and no injectivity conclusion. It isolates
identification of the two objects, leaving all Hom detection and categorical
cancellation implemented in the item. Both isomorphisms are consumed only in a
proposition proof, with no data defined by choosing witnesses.

Updated the original node's proof, proof dependencies and proof origin to agree
with the Lean argument, and added the matching node for the geometric step.
No definition, public declaration signature, target or unit route was changed.
Both files compiled together successfully (49.7 s and 55.8 s); profiler output
showed only a few seconds in proof processing, with no slow definition. The
temporary profiling options were removed before the final delivery checks.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.SpIntegralOrientation.reduction_injectivity`.
Its body is now a complete proof from the named shifted-sheaf-model statement.
The naturality and finite-evaluation identities and the private helper
`shifted_single_hom_ext` are proved in Lean.

Added holes: 1, exactly
`AlgebraicGeometry.ProEtale.SpIntegralOrientation.shifted_sheaf_models`
(node `lem-pur-integral-orientation-shifted-sheaf-models`). Its proof is exactly
`:= by sorry`, with the source and full proof in words in the docstring and node.
There are zero local holes in the item module, one in the new dependency module.
This is a decomposition (one upper hole closed, one strictly smaller geometric
step added), not a net proof of the original geometric theorem without sorry.

## No longer needed

Removed these redundant direct imports, still available through the public import
of `Sheaf.Paper.IntegralAdjunctionBijection`:

- `Sheaf.Paper.PurityFiniteSetting`
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `WeilConjectures.Compactification.RefinementCategory`
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`

Removed the unused direct dependency anchor `Sheaf.Paper.FiniteTorAmplitudeSites`.
No library module is withdrawn or asserted globally unreachable.

`lem-sp-twisted-pullback-reduction-tower`, `def-coefficient-twists-detailed`,
and `det-sp-tower-gamma` are no longer direct proof dependencies of the item:
their geometric application is isolated in the new shifted-sheaf-model node.
They remain necessary there and are not pruned. The argument retains
`det-sp-integral-adjunction-bijection`, `det-sp-coefficient-towers-abelian`,
`def-weil-triangulated-category`, `lem-weil-pbc-derived-single-fully-faithful`,
and `sk-def-sp-coefficient-towers`.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The existing proof plan is correct
but its Step 1 requires substantial coordinate glue: integral unit pullback,
completed tensor unitors, the simultaneous reduction comparison, and the ordered
Tate-line presentation must be reconciled before the objects have shifted-sheaf
models. The new lemma isolates exactly that step. Merely joint conservativity
of exact evaluations on arbitrary derived objects would not imply faithfulness;
the implemented helper instead uses full faithfulness on shifted degree-zero
objects. The original node's unit record has no realized statement/step on this
node; its route is preserved.

## New nodes

`lem-pur-integral-orientation-shifted-sheaf-models`, in
`dag/nodes/sec-poincare-duality/`, states the shifted sheaf presentations of the
reduced integral Tate line and exceptional image of the unit. The node records
actual LeanFinder, Loogle, grep and LeanSearch searches, the original Step 1's
sources, edge cases d=0 and empty X, and the matching Lean signature. No change
record is required because no existing signature or definition changed.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
