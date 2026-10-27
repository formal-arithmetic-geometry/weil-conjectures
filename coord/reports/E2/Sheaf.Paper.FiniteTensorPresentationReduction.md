## What changed

Reduced `WeilConjectures.PurityFiniteSetting.finiteTensorStructuralCoherence` to its
native symmetry and simultaneous-shift assertions. The original theorem combines
them by conjunction introduction, with its statement unchanged. Added one new public
sorry theorem and node for each assertion, in separate modules
`Sheaf.Paper.FiniteTensorSymmetryCoherence` and `Sheaf.Paper.FiniteTensorShiftCoherence`.
Their docstrings give the homogeneous tensor calculations and localization arguments.
Both are strict parts of the original statement, not renamed copies of it.

The parent node retains the remaining proof plan and records the conjunction
assembly. No public definition or existing statement changes.

## Proved and sorry left

Decomposition: one existing hole closed and two new holes added, net minus one.
The proof of `WeilConjectures.PurityFiniteSetting.finiteTensorStructuralCoherence`
from the two stated components is complete.

Five original holes remain, on `lem-pur-finite-tensor-presentation-reduction`:

- `WeilConjectures.PurityFiniteSetting.finiteTensorTwistAdditionCoherence`
- `WeilConjectures.PurityFiniteSetting.finiteTensorPullbackCoherence`
- `WeilConjectures.PurityFiniteSetting.finiteTensorPositiveReduction_chart`
- `WeilConjectures.PurityFiniteSetting.finiteTensorTau_reduction`
- `WeilConjectures.PurityFiniteSetting.finite_tensor_presentation_reduction`

Two new holes are split off:

- `WeilConjectures.PurityFiniteSetting.finiteTensorSymmetryCoherence`, on
  `lem-pur-finite-tensor-symmetry-coherence`.
- `WeilConjectures.PurityFiniteSetting.finiteTensorShiftCoherence`, on
  `lem-pur-finite-tensor-shift-coherence`.

There are seven holes in the delivered Lean files, versus six in the original item.
No axiom or sorry inside a definition is added. The component formulas include
zero and negative shifts, the empty scheme, equal levels and nonflat quotients;
the same cochain sign calculations apply in each case.

## No longer needed

Removed these unused proof imports from the item:

- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.ScalarExtensionDualLocalIso`
- `Sheaf.Paper.ScalarExtensionDualEvaluation`
- `Sheaf.Paper.ScalarExtensionBinaryCoherence`
- `Sheaf.Algebra.Homology.DerivedScalarExtensionCounitShift`
- `Sheaf.Paper.CochainPullbackTensorShift`
- `Sheaf.Algebra.Homology.DerivedTensorShiftDescent`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Paper.FiniteReductionChartCalculus`

The new modules publicly import only the interfaces their statements need.

No existing node or module is pruned or withdrawn. The five remaining original
assertions retain their existing dependencies and proof plans. The split assertions
use precisely the symmetry and shift parts of that plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. An attempted reduction of the Tau
assertion by abstract categorical pasting elaborated, but its specialization caused
expensive kernel conversion through the native localized shift construction and
exceeded the fixed compile limit. That exploratory reduction is not delivered.
The delivered decomposition instead separates Steps 2 and 6, without changing any
definition, increasing a limit, or splitting a file to avoid a timeout.

## New nodes

`lem-pur-finite-tensor-symmetry-coherence`: scalar reduction commutes with the
native signed derived braiding, from parent Step 2 and Stacks 07A4/0FPT. Its new
module is `Sheaf.Paper.FiniteTensorSymmetryCoherence`.

`lem-pur-finite-tensor-shift-coherence`: scalar reduction commutes with the native
simultaneous integer tensor shift, from parent Step 6 and Stacks 07A4/0FNH. Its new
module is `Sheaf.Paper.FiniteTensorShiftCoherence`.

Each node has its Lean statement, dependency list, proof steps and three actual
Mathlib searches. The unit route is preserved. No change record is needed because
no existing statement, definition or public import was changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
