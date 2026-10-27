## What changed

`WeilConjectures.PurityFiniteSetting.finiteReductionOfPurity` now has a complete
Lean proof: unfold the purity map into realized twist reassociation followed by
the tensor form of purity, map the composite through coefficient reduction, and
paste the two constituent squares by associativity. The theorem statement and
all existing definitions and public imports remain unchanged. The two added
imports are proof-only.

Added `Sheaf.Paper.FiniteReductionTensorSource`, containing concrete definitions
`WeilConjectures.PurityFiniteSetting.finiteReductionTensorInputComparison` and
`WeilConjectures.PurityFiniteSetting.finiteReductionTensorSourceComparison`.
The input comparison uses the specified scalar realization and the two intrinsic
realization counits, transported by a fully faithful functor. The tensor-source
comparison uses scalar realization, the existing fixed-scalar target comparison,
and tensoring the transported input comparison with the identity on the smaller
positive coefficient line. Neither construction uses a purity morphism, an
orientation, or data selected from an unproved existence statement.

Added the reassociation square in `Sheaf.Paper.FiniteReductionReassociation` and
the tensor-form square in `Sheaf.Paper.FiniteReductionTensorPurity`. These are
separate factors of the original three-factor argument: the first has no
exceptional inverse image, and the second has no twist reassociation. Their
statements are not the original purity square under another name. Their full
proof plans are in their docstrings and nodes. The parent DAG now records the
actual pasting and retains the unfinished unit-trace and composition plans.

Validation: the four-module sandbox compiled as a set before the last cleanup.
A final compile and the delivery checks validate the submitted versions. No
source-library declaration or target statement was changed. Edge cases checked
in the argument: m=n uses the same scalar/counit normalizations; d=0 uses the
unit line and zero shift; empty schemes introduce no root-generator requirement
at a nonexistent point. No flatness of the coefficient quotient is assumed.

## Proved and sorry left

Original holes: 4. Closed in the item module:
`WeilConjectures.PurityFiniteSetting.finiteReductionOfPurity`.
This is a decomposition into two strictly smaller constituent squares, not a
net proof of the imported mathematics: 1 original hole closed, 2 new holes added,
net -1. The proof combining those squares is complete Lean.

The three original holes left, all attached to
`thm-pur-finite-reduction-of-purity`, are:

- `WeilConjectures.PurityFiniteSetting.finiteReductionOfUnitSmoothTrace`.
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionSource`.
- `WeilConjectures.PurityFiniteSetting.finiteReductionOfCompositionExceptional`.

The two added holes are:

- `WeilConjectures.PurityFiniteSetting.finiteReduction_reassociation`, node
  `lem-pur-finite-reduction-reassociation-intrinsic`.
- `WeilConjectures.PurityFiniteSetting.finiteReduction_tensorPurity`, node
  `lem-pur-finite-reduction-tensor-purity`.

The delivery therefore contains five remaining named theorem holes. The two new
comparison definitions have zero holes. The previously completed smooth-trace,
composition-coherence, base-change and affine-orientation proofs are preserved.

## No longer needed

None. No existing import, module, declaration or unit step is removed. The old
main-proof dependencies remain needed transitively by the new constituent
lemmas, or directly by the retained pending composition clauses. In particular,
the diagonal-orientation reduction is still used for the affine-orientation
clause and the tensor-form argument. No module withdrawal is requested.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The DAG's original assembly steps suppress a
coordinate change: `finite_tensor_presentation_reduction` is stated in fixed
scalar coordinates, whereas the item uses arbitrary intrinsic K. Applying the
smaller realization to that square does not directly yield the item's source
comparison. The realization counit at K and its naturality must also be inserted.
An attempted direct simplification exhibited this precise mismatch. The new
input comparison and reassociation lemma isolate that transport rather than
silently identifying the two coordinate systems.

The tensor-form square similarly requires transporting the diagonal orientation
and adjoint-mate equations into the intrinsic presentation and identifying their
coefficient-line map with the existing positive-line reduction. That remains an
explicit proof obligation, not an extra hypothesis in the original statement.

The unit `sk-thm-purity-transport` is retained: tau, inverse orientation and theta
are still the factors of the argument. No geometric-fibre equality inference or
alternative unit route is used. The compiler restored the existing unpublished
`FiniteReductionBaseChangeSource` dependency in its private overlay; no archived
or missing shared module was deleted or replaced.

## New nodes

`def-pur-finite-reduction-tensor-source` attaches the two explicit intrinsic input
and tensor-source comparison definitions. These extend the existing fixed-scalar
comparisons to the original intrinsic input; they do not duplicate or replace
`def-pur-finite-tensor-fixed-comparisons`.

`lem-pur-finite-reduction-reassociation-intrinsic` is the realization/counit
transport of `lem-pur-finite-tensor-presentation-reduction`. Its extra content is
the source/input coordinate transport. Its conclusion concerns tau alone.

`lem-pur-finite-reduction-tensor-purity` is the other constituent square, for
(1 tensor Pi inverse) followed by theta. It uses the existing diagonal reduction
and finite-adjoint-mate compatibility instead of restating their separate
geometric constructions. It has no tau and is not the full purity reduction.

Searched Mathlib using leansearch, leanfinder, loogle and grep (queries recorded
in the node records and sandbox search log), and searched both library roots and
the DAG. Existing fixed-scalar comparisons, tensor presentation reduction,
diagonal reduction and adjoint-mate compatibility supply the constituent route;
none states these intrinsic squares with this input counit. Nearby universal
finite-free trace and adic/tower trace nodes have different coefficient functors
or inputs and do not supply either square. No change record is required because
no existing statement, definition or public interface was altered.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
