## What changed

Retained and repaired the earlier sandbox proofs in
`Sheaf.Paper.IntrinsicCompletionCompleted`. Proved additivity of the constant-extension
functor using `CompletedConstantReduction.constant_additive` and the existing scalar
extension additivity instance. Proved transition compatibility by naturality of Clifford
contraction under the diagonal generator map. Constructed the uniquely specified unit
from its compatible global section, using the ordinary tensor-unit naturality and
constant sheafification naturality. Proved the degree-zero unit is closed by the
extension-by-zero differential lemma. Proved tensor-unit compatibility by expanding
the two total differentials, killing the second by closedness and using right-unitor
naturality for the first. All existing public signatures and definitions
are preserved. Added one proof-only import of
`Sheaf.Paper.CompletedConstantSheafReduction`.

## Proved and sorry left

Closed 5 of the original 7 holes, with no new holes:

- `AlgebraicGeometry.Scheme.completedKoszulConstant_additive`.
- `AlgebraicGeometry.Scheme.completedKoszulTransition_comm`.
- `AlgebraicGeometry.Scheme.completedKoszulOne_exists`.
- `AlgebraicGeometry.Scheme.completedKoszulSheafUnitZero_closed`.
- `AlgebraicGeometry.Scheme.completedKoszulTensorUnitComponent_comm`.

The following 2 original holes remain, all attached to
`def-weil-pbc-intrinsic-completion`, with their original proof sketches:

- `AlgebraicGeometry.Scheme.completedKoszulLift_relation`: the exterior degree-zero
  transition is the identity; check compatibility of the units and then use product
  extensionality to show the product unit kills one minus shift.
- `AlgebraicGeometry.Scheme.completedIntrinsicCompletion_descends`: construct the
  natural fiber endofunctor, use finite-free Koszul K-flatness and exact countable
  products to show it preserves quasi-isomorphisms, and descend the functor and unit
  through the derived localization universal property.

## No longer needed

None at this checkpoint. No dependency node is withdrawn. The countable-product and
localization imports remain relevant to the original descent obligation.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox proof of `completedKoszulOne_exists` used `rfl` for naturality,
but the scalar-extension object is transported from its specification and its section
map is not definitionally natural. Replaced that step with the naturality of the
uniquely specified ordinary tensor unit and of `toSheafify`.
The sandbox initially had no report. No mathematical statement is corrected and no
new statement or node is introduced. The empty generator tuple and the empty scheme
are not excluded by any argument.

The final module compiles through `lcompile.py` without errors or warnings. A prior
dry run received no compile-server answer within its timeout; the separate single-file
compile subsequently succeeded. No global build was run by this worker.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
