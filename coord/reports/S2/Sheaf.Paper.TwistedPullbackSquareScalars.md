## What changed

Filled the proof of
`WeilConjectures.TwistedPullbackScalars.twistedPullbackSquareScalars` without changing
its statement or any public definition. Constructed every field of `Geometry` from
the given finite-type and Cartesian-square hypotheses. Added a proved private
pasting lemma: the two intermediate equations and the middle equation (M) follow
from primitive (Z), (C) and the naturality of q and z. Added a proved private
isomorphism-invariance argument for the actual uniform finite-Tor predicate.
The existing framework/PBC bridge identifies the two ordinary scalar models;
transporting the existing `AdicOperationSource.scalar_preserves` result along
that identification supplies both required `ScalarClosed` conclusions.

Added three proof-only imports for the three substeps below, plus proof-only
imports of `AdicOperationDomainsSourceComparison`,
`FrameworkPbcPullbackScalarBridge`, and `SfIntegralConstructibleTriangulated`.
All original public imports remain unchanged. No other existing module is adapted.
The node proof now records this assembly and the explicit pasting calculation.

Validation: all three new statement modules compiled on the project server.
The completed item proof compiled successfully in 54.2 seconds with profiling
enabled; development profiling options were then removed for delivery.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.TwistedPullbackScalars.twistedPullbackSquareScalars`
(node `lem-pur-twisted-pullback-square-scalars`). Its proof is complete relative
to three strictly smaller statements. This is a decomposition, not a net proof
of the full package: 1 hole closed, 3 holes added, net -2.

The item module contains zero `sorry`. The delivery leaves exactly these holes:

- `WeilConjectures.TwistedPullbackScalars.twistedPullbackScalarPrimitives`, node
  `lem-pur-twisted-pullback-scalar-primitives`: (Z), (C), and naturality only;
  no composite equations or coherence/coordinate/adic conclusions.
- `WeilConjectures.TwistedPullbackScalars.twistedPullbackCoefficientCoherence`, node
  `lem-pur-twisted-pullback-coefficient-coherence`: common normalized coordinates
  and unit/tower/shift laws only; no scalar-square or adic equations.
- `WeilConjectures.TwistedPullbackScalars.twistedPullbackAdicIdentification`, node
  `lem-pur-twisted-pullback-adic-identification`: the one-arrow identification,
  with scalar closure already supplied; no square or coefficient-coherence laws.

Each is a public theorem with whole proof `:= by sorry`, its source and complete
natural-language argument in its docstring, and its own new module and DAG node.
None repeats the original theorem, and the real Lean pasting argument proves
three of its five scalar-square equations rather than moving those equations.

Edge cases: no positive-dimension, strict-field-inclusion, nonempty-scheme or
nonzero-object assumption was added. The primitive and coefficient statements
include d=0 and equal fields; all shifts are integer shifts. Arbitrary maps u,v
and even a merely commutative square are allowed in the algebraic substeps.
The geometric argument alone uses the Cartesian hypothesis to supply the
asserted properties of f'. No exceptional inverse-image or exchange theorem
is used in the square pasting or one-arrow identification.

## No longer needed

No module is withdrawn or pruned; no import is removed. The original dependency
lemmas remain needed by the three named substeps, rather than being imported
without use into the assembly module. The original direct proof-dependency list
has been replaced by the actual assembly dependencies. In particular the
roots/line, whole-system tensor, normalized-realization, localization and
cochain-shift calculations now belong to the corresponding new nodes.

Removed obsolete top-level `tool_uses` entries from the parent node for
`lem-pur-integral-operations-preserve-constructible`,
`lem-pur-twist-sheaf-locally-free`, `prop-weil-pbc-scalar-extension`,
`det-prop-sfb-cartesian-coefficients-twists`,
`lem-pur-scalar-extension-tower-coherence`,
`lem-pur-normalized-scalar-comparison-realization`,
`lem-pur-derived-pullback-tensor-iso`,
`lem-weil-pbc-cochain-pullback-tensor-shift`,
`lem-weil-completed-scalar-chain-shift`, and
`lem-pur-adic-purity-scalar-naturality`: their calculations are retained in the
new nodes. This removes no mathematical prerequisite or unit-route step.

## Where the brief, the DAG or earlier work was wrong

The DAG's generic declarations do not directly provide the new comparison
records used by the current statement. The normalized tensor-to-termwise beta,
PBC coordinates, primitive equations and their exact shift normalizations need
substantial interface glue. That glue is isolated in three genuine parts of
the argument. The original proof's elementary pasting steps are implemented
explicitly in Lean.

`AdicOperationSource.scalar_preserves` uses `completedDerivedScalarExtension`,
whereas `ScalarClosed` uses `integralOrdinaryDerivedScalar`. They are not
definitionally equal. The existing bridge supplies the required ordinary-model
isomorphism; finite-Tor membership is transported along it. No functor was
silently identified, redefined or chosen from mere existence.

The node for `lem-pur-normalized-scalar-comparison-realization` records
`Sheaf.Paper.NormalizedScalarComparisonRealization`, but that file is absent
from the supplied source snapshot, and no matching rework row was found. It
remains a prerequisite recorded in the appropriate substeps; no duplicate or
replacement declaration was introduced.

The latest blueprint uses `sk-thm-purity-transport-coefficient-change.proof.md`
for the coefficient-change proof, rather than the old filename cited by the
parent node. The new records cite the current file and the parent's expanded
ordinary-operation calculation. The unit route is preserved.

## New nodes

`lem-pur-twisted-pullback-scalar-primitives` is stated in
`lean/Sheaf/Paper/TwistedPullbackScalarPrimitives.lean`. It isolates the genuine
whole-system tensor/line square and compositor-cancellation calculation.

`lem-pur-twisted-pullback-coefficient-coherence` is stated in
`lean/Sheaf/Paper/TwistedPullbackCoefficientCoherence.lean`. It isolates the
simultaneous normalized coordinates and coefficient/shift laws, for arbitrary
commutative squares on the required domains.

`lem-pur-twisted-pullback-adic-identification` is stated in
`lean/Sheaf/Paper/TwistedPullbackAdicIdentification.lean`. It isolates the
identification of the very same integralA with the recorded ordinary adic
sourceScalarComponent after the actual chi and shifted-beta maps.

All three inherit the parent's chapter and unit, retain the relevant original
proof dependencies, and record LeanSearch, Loogle/LeanFinder and local grep
searches. No existing public signature or definition changes, so no change
record or consumer adaptation is required.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
