## What changed

Restored the quarantined item from its recorded archive, retaining its public import,
Lean attachment, and theorem signature. Replaced its hole by a factorization through
the tensor unit: gamma equals zeroSourceMap followed by finiteSmoothGammaMap for
alpha followed by zeroLineIso. Functoriality cancels the two mapped line coordinates
and the two right-unit constraints. The orientation and tensor normalization lemmas
then identify the latter map with the inverse adjoint comparison, which cancels.

Added two smaller statement modules, each with a node and a complete proof in words.
The geometric lemma identifies only the coefficient-unit orientation, without a
variable complex or tensor map. The equality hd is retained explicitly, avoiding
dependent substitution across the geometric data. The tensor lemma concerns only the fixed adjoint
unit orientation, without supplied geometry, specialization, or alpha. They apply
to arbitrary finite coefficient rings directly; no transport between the single
and double universe lifts is required in the combining proof.

## Proved and sorry left

This is a decomposition, not a completed geometric normalization proof.
One original hole is closed in
AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothIntrinsicLevelProperties
(node lem-pur-finite-smooth-intrinsic-level-properties). Two holes are added:

- AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothZeroOrientationCoordinates
  (lem-pur-finite-smooth-zero-orientation-coordinates).
- AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothOmegaTensorCoordinates
  (lem-pur-finite-smooth-omega-tensor-coordinates).

The item itself has zero sorrys. No definitions or existing dependency modules are
changed. The packet closes one hole and adds two, so its net closure count is minus one.

The combining proof compiles in 5.3 seconds. A private categorical helper proves
the cancellation before specialization to derived categories, avoiding expensive
unfolding of geometric definitions. Delivery preflight checks the complete packet.

## No longer needed

No original import is removed and no module is withdrawn or pruned. The tensor-step
module imports only FiniteSmoothGammaNormalization; it needs no adjunction-data
or pro-etale purity definitions.
The item node no longer directly cites lem-pur-finite-smooth-gamma-normalization,
lem-pur-noetherian-etale-section-specialization,
lem-trf-finite-ring-section-deformation, or def-amb-vector-integration; it cites
the two new partial statements. The finite-ring deformation and vector integration
remain needed by the geometric step. The single-lift gamma theorem is not used as
a theorem by this proof route, and the Noetherian prime-power specialization
statement is superseded for this argument by its finite-ring counterpart. Their
modules remain transitively imported for existing definitions and other consumers;
this packet does not claim to prune those modules or their descendants.

## Where the brief, the DAG or earlier work was wrong

The item was absent from lean at the start because it was quarantined, as recorded in rework.tsv.
Its absence does not mean that its mathematical obligation or parent use disappeared.
The baseline restored source compiled successfully through lcompile.py.

The original plan requires transporting the single-lift gamma theorem to a double
lift, but no such transport declaration is supplied by that theorem. Moreover its
constructed alpha is not the arbitrary supplied OrientationNormalized alpha.
The two new steps isolate the geometric identification and the independent tensor
normalization precisely. The generic finite-coefficient formulations follow the
latest blueprint's instruction to perform the calculation over A throughout.

For the tensor node, lem-sf-etale-unit-tensor-arbitrary-base is requested as a tool
from another unit: its already-proved statement supplies the normalized tensor
identity for arbitrary finite A. No tool_uses approval field is changed here.
The geometric edge cases N=1 (hence the zero coefficient ring), empty X or Y,
and rank-zero conormal are retained. The tensor step requires no choice of a
geometric orientation and works on all unbounded complexes.

## New nodes

lem-pur-finite-smooth-zero-orientation-coordinates records the rank-zero
coefficient-unit orientation equality from the first three factors of the latest
orientation proof and finite-ring specialization uniqueness. Its proof contains
no claim about gamma on variable complexes.

lem-pur-finite-smooth-omega-tensor-coordinates records only the tensor/projection
normalization at the graph-normalized coefficient unit. Its proof uses graph
normalization uniqueness and the arbitrary-base etale unit/tensor theorem, followed
by adjunction comparison cancellation. No definition or statement repair, change
record, or forced adaptation is needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
