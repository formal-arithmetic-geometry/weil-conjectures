## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarTensorRepresentative_transport`
in its assigned module, with its statement unchanged. Lift the section complexes through the
termwise section equivalence and transport K-flatness and termwise flatness along the counit.
Both sides of the representative equation are components of natural transformations: the scalar
counit, signed total comparison, derived tensorator, and qTensor compose by whiskering.
Naturality along the pair of counits transports the assumed internal equation by cancellation.
The private proved helper `resolving_of_iso` supplies the isomorphism invariance;
`app_eq_of_iso` supplies the generic natural-transformation cancellation argument.
Local irreducibility annotations keep comparison data closed during elaboration.
The theorem retains its original exactness assumption; its unused-section-variable linter is
locally disabled because the transport argument only needs the supplied comparison data.
Only the assigned Lean module and its own DAG node are changed.
The proof imports `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`
for the proved natural isomorphism from the explicit site tensor to the monoidal tensor.

## Proved and sorry left

Closed the single hole in
`AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarTensorRepresentative_transport`
(node `lem-sfb-coefficient-scalar-tensor-representative-transport`).
There are zero holes left in the item and zero holes added; no statements are split off.
The completed proof compiled in 45.5 seconds; the delivery axiom probe compiled in 39.5 seconds.
The original unused exactness assumption is retained with a scoped linter option. The heartbeat
option carries its required explanation immediately after the option.

## No longer needed

The transport proof does not use
`lem-sfb-coefficient-scalar-tensor-representative-internal` or import its module
`Sheaf.Paper.CoefficientScalarTensorRepresentativeInternal`: the internal equation is already
an explicit hypothesis. The DAG proof dependency on that theorem is removed. Its independent
use by the parent representative theorem remains needed. No existing import is removed and no
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG listed the internal-image theorem as a proof dependency of the transport theorem,
although the latter takes the internal-image equation as a hypothesis. This dependency is
unnecessary. The transport itself closes by existing naturality and equivalence APIs,
without a further decomposition. The unit route is unchanged.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
