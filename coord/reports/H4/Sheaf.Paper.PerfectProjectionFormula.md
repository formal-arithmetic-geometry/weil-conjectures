## What changed

Proved `AlgebraicGeometry.Scheme.PerfectProjection.ordinaryUnit_coherence` in
`Sheaf.Paper.PerfectProjectionFormula`. The proof reduces equality of sheaf tensor
maps to pure tensors using the sheafification adjunction, computes the tensor
unitor on those tensors, and applies the normalization of the chosen ordinary
pullback unit. Every private helper is proved.

Constructed `ordinaryRightUnit` explicitly through tensor sheafification,
the presheaf unitor and the sheafification counit. The proved public theorem
`ordinaryRightUnit_eq` identifies it with the original monoidal unitor.
`ordinaryTensorHom` receives a definitionally equal explicit result type.
`Resolution.totalInverse` uses the unitor equality to supply its original
coherence premise; its chain map is unchanged by proof irrelevance.
Only this item uses these declarations; no consumer adaptation is needed.
The change records are `coord/changes/perfect-projection-ordinaryRightUnit.md`
and `coord/changes/perfect-projection-ordinaryTensorHom.md`.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.Scheme.PerfectProjection.ordinaryUnit_coherence`.
Added zero holes and split off zero statements.

Three original sorries remain, all attached to
`lemma-weil-pbc-perfect-projection-formula`:

- `AlgebraicGeometry.Scheme.PerfectProjection.perfect_projection_formula`
- `AlgebraicGeometry.Scheme.PerfectProjection.totalization_compatibility`
- `AlgebraicGeometry.Scheme.PerfectProjection.baseChange_compatibility`

Actual hole count in the delivered Lean file: three. The complete proof compiled
in 35.7 seconds against the shared library after constructing the unitor explicitly
and proving its equality to the monoidal unitor. The delivery tool performs the
final compile, axiom checks and preflight. No experimental dependency artifacts
are used.

## No longer needed

No whole node or blueprint unit is pruned. The three remaining obligations still
follow the recorded route. The existing planned proof imports remain available.
The unit proof adds `import all Sheaf.Algebra.Homology.KFlatResolutionGeneral`
for its existing sheafification tensor-naturality lemma.

The experimental forward-totalization helper and tensor API changes were not
retained. They are not imported or delivered, and no new node remains in the
packet. The unit proof does not depend on cached experimental modules.

## Where the brief, the DAG or earlier work was wrong

The earlier report claimed a pending totalization decomposition. That is withdrawn
from this packet: its fully expanded forward calculation did not pass the file
limit, and it is not replaced by a new sorry to avoid that limit. Only the proved
ordinary-unit result is submitted. The remaining three original statements keep
their signatures and sorries.

The resumed dispatcher reference clock was reset while the original session
continued; no budget metadata was edited. Earlier provider and compile-server
interruptions caused no push, and no interrupted delivery was repeated.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
