## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartMonoidalPresentation`
without changing its statement. Added private constant-function and local-bijection helpers,
and proved that the actual `integralModelFixedScalars` is an equivalence by the invertible
associated-module-sheaf unit. This proves equivalence of the specified intrinsic realization.
Constructed the required H by composing the inverse intrinsic equivalence with the existing
monoidal continuous-to-coefficient-model encoding. The equivalence unit cancels the intrinsic
realization from the required composite. Transport of monoidal structure completes the proof.
The imports of the intrinsic comparison and finite comparison presentation use `import all`
to reuse their proved private helpers. Updated the node proof to this route.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteHeartMonoidalPresentation`.
No holes added; no `sorry` remains in the delivered module. All private helpers are proved.
This is a proof from existing declarations, not a decomposition.

## No longer needed

No original public imports removed: all three support the unchanged statement.
No original dependency is withdrawn. The section tensor and coefficient model comparisons
are used through the existing finite comparison monoidality proofs. Their general generic
proofs avoid repeating a new local-pure-tensor construction for this particular composite.
No module is withdrawn and no new node is introduced.

## Where the brief, the DAG or earlier work was wrong

The existential statement does not prescribe H or a normalization on its tensor comparison.
It permits H to be constructed by cancellation of the actual intrinsic realization against
an existing monoidal equivalence. Thus the second DAG step need not repeat all scalar and
site comparisons on the literal finiteHeartRealization composite. The first step still
requires proving equivalence of the actual fixed-scalar restriction; the proof does this
from the canonical constant-function map and the sheafification adjunction unit.
Empty schemes use the empty covering in local injectivity. The zero ring and disconnected
schemes require no extra assumption; the same fibre-cover argument applies.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
