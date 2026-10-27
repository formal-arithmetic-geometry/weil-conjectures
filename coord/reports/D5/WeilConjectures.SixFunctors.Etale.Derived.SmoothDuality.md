## What changed

Filled AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor with a complete
Lean proof from the existing etale and affine-line declarations. Five proved private
helpers identify the actual ambient/upstream tensor maps, prove compactification
transport, recover the etale interface and the affine-line interface, and establish
rank-one Tate-line stalks from the published local trivializations. The existing
SmoothDuality.AffineSpace theorem supplies coordinate induction and chart descent.
The original source signatures, public imports and existing theorem remain unchanged.

Removed the unused private EtaleFiniteTwistPullback import from the unclaimed
SfAffineLineCanonicalDuality module to break its path back to this item. See
coord/changes/D5-smooth-duality-affine-line-proof-import.md. Both modules compile.
The final delivery tool performs the compiler and axiom probes independently.

## Proved and sorry left

Closed 1 of 1 original item holes:
AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor
(node lem-sf-smooth-dualizing-complex-invertible).
Added 0 holes; split off 0 statements; no new definitions or public declarations.
The second existing theorem remains proved unchanged.

The additional delivered module retains its existing hole
AlgebraicGeometry.Etale.sfAffineLineCanonicalDuality
(node lem-sf-affine-line-canonical-duality); it is neither added nor moved.
The proof also uses the existing sfEtaleUnitTensorArbitraryBase obligation.
Thus this closes the assigned upper hole from declared inputs, not a claim that
its full transitive axiom closure is already sorry-free.

## No longer needed

Removed private import Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback from
Sheaf.AlgebraicGeometry.SfAffineLineCanonicalDuality: its current declaration and
proof do not use it, and its transitive smooth-purity import creates a cycle.
This does not withdraw its mathematical statement or erase the affine-line node's
future need for roots-of-unity pullback; an acyclic lower-level API is needed there.

The new proof does not import these originally planned dependency modules:
Sheaf.AlgebraicGeometry.SfExceptionalTensorTransitivity,
Sheaf.AlgebraicGeometry.ShiftedEtaleLinesLocality,
Sheaf.AlgebraicGeometry.EtaleLocalNormalForm,
WeilConjectures.Compactification.NagataCompactification.
The already proved upstream Local/Charts/AffineSpace modules provide the required
composition, fixed-universe descent and normal-form route. Consequently the
additional inverse-shape and arbitrary-universe cohomology-witness declarations
of ShiftedEtaleLinesLocality are not needed here. Its node remains a dependency for
the upstream line-shape operations that its lean.note explicitly records.

Removed proof dependencies lem-sf-exceptional-tensor-transitivity,
thm-nagata-compactification and lem-weil-pbc-lfp-affine-opens-finite-presentation.
The supplied-adjoint transitivity package is replaced by already proved upstream
canonical-map composition. General Nagata and the affine finite-presentation
argument are replaced by the proved quasi-affine compactification construction
prop-nagata-affine-compactification. No modules or declarations are withdrawn.
The redundant explicit LowerShriekProjectionExchange proof import was also removed;
SmoothDuality.AffineSpace already publicly exposes the comparison lemma it uses.

## Where the brief, the DAG or earlier work was wrong

The DAG described an existing affine-space induction and chart-descent proof as
work to repeat. Reusing it leaves only the two genuine canonical etale/affine-line
inputs and concrete interface glue. The finite-twist theorem exposes rank-one
local bases rather than a direct geometric-stalk conclusion; the latter is now
proved by lifting separably closed points to its cover and transporting its basis.
No hypothesis was strengthened and no conclusion changed. Empty schemes, arbitrary
bases, zero coefficient ring and unbounded complexes remain covered.

The original affine-line private proof import introduced a reverse dependency
through smooth purity. Removing it compiles and leaves its public surface intact.
The updated item node records the actual route, preserving its unit's smooth case.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
