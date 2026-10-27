## What changed

Replaced the hole in `AlgebraicGeometry.topEdgeTruncatedCounit_localClass` by a proof
using naturality, normalization on single complexes in arbitrary integer degree, and
truncation. Its signature and original public import are unchanged. Added private proof
imports of `DerivedDirectImageSingleEdge`, `DerivedLocalClassEdge`, and
`RightDerivedFunctor.PlusCompatibility`.

The private `natural_edges_ext` proves that two natural edges from Hq(RK) to F(Hq K)
agree everywhere if they agree on degree-q singles, provided R preserves lower bounds.
It projects K to its lower truncation, then uses the upper-truncation triangle there.
The private `truncatedCounit_naturality` proves the required naturality directly from
upper truncation, the pinned derived adjunction, and naturality of kappa.

Added `DerivedSingleAdjunctionTranspose`, which constructs the single direct-image
comparison in every integer degree and proves the pinned adjunction transpose formula
`AlgebraicGeometry.topEdgeSingleAdjunctionTranspose`. Added `DerivedDirectImageSingleEdge`,
which proves `AlgebraicGeometry.topEdgeSingleDirectImageMap_counit`
from the pinned derived adjunction and the explicit kappa. In particular, this proof
handles tensor pullback rather than substituting an unrelated ordinary pullback
comparison, and does not assume a shift compatibility equation for this new comparison.

Added `DerivedLocalClassEdge` for the remaining, genuinely local part: constructing a
natural module edge by sheafifying the cocycle maps and computing its value on a single
complex. This statement mentions no derived pullback, derived adjunction, kappa, or
truncated counit. It carries the source and a complete proof in words. The main proof
identifies this local edge with the explicit truncated counit by the proved algebraic
normalization and uniqueness argument. No definition chooses data from the new hole.

Updated the assigned node's proof, proof dependencies and proof origin; added matching
nodes for the three new modules. No existing module other than the assigned item is edited.

The full sandbox compiled in import order with per-file times 29.6 s
(single adjunction), 48.7 s (single counit), 5.8 s (local edge), and 20.5 s
(assigned theorem), all below 60 s. The only style warning requested a reason for
the single-adjunction elaboration heartbeat allowance; that comment was added
before the delivery tool performs its final compile and preflight.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.topEdgeTruncatedCounit_localClass` (node
`lem-weil-pbc-truncated-counit-local-class`). The item's module has zero holes.

Proved the new theorem `AlgebraicGeometry.topEdgeSingleDirectImageMap_counit` (node
`lem-weil-pbc-single-truncated-counit-normalization`), with zero holes in its module.
Its supporting private lemmas are all proved. Also proved the new
`AlgebraicGeometry.topEdgeSingleAdjunctionTranspose` (node
`lem-weil-pbc-integer-single-adjunction-transpose`), with zero holes in its module.

The full single calculation initially compiled without proof errors but exceeded 60 s.
Profiling found expensive comparison type checking. Locally making the tensor-pullback
object/map and derived-functor data irreducible, making the new single-unit definition
irreducible, and replacing a convert/rfl proof by a direct exact proof did not suffice.
The self-contained termwise single-adjunction calculation was then moved to its own
module. These local attributes do not change any shared definition or exported attribute.
The new single-unit definition is intentionally irreducible and has a real construction;
its normalization is provided by the proved transpose theorem.

Added one hole, exactly the body of the public theorem
`AlgebraicGeometry.exists_topEdgeLocalClassEdge` (node
`lem-weil-pbc-local-class-edge-single-normalization`). There are no other new holes.
This is a decomposition: one original hole closed and one strictly local hole added,
net zero holes closed. The derived-algebraic normalization and the truncation argument
are proved, rather than deferred to a renamed copy of the assigned statement.

The new statements were checked mathematically for arbitrary positive, zero and negative
q, zero modules and derived objects, empty opens and schemes, and nonflat morphisms.
There is no bound on K. The arguments use left exactness of direct image, not exactness;
they require neither acyclicity of arbitrary module sheaves nor flatness of g.

## No longer needed

No original public import was removed. All three private proof imports are used.
The new local-edge module imports only the single-adjunction module; its earlier
dependency on the single-counit normalization module was removed when the calculation
was separated. It therefore does not depend on the theorem identifying the counit.
No module is withdrawn or globally pruned: dependencies still publicly imported by
`DerivedAdjunctionTopEdgeData` or used elsewhere remain in the library.

The assigned node's old arbitrary-source factorization and separate shift route are
unnecessary for this proof. Its direct proof dependencies no longer include
`lem-pc-derived-tstructure-orthogonality`,
`lem-weil-pbc-hom-out-of-triangle-exact`,
`lem-weil-pbc-hom-into-triangle-exact`,
`lem-weil-pbc-derived-single-fully-faithful`,
`lem-pc-pinned-pullback-counit-shifts`,
`lem-pc-canonical-single-adjunction-transpose`,
`lem-pc-pinned-derived-adjunction-shifts`, and
`lem-pc-ringed-spaces-derived-adjoint`.
The proof uses the existing top-cohomology Hom-bijection and a direct integer-degree
single transpose, followed by natural-edge uniqueness. The old explicit degree-zero
single comparison is replaced here by the same termwise construction in arbitrary degree;
`lem-pc-canonical-single-direct-image-comparison` is not used directly.
The local sheafification and local Leray dependencies move to the new local node;
they are still needed, not pruned. No source-library declaration is removed or changed.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The old plan is longer than necessary: factorization of an
arbitrary derived morphism and separate pinned integer-shift comparisons can be replaced
by naturality and a two-truncation uniqueness argument. All unit statements and realized
unit proof steps are retained. The new nodes are tools below that route.

## New nodes

`lem-weil-pbc-integer-single-adjunction-transpose`, in
`dag/nodes/sec-proper-base-change/`, records the constructed integer-degree single
comparison and the proved pinned single-adjunction equation. Its Lean module is
`Sheaf.AlgebraicGeometry.DerivedSingleAdjunctionTranspose`.

`lem-weil-pbc-single-truncated-counit-normalization`, in the same directory, records
the proved normalization for the explicit truncated counit. Its Lean
module is `Sheaf.AlgebraicGeometry.DerivedDirectImageSingleEdge`.

`lem-weil-pbc-local-class-edge-single-normalization`, in the same directory, records the
remaining local sheafification construction, naturality and single cocycle computation.
Its Lean module is `Sheaf.AlgebraicGeometry.DerivedLocalClassEdge`. This is the sole
split-off hole. No change record is required for another existing module: none is edited.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
