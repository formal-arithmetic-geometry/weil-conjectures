## What changed

The original `derivedScalarMateThickLocus` statement is unchanged. Its proof now assembles
projection normalization and canonical exact structures with already-proved categorical APIs.
It proves the geometric mate-counit identity using `mateEquiv_counit`, constructs the required
morphism of triangles using `NatTrans.mapTriangle`, identifies the locus with the restricted
transformation's `isoLocus` using restriction conservativity, transfers triangulated and retract
closure, and derives finite biproduct closure from the biproduct limiting fan. A proved private
helper verifies both identities for the specified inverse on a split retract.

Two strictly smaller geometric steps are separately stated: the normalized projection equality
and the canonical exact/shift structures. Neither includes thick closure, finite sums, retract
closure or its explicit inverse, and neither is the item under a different name. Their source
proofs are in their docstrings and nodes. The unit's direct-image route is retained.

The auxiliary declarations formerly preceding the main theorem are moved together to
`Sheaf.Paper.DerivedScalarMateData` to avoid a cycle: the geometric lemmas need the existing
normalized definitions and the item needs to import these lemmas. The item publicly reexports
all their existing names. Every public signature and non-theorem body is unchanged. The
previous ordinary comparison proof is retained. The original derived-tensor normalization hole
is relocated without claiming to prove it. The attachment now names its own extracted node.

Change record: `coord/changes/H6-derived-scalar-mate-data.md`.

Validation: all four delivered Lean modules compiled together successfully with the remote
compile wrapper. Times were 55.2 s (data), 7.6 s (exact structures), 6.8 s (projection
normalization) and 9.1 s (item), each below 60 s. The initial item run emitted style suggestions
for local instance bindings; the suggested ordinary local bindings replace them
before final delivery. No profiling options remain in the delivery.

All four direct importers compiled against the changed item without compiler errors:
`CompletedScalarMateCoefficientTransport` (14.9 s),
`CompletedTensorProjectionCoefficientTransport` (11.3 s),
`GeometricGeneratorProjectionDevissage` (initially 69.8 s), and
`ProEtaleScalarMateIdentifications` (22.3 s). The one slow initial run was investigated
with temporary profiling: the same devissage consumer took 6.1 s against the packet
and 5.6 s against the published item; no declaration took more than 1.3 s. These
comparison runs found no slow declaration or compatibility change requiring an
adaptation. All temporary consumer copies and profiling options were removed.

## Proved and sorry left

Of the two original holes, the main theorem
`AlgebraicGeometry.Scheme.DerivedScalarMate.derivedScalarMateThickLocus` is closed by a
complete assembly proof with two new geometric holes. This is a decomposition, not a net proof
of the geometric comparison. The existing auxiliary hole is moved with the same declaration
name. The packet has three holes in total: one retained/moved, two added; net hole change +1.

Every remaining hole:

- `AlgebraicGeometry.Scheme.DerivedScalarMate.derivedTensorIso_existsUnique`, in
  `Sheaf.Paper.DerivedScalarMateData`, attached to
  `lem-sfb-derived-scalar-tensor-identification`: original hole, unchanged.
- `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_projection_normalization`, in
  `Sheaf.Paper.DerivedScalarMateProjectionNormalization`, attached to
  `lem-sfb-derived-scalar-projection-normalization`: new, original DAG steps 2--3.
- `AlgebraicGeometry.Scheme.DerivedScalarMate.scalarMate_canonical_exact_structures`, in
  `Sheaf.Paper.DerivedScalarMateExactStructures`, attached to
  `lem-sfb-derived-scalar-canonical-exact-structures`: new, original DAG steps 4--5 up to
  the shift equation. The triangle-morphism construction itself is proved in the item.

The private `retract_inverse` helper is completely proved. The ordinary tensor comparison
was already proved before this packet and is not counted as newly proved.

## No longer needed

No mathematical module or dependency is withdrawn. The original geometric dependencies are
retained through the smaller steps that actually use them. No node below a still-needed
statement is asserted to be pruned. All original public imports remain available through the
public data-module reexport. The two ordinary-comparison proof imports are relocated with that
proof. The main module now directly imports only the shared data, its two geometric proof
steps, and the source-library triangulated-generators API. Its original separate closure
calculations are supplied by the already-proved `isoLocus` instances, finite-product closure
and `NatTrans.mapTriangle`; no new categorical closure hole is added.

The following obsolete *direct* tool-use approvals are removed from the principal node,
with the same underlying dependencies retained on the extracted step that uses them:

- `lem-pur-derived-change-of-rings`.
- `lem-weil-pbc-ringed-projection-mate-exact`.
- `lem-weil-pbc-site-derived-tensor-descent`.
- `lem-sfb-kflat-scalar-comparison-normalization`.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
- `lem-sfb-ringed-projection-first-shift`.
- `lem-weil-pbc-adjunction-shift-compatibility-unique`.
- `lem-pur-derived-tensor-additive-constraints`.

The new nodes' `split_report.tool_uses` request the inherited generic-tool uses for their
respective argument steps; no new top-level maintainer approval is written by this packet.

## Where the brief, the DAG or earlier work was wrong

The original mathematical plan is retained. It did not take advantage of the already-proved
source-library `NatTrans.isoLocus` and `NatTrans.mapTriangle` APIs, which supply the categorical
closure and all three triangle squares. Extracting the existing data is necessary only to keep
the smaller geometric statements in separate modules without an import cycle.

Edge cases checked mathematically: zero rings, the zero complex and empty finite sums require
no extra assumption; the finite-product argument covers `Fin 0`. The retract argument uses an
actual splitting and does not assume idempotent completeness. Nonflat B is handled by first
resolving the input and then tensoring the coefficient resolution with that K-flat input.
An arbitrary beta need not commute with shifts merely because its functors are exact: the
new exact-structure statement explicitly retains compatibility of this prescribed beta.

## New nodes

`lem-sfb-derived-scalar-tensor-identification` owns the relocated normalized scalar tensor data
and the unchanged auxiliary existence/uniqueness theorem. This extracts original DAG step 1;
it is not an added hole or a proof of the old one. Its Lean file is
`Sheaf.Paper.DerivedScalarMateData`.

`lem-sfb-derived-scalar-projection-normalization` states exactly the representative-balancing
and adjunction calculation of original steps 2--3. It is the equality with the specified
projection arrow; it asserts no invertibility or closure property. Its Lean file is
`Sheaf.Paper.DerivedScalarMateProjectionNormalization`.

`lem-sfb-derived-scalar-canonical-exact-structures` retains the canonical tensor normalization,
compatible geometric adjunction shift, transported source/target shifts, exactness and the
restricted beta shift equation of original steps 4--5. It asserts no thickness and does not
include the triangle-morphism construction proved in the item. Its Lean file is
`Sheaf.Paper.DerivedScalarMateExactStructures`.

All three nodes inherit the parent chapter/unit and blueprint ancestry. Searches used
LeanSearch, LeanFinder and Mathlib/project grep; no existing general normalized comparison
was found beyond the parent and its constant/condensed specializations. Sources are Stacks
03EK, 03EL, 06YY, 07A4, 07A6, 0A8D and 0FPT, with the added normalization calculations
honestly marked as agent-written expansions of the original plan.

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
