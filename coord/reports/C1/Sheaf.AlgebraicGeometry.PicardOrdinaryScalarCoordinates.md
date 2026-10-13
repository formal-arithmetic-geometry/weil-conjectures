## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.picard_ordinary_scalar_coordinates`
by a reduction to the new raw-coordinate calculation
`AlgebraicGeometry.Scheme.picard_ordinary_raw_coordinates` in
`Sheaf.AlgebraicGeometry.PicardOrdinaryRawCoordinates`. All existing signatures and
visibility are unchanged. The target now constructs the open cycle by the inverse
of its additive coordinate equivalence, proves both cycle assertions by injectivity
of degree-one coordinates and the differential formulas, and uses residue
naturality to prove the required evaluated coordinate.

The new theorem is a coordinate diagram calculation for raw morphisms in both
degrees. It omits `hdw`, assumes no scalar annihilation, and asserts no cycle
membership or existence. Its docstring gives the affine basis, tensor-unit and
restriction calculation. The target proof supplies the vanishing argument and
constructs the cycle; this is a decomposition, not a proof without remaining holes.
The plan and proof dependencies of the original node now describe this reduction.
Both modules compiled locally without errors or warnings. The delivery dry run
passed compilation and preflight, with no push; the second reading remains for
the next worker.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.Scheme.picard_ordinary_scalar_coordinates`
(node `lem-sc-picard-ordinary-scalar-coordinates`).

Added one hole:
`AlgebraicGeometry.Scheme.picard_ordinary_raw_coordinates`
(node `lem-sc-picard-ordinary-raw-coordinates`), whose whole proof is `by sorry`.
There are no other holes in the delivered modules. Holes closed: 1; holes added: 1;
net: 0. This is a decomposition of the scalar-cycle result into the raw-coordinate
calculation and a complete Lean proof of the cycle construction.

Edge cases checked in the mathematical argument: for `m = 0` the degree-one
coordinate vector and sheaf are zero, and the differential formulas still hold;
nonaffine `V` is allowed because the bases are sheaf bases restricted from affine
`U`; zero coefficients impose no restriction on scalars. No data definition or
choice of an arbitrary witness from an unproved existence theorem was added.

## No longer needed

Removed proof imports `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
and `Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf` from the original module.
These imports are retained as plain proof imports in the new raw-coordinate module,
matching its still-open proof plan. The original node now directly needs only
`lem-sc-picard-ordinary-raw-coordinates`. Its earlier affine adjunction,
tensor-unit comparison and tensor adjunction dependencies remain needed in the
new node's planned proof; none of those nodes is claimed globally pruned.
No unit statement or step was bypassed (the unit has no realized nodes here).
No globally pruned nodes or modules.

## Where the brief, the DAG or earlier work was wrong

The source check confirms that Tag 06Z0 is a derived-equivalence statement.
Its proof cites ordinary Tags 01I7 and 01IB; the new coordinate theorem cites
those directly and needs no derived affine equivalence. The original theorem
and its docstring are unchanged. A blueprint search for scalar coordinates
found no existing blueprint node, and local declaration searches found no
existing theorem for the simultaneous raw-coordinate calculation.

The earlier attempt reported that unproved or missing coordinate infrastructure
prevented a delivery. Stage 3 permits a named intermediate calculation with its
source, proof in words and DAG node. The raw differential formulas can be stated
without scalar vanishing and suffice for an actual Lean cycle construction.

The prior sandbox contained a full library snapshot. Unchanged copies were removed
from the delivery tree; unrelated stale copies and build artifacts were preserved
under `scratchpad/`. Only the item's module and the new coordinate module are
included in the delivery. No repository files were manually written.

## New nodes

`lem-sc-picard-ordinary-raw-coordinates`, in
`dag/nodes/sec-abelian-varieties/lem-sc-picard-ordinary-raw-coordinates.json`,
states the additive coordinates in degrees zero and one, differential formulas,
and residue restriction naturality, with no vanishing hypotheses. Source: Stacks
Project Tags 0BF2, 01I7, 01IB and 0096. It retains the original node's ordinary affine
and tensor comparison argument below the unit level. No change record is needed:
no existing statement, definition or public import was changed.

## Second reading by C1

1. I compared both delivered Lean modules with the repository versions. The existing
   theorem signature and all definitions are byte-for-byte unchanged; only its proof and
   proof-only imports changed. The raw-coordinate theorem is a new declaration with a
   corresponding node and module.

2. I compiled `PicardOrdinaryRawCoordinates.lean` and
   `PicardOrdinaryScalarCoordinates.lean` with `lcompile.py`; both compile without errors
   or warnings. The only remaining `sorry` is the named raw-coordinate theorem, and no
   definitions contain `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by`. The scalar theorem depends on `sorryAx` only through that explicitly
   split theorem.

3. The split-off raw-coordinate statement isolates the raw-morphism calculation:
   it gives additive coordinates, differential formulas, and restriction naturality, with
   no cycle-membership or scalar-vanishing conclusion. Its source, proof description,
   searches, and DAG node are present; local searches found no existing declaration of
   the same result. The edge cases `m = 0`, zero coefficients, and nonaffine opens are
   covered by the statement and proof description.

4. The proof follows the node route: it obtains raw coordinates, uses injectivity of the
   degree-one coordinates for both kernel arguments, constructs the open cycle by the
   inverse coordinate equivalence, and applies restriction naturality for evaluation.
   The unit route is unchanged. The scalar module has only the raw-coordinate proof import;
   the two removed imports are no longer used.

5. The raw node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof's actual
   reduction, and the scalar node now depends only on the raw node. No existing target or
   public interface was weakened. I corrected the report wording about the raw-coordinate calculation and retained
   the affine adjunction and tensor-unit modules as plain proof imports in the new
   raw-coordinate module, so that its stated proof dependencies remain available.
   No Lean statements or definitions required repair.
