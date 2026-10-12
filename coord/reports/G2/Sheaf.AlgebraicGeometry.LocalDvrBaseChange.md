## What changed

Closed `AlgebraicGeometry.Scheme.local_dvr_base_change` with a complete compiling
reduction to preservation of irreducibles by the scalar-extension stalk map.
Constructed the point above P using the existing rational-point base-change construction;
proved existence, uniqueness and closedness from PointCount and DensePoints.
Used the proved regularity, connected-integrality and smooth-relative-dimension APIs
for the integral, Noetherian and DVR conclusions on both schemes. Proved stalk-map
injectivity by flatness and faithful flatness. Constructed the function-field map by
`IsFractionRing.lift`, with its required compatibility from `lift_algebraMap`.

The proved private helper `AlgebraicGeometry.ord_eq_of_stalk_uniformizer` works for any
pair of integral locally Noetherian schemes with DVR stalks and an irreducible-preserving
stalk map. It uses unit-times-uniformizer powers, the Mathlib `ordFrac` API and fraction
representations to establish the order equality for every function-field element,
including zero. No data is chosen from an undetermined existence statement: the point
is the explicit baseChangeFieldPoint and the rational map is the explicit fraction lift.

Added the proof-only import `Sheaf.AlgebraicGeometry.RationalPointBaseChangeStalk` and
proof-only source imports `BaseChangeCurve`, `Curve.ClosedPoint`, and `DensePoints`.
The new statement module retains proof imports for the existing affine fibre and DVR
calculation nodes that its future proof needs. Existing public imports and all existing
signatures are unchanged. Updated the original DAG proof and proof dependencies.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.local_dvr_base_change`
(node `lem-sc-local-dvr-base-change`). Its proof contains no sorry.

Hole added: `AlgebraicGeometry.Scheme.rational_point_base_change_stalk`
(node `lem-sc-rational-point-base-change-stalk`), the only sorry in this delivery.
It asserts only that an irreducible element of the source stalk has irreducible image
at a point above P. It has no existence, uniqueness, DVR, integral, Noetherian,
function-field-map or order-equality conclusion. This is a decomposition (one upper hole
closed, one strictly smaller lower hole added), not a net reduction in hole count.

The private helper `AlgebraicGeometry.ord_eq_of_stalk_uniformizer` is fully proved.
Both delivered modules compile cleanly with the local launcher.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`;
- `Sheaf.AlgebraicGeometry.DvrFieldExtensionOrder`;
- `Sheaf.RingTheory.FibrePrimesResidueFields`.

`lem-sc-smooth-connected-curve-local-rings` and its large module are not needed anywhere
in this delivery: the closed-stalk DVR conclusions use proved source-library theorems.
The other two removed direct imports and nodes
`lem-sc-dvr-field-extension-order` and
`lem-weil-pbc-fibre-ring-primes-residue-fields` remain proof dependencies of the strictly
smaller new geometric bridge, so they are not claimed as globally pruned.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's assertion that the fibre uniqueness is only two lines from the affine fibre
prime correspondence does not provide the Lean affine/stalk identifications. Uniqueness
is already proved at scheme level by DensePoints.baseChangeFieldPoint_eq_of_fst_eq,
which the delivery uses. The existing smooth_connected_curve_local_rings package is
unnecessarily large for the original and target DVR conclusions; proved ClosedPoint
and Regular declarations suffice. No mathematical statement or definition was changed.

The existing DVR tensor/localization theorem is stated for a particular tensor-product
localization and particular fraction-field structures, whereas the required map is a
scheme stalk map. The new statement isolates only the geometric identification needed
to use its uniformizer clause. Its source is the same affine unit-quotient argument
and Stacks 00E6/00PD as the original node.

## New nodes

`lem-sc-rational-point-base-change-stalk` in
`dag/nodes/sec-curve-estimates/lem-sc-rational-point-base-change-stalk.json`, realized by
`Sheaf.AlgebraicGeometry.RationalPointBaseChangeStalk`.
The complete argument in its docstring identifies the affine fibre and tensor-localized
stalk, then transports the uniformizer clause of dvr_field_extension_order.
Edge cases checked mathematically: for k'=k it is the identity up to the canonical
pullback/stalk isomorphisms; for the projective line at a rational point a local parameter
remains a local parameter; any unit multiple of a uniformizer remains such since units
map to units. The statement does not claim that all points become unique or that
ramified maps preserve irreducibles. Its closed-point and field-extension hypotheses
are retained exactly. LeanSearch was unavailable (HTTP 500); LeanFinder, Loogle and
grep queries and their actual results are recorded in the node. No change records needed.

## Second reading by G2

1. I compared the delivered `LocalDvrBaseChange.lean` against the repository version. The
existing target signature is byte-for-byte unchanged. The proof closes exactly
`AlgebraicGeometry.Scheme.local_dvr_base_change`; the added declaration is in a separate
proof-only module and has the signature recorded in its node. No target hypothesis was added,
removed, or weakened.

2. I compiled both delivered modules with `lcompile.py --all`; they compile without errors or
warnings. The target proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
`implemented_by`. The only remaining `sorry` is the named theorem
`AlgebraicGeometry.Scheme.rational_point_base_change_stalk`, and its node and source/docstring
are present. The helper `ord_eq_of_stalk_uniformizer` is proved. Explicit `#print axioms` in a scratch copy reports only `propext`, `Classical.choice`, and
`Quot.sound` for the private helper. The target and new bridge additionally use `sorryAx`,
as expected from the open bridge and imported open statements; no other axiom occurs.

3. I read the new node and checked it against its Lean declaration. It states only preservation
of irreducibility under the stalk map at a point above a closed point; it does not restate the
local-DVR target or claim uniqueness, fraction-field compatibility, or order equality. Its
hypotheses match the declaration exactly, and the recorded searches include LeanFinder, Loogle,
grep, and the unavailable LeanSearch service. The statement is mathematically consistent in the
identity-extension case and for a DVR uniformizer; the node's retained closed-point and
algebraically-closed-field assumptions are needed for the geometric fibre argument.

4. I checked the proof route and imports against the DAG. The target proof uses the base-change
curve, regularity/integrality, DVR, and rational-point bridge dependencies recorded in
`proof_deps`; the removed direct imports are not used by the target proof. The unit route remains
within the affine unit-quotient argument: the new bridge supplies only the stalk irreducibility
fact, while the target proof separately constructs the fraction-field map and proves the order
comparison. No hollow definition or arbitrary witness was introduced.

5. I checked the DAG/Lean agreement, including `proof`, `proof_deps`, `proof_origin`, the new
node's `lean.statement`, and the report's proved/sorry accounting. The delivery is a genuine
one-hole-to-one-smaller-hole decomposition rather than a restatement: the target's proof combines
DVR geometry, faithful-flat injectivity, an explicit fraction-ring lift, and the private order
lemma around the remaining bridge theorem. No further mathematical or code change was needed
in this second reading.

Second-reader search detail: I independently ran LeanFinder for flat local maps with field
closed fibre, Loogle for `IsLocalHom, Irreducible`, and grep for maximal-ideal map/span lemmas.
Loogle found only `Irreducible.of_map` (the opposite direction); LeanFinder found
`Algebra.FormallyUnramified.map_maximalIdeal`, whose unramified finite-type hypotheses do not
apply to an arbitrary algebraically closed field extension. I also read the existing upstream
`IsDiscreteValuationRing.irreducible_algebraMap_of_map_maximalIdeal`: it proves the last algebraic
step once maximal-ideal equality is available, but does not supply the missing geometric
stalk/fibre identification. Searches of `lean/Sheaf`, `lean/WeilConjectures`, and the upstream
checkout found no exact scalar-extension stalk theorem.

In the helper, `eq_unit_mul_pow_irreducible` reduces nonzero stalk elements to a unit and a power;
units stay units under the ring map. `div_surjective` handles arbitrary fractions, with the zero
numerator checked separately. Thus no injectivity assumption is silently needed by the helper.
In the target, the point is constructed by `baseChangeFieldPoint`, and the map by
`IsFractionRing.lift`; the `obtain` of a rational point uses the proved finite-residue-field API,
not an unproved arbitrary-existence statement. The unit record
`dag/units/sk-prop-ext-invariance.json` has empty realized arrays, and no realized node is
removed. The blueprint literature file is absent on this read-only machine; I checked the
available unit text and the source attribution/docstring rather than claiming to read that file.
