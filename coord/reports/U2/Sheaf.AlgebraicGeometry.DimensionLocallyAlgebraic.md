## What changed

Proved AlgebraicGeometry.dimension_locally_algebraic in
Sheaf.AlgebraicGeometry.DimensionLocallyAlgebraic, with its signature and visibility unchanged.
The reduction map is a homeomorphism. Its source is integral and the composite to Spec k is
locally of finite type. Pull back a nonempty open, apply the already-proved source theorem
AlgebraicGeometry.topologicalKrullDim_opens_eq, and transport dimension through the restricted
homeomorphism. The pointwise clause follows from topologicalKrullDimAt_eq_of_forall.
All proof imports are private. No definitions, instances, or public imports changed.
The final module compiles without warnings using lcompile.py.

## Proved and sorry left

Closed the only original hole: AlgebraicGeometry.dimension_locally_algebraic
(node lem-sc-dimension-locally-algebraic). No sorry remains in this module and no hole was added.
This is a proof, not a decomposition into new unproved statements.

## No longer needed

Removed import Sheaf.Topology.DimensionSupremumLocalDimensions. Its node
lem-weil-pbc-dimension-supremum-local-dimensions is not needed on this proof route.
The direct dependencies def-kun-topological-dimension-at-point and
lem-weil-pbc-open-subspace-dimension-monotone are not used directly by the main theorem.
The latter remains below the attached source theorem, as do
lem-weil-pbc-affine-opens-basis, lem-sc-integral-locally-algebraic-affine-opens-dimension,
and def-weil-affine-spectrum; these are not claimed globally pruned.
Kept the reduction theorem and WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType.
No other module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The existing node's split report had already identified topologicalKrullDim_opens_eq,
but the planned route still reimplemented its integral-case argument. The proof now uses that
closed source theorem and records it as a dependency. The node is not a realization of the
unit's statement or any unit proof step in dag/units/sk-prop-jacobian.json, so this shortcut
is below the unit level. The unit and its realization were unchanged.
LeanFinder and Loogle returned supporting topology/integrality facts, not the full theorem;
LeanSearch was unavailable (HTTP 500). Direct source search found the proved integral-case
statement. No statement was disputed or changed, and no forced adaptation was necessary.

## New nodes

lem-sc-integral-locally-algebraic-opens-dimension attaches the existing, fully proved
AlgebraicGeometry.topologicalKrullDim_opens_eq in
WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType. It introduces no module,
no declaration and no sorry. Its statement is the integral-case open-subset clause, strictly
smaller than the item (which allows nonreduced X and also asserts pointwise dimension).
The source theorem's finite-chain/affine-cover proof and original affine-dimension dependency
are recorded. The generic closed theorem is used as a tool, preserving the unit route.
Blueprint search for "nonempty open" returned 13 nodes, none stating this integral-case result;
the existing broader node remains the item. No change record is needed.

## Second reading by U2

1. **Visible changes.** Compared the delivered module and DAG records with the repository versions. The theorem signature and visibility are byte-for-byte unchanged; only the proof, imports, and proof metadata changed. No target statement or definition changed.

2. **Proof and axioms.** Compiled `DimensionLocallyAlgebraic.lean` with `lcompile.py`; it compiles without warnings and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. The proof reduces to the reduction homeomorphism, applies the existing integral open-dimension theorem, and uses the proved local-dimension characterization.

3. **Split statements and nodes.** The added node `lem-sc-integral-locally-algebraic-opens-dimension` records the already-proved source declaration `AlgebraicGeometry.topologicalKrullDim_opens_eq`; it introduces no Lean declaration or proof hole. Its statement is the strictly smaller integral case and is true. No duplicate declaration was found in `lean/` beyond the attached source theorem.

4. **Pruning and route.** The removed `Sheaf.Topology.DimensionSupremumLocalDimensions` import is unused by the proof. The old affine-open and supremum-local-dimension dependencies are no longer on the proof route. The reduction and integral open-dimension route remains below the unit level, and the unit realization is unchanged.

5. **DAG agreement.** The item node's proof and `proof_deps` record the reduction, homeomorphism dimension transport, integral open-dimension theorem, and local-dimension step used by the Lean proof. No statement change or forced adaptation is required.

Changed: appended this review, retained the delivered proof, and made no further code changes.
