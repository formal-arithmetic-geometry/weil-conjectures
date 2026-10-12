## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAffine_and_isAmple_tensorUnit_of_dim_le_zero`
without changing its signature. Uses the existing dimension-zero finite-discrete theorem,
then Mathlib's affine instance. The ampleness verification is completely proved in private
helpers: construct the map from the structure-module stalk to the local ring by the colimit
universal property, make it linear, and transport section 1 through the right unitor.
Its germ maps to 1, hence cannot belong to the maximal ideal times the stalk module.
All helper data are actual constructions and all helper proofs are complete.

Added proof imports `Mathlib.AlgebraicGeometry.Limits` and
`WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk` (proved stalk linear-map API).
Updated the existing node's proof, proof_deps and proof_origin to match.
The unit's realized statement and steps are retained unchanged.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.Modules.isAffine_and_isAmple_tensorUnit_of_dim_le_zero`
(node `lem-sc-zero-dim-noetherian-affine`). No sorry remains in the delivered module.
No holes added, no new nodes, and no decomposition into new sorried statements.
The imported existing theorem
`AlgebraicGeometry.finite_and_discreteTopology_of_topologicalKrullDim_le_zero`
(node `lem-sc-zero-dim-noetherian-finite-discrete`) is used as the stated next item;
this delivery does not claim to close its hole or the target's entire axiom closure.
Empty schemes are covered by the finite-discrete theorem; the ampleness pointwise
condition is vacuous. Nonempty cases use only that stalk rings are local.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine`:
node `lem-sc-finite-discrete-separated-affine` is bypassed by the proved Mathlib
instance recorded in `lem-weil-pbc-finite-discrete-scheme-affine`.
Removed redundant direct import `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
the tensor powers and unit API are already publicly imported by Ample.
The direct proof dependency `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`
is unnecessary here; it remains in the finite-discrete theorem's own proof plan.
No other node or module in the original plan is pruned. These are local pruning
claims, not claims that no other target route imports the modules.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found. The DAG's separated affineness step can use the
stronger proved Mathlib instance directly. The step described as elementary ampleness
requires transporting section 1 along the unitor and a linear identification of stalks;
these categorical and colimit calculations are now implemented explicitly.

## Second reading by R3

1. **Statements and signatures.** Compared the delivered module and node with the repository versions. The public theorem signature is byte-for-byte unchanged: it still assumes `[IsLocallyNoetherian Y]`, `[CompactSpace Y]`, `[Y.IsSeparated]`, and `topologicalKrullDim Y ≤ 0`, and concludes `IsAffine Y ∧ IsAmple Y (𝟙_ Y.Modules)`. The finite-discrete theorem is used with the same hypotheses, including the empty scheme.

2. **Proof and axioms.** Compiled the delivered module with `lcompile.py`; it compiles without warnings. The proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx`. A scratch axiom probe shows every private helper uses only `propext`, `Classical.choice`, and `Quot.sound`; the public theorem additionally depends on the intentionally open finite-discrete theorem and therefore reports `sorryAx` transitively.

3. **Statements split off and searches.** No statements were split off and no new nodes were added. The helper constructions are private proof infrastructure, not API claims. The existing Mathlib finite-discrete affineness instance and the existing stalk-module API were checked in their recorded nodes; a fresh concept search found no shorter theorem proving ampleness of the tensor unit on an arbitrary affine scheme.

4. **Pruning and route.** The proof follows the unit route: finite/discrete topology, Mathlib finite-discrete affineness, then the Definition 01PS ampleness check. It removes only proof-only imports that are no longer used (`Sheaf.AlgebraicGeometry.FiniteDiscreteSeparatedAffine` and `WeilConjectures.AlgebraicGeometry.Modules.Invertible`) and the corresponding obsolete proof dependencies. The unit record remains unchanged.

5. **Node agreement and mathematical edge cases.** The only changed existing node fields are `proof`, `proof_deps`, and `proof_origin`. Its three steps match the Lean: the finite-discrete theorem, the Mathlib instance at `AlgebraicGeometry/Limits.lean:700`, and the explicit stalk-linear nonvanishing argument. The new `proof_deps` is exactly the union of the steps’ `uses`; every old dependency no longer used is named under `## No longer needed`. No new node requires validation. The empty scheme is covered by the finite-discrete theorem and the pointwise ampleness condition is vacuous. For every nonempty point, the constructed stalk-linear map sends the selected germ to `1`; membership in maximal-ideal times the stalk would force `1` into the maximal ideal, contradicting its properness. The top open is affine by the inferred `IsAffine Y` instance.

Changed during second reading: added this review record only; no Lean statements or proof terms required repair.
