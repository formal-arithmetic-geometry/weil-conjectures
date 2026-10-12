## What changed

Replaced the sorry in `AlgebraicGeometry.closedImmersion_rankStrata_scalar_formality`
with a complete Lean proof from a single new one-stratum scalar lifting theorem.
The existing signature, universe parameters, public imports, and docstring stay unchanged.

The item now proves three private helpers: `coprojection_isIso_of_other_zero`,
`inclusion_homology_isIso`, and `zeroDifferentialAssembly`. The last constructs the
countable coproduct of single complexes, uses `derivedAmbientDirectSumsCofan` to
assemble the chosen lifts, and uses `derivedAmbientDirectSumsHomology` to show both
the comparison to the zero-differential complex and the map to K are isomorphisms.
The integer index is lifted to `ULift.{u} ℤ` to match the coproduct lemmas' universe.
No finiteness or algebra-action hypothesis is introduced.

Added proof imports of `ClosedImmersionRankStrataScalarHomologyLift` and Mathlib's
`SingleHomology`. Updated the item's DAG proof and dependencies to match this route.
Added one module and node for the remaining geometric lift, with its complete proof
in words. The source's truncation, open-extension, and coproduct route is retained.
The unit record `sk-thm-picard-duality` has no realized statement or step pointing
at this item; no unit-level statement or route has been changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.closedImmersion_rankStrata_scalar_formality`
(node `lem-sc-closed-immersion-rank-strata-scalar-formality`). No sorry remains
in the item's module, including its three private helpers.

Added: `AlgebraicGeometry.closedImmersion_rankStrata_scalar_homology_lift`
(node `lem-sc-closed-immersion-rank-strata-scalar-homology-lift`), whose entire
proof is `by sorry`. This is the only new hole. It asserts the lifting of an
arbitrary map from ONE single-degree support, assuming only the other degrees
are prescribed; it asserts neither global formality nor an isomorphism. The
parent supplies the degree-n isomorphism, turns the lift into an isomorphism
on degree-n homology, and proves all countable assembly and detection glue.
This delivery is a decomposition: one old hole closed, one strictly smaller
hole added, not a net reduction in the number of holes.

The new lifting statement was checked on negative degrees (zero source), empty
Z and empty rank strata (zero source), rank zero (degree-zero truncation), and
unbounded rank (only one support is used). The open complement V of the other
closed rank supports contains the closed support of the source. Exact extension
by zero of its restriction has the same stalks as the source even at boundary
points outside V, because the support is closed and contained in V.

Both modules compile through lcompile.py with no warnings. The generic coproduct
assembly is proved rather than split off. The new lift is not the existing
algebra-valued `clopenRankStrata_homology_lift`: its module category is scalar
O_Y-modules, and no direct-image-algebra action is available.

## No longer needed

Removed the item's direct proof imports:
- `Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction`;
- `Sheaf.Algebra.Homology.ModuleStalkExact`;
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`.

Their nodes `lem-sc-derived-open-shriek-derived-adjunction`,
`lem-weil-pbc-module-stalk-exact`, and
`lem-sc-derived-open-restriction-adjunction-exact` move to the proof of the new
one-stratum lift. They remain needed transitively, so no global pruning of these
modules is claimed. Likewise `def-sbc-standard-tstructure-derived-category`
is used by the lift, not the assembly. `def-weil-closed-immersion` and
`def-sc-locally-ranked-exterior-complex` remain statement dependencies and are
used by the lift's geometry. The two ambient direct-sums nodes and their imports
are used explicitly and retained. No planned module is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The existing finite-rank, algebra-valued
formality and lifting declarations do not apply to the scalar, potentially
unbounded-rank statement. The original plan omitted the concrete one-stratum
lifting interface needed to combine its truncation and adjunction steps with
Lean's coproduct interfaces; that interface is now the sole remaining hole.

Searches were run via msearch.py (LeanFinder, Loogle, grep, and LeanSearch) and
local rg in both library roots and Mathlib. LeanSearch returned Internal Server
Error and is recorded as unavailable, not as a negative search result. Searches
found generic single-complex and K-injective declarations but no exact scalar
rank-support lift. Blueprint searches for rank stratum and single degree found
no equivalent statement. The cited Stacks TeX files are not present in this
read-only checkout; the source places and argument come from the supplied parent
node and its full declaration docstring, not an independently fetched source.

## New nodes

`lem-sc-closed-immersion-rank-strata-scalar-homology-lift`:
`lean/Sheaf/AlgebraicGeometry/ClosedImmersionRankStrataScalarHomologyLift.lean`.
It isolates one-degree scalar lifting through the open complement of the other
closed rank supports. Its three proof steps give the geometry, exact restriction
and single-degree truncation, then extension by zero with the homology equation.
No interface change, forced adaptation, or change record is needed.

## Second reading by N4

1. The existing target declaration and signature were compared byte for byte with the repository version; the target statement is unchanged. The new scalar homology-lift statement is a separate strictly smaller interface and introduces no hypotheses into the target.

2. Both delivered modules compile cleanly with `lcompile.py --all`. The formality proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definitions; the only remaining `sorry` is the named public lifting theorem, and its node and proof docstring are present.

3. The split-off lifting statement is true and exactly the needed one-degree reduction: it allows arbitrary degree-n maps, assumes only other-degree homology identifications, and does not restate the parent target. Searches and local `rg` found no existing scalar theorem with this interface.

4. The proof follows the shortest available route after the split: one-stratum lifts, proved direct-sum cofan and homology declarations, and an elementary zero-differential assembly. The removed proof-only imports are no longer referenced by the item; the corresponding dependencies remain in the lifting node. The unit route is preserved through the one-stratum truncation/lifting step and direct-sum assembly.

5. The formality node proof, proof dependencies, and proof origin match the Lean proof. The new lifting node records its declaration, source, proof steps, searches, and remaining `sorry`; no unit record or target statement was changed.

Changed after reading: added this review section only; no Lean statements or proofs were altered.
