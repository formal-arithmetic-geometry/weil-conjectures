## What changed

Proved `AlgebraicGeometry.Etale.derivedGlobalGerm_unit_fac` in
`Sheaf.AlgebraicGeometry.DerivedGlobalGermUnitFac`, without changing its signature or
public imports. Added a fully proved private abstract helper `derived_unit_germ_fac` in
that same module. It expands the adjunction unit, transports localization factors by
naturality, applies both Leray unit formulas, and applies the derived germ and exact-stalk
unit formulas. The final identity is checked degreewise through the faithful bounded-below
homotopy inclusion. Keeping the functors abstract avoids expensive unfolding of concrete
small-etale functors; the concrete proof instantiates this helper.

Removed the proof-only import `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`.
Updated the item's node proof, proof dependencies and proof origin to match the direct
unit-formula route. A declaration-scoped unused-variable linter setting preserves the
original interface's unused `sq`, `F`, and `G`; no public statement or definition changed.
Local compilation is clean, about 16 seconds, below the 60-second limit.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.derivedGlobalGerm_unit_fac`
(node `lem-weil-pbc-derived-global-germ-unit-fac`).
The private helper `derived_unit_germ_fac` is fully proved too.
No sorry remains in the item and none was added. This is a proof, not a decomposition.

## No longer needed

Removed import and module: `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`.
Removed proof dependency: `lem-weil-pbc-cohomology-pullback-derived-unit`.
In particular this proof does not use its K-injective preservation or Leray-on-K-injective
lemmas. No new imports were added; the original public imports remain necessary for the
statement. Pruning is relative to this module; other target routes may still need the
removed module and its dependencies. The item's node is not a unit-realized statement
or step of `dag/units/sk-thm-p1.json`; the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface error found. The original docstring and DAG describe a
longer route through `derivedCohomologyPullback_eq_derivedUnit`; the same calculation can
start directly from the already proved generic adjunction unit formula. The existing
public docstring is preserved; the updated node and proof comments document the shorter
implemented route. No forced adaptations and no new nodes.

## Second reading by E1

1. Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are byte-for-byte unchanged; only the proof, a proof-only
   import removal, and the declaration-scoped linter setting were changed. Verdict: pass.
2. Compiled the module with the launcher and checked the target's axioms. Compilation is
   clean, there are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or
   `implemented_by` declarations, and `#print axioms` reports only `propext`,
   `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Reviewed the private helper and the updated DAG proof steps. The helper is fully
   proved, introduces no statement or node, and the target statement remains unchanged;
   no split-off statement was added. Verdict: pass.
4. Checked the direct generic unit-formula route against the imported declarations and
   searched for existing alternatives. The removed `CohomologyPullbackDerivedUnit` import
   and dependency are unused; the remaining imports are needed. Verdict: pass.
5. The item's unit `sk-thm-p1` is not realized by this target, so no unit step is
   bypassed. The node's proof, dependencies, and origin match the implementation, and
   the route remains below the unit level. Verdict: pass.

Changed after review: no proof changes; recorded the checks above and retained the
proof-only import pruning and corresponding DAG update.
