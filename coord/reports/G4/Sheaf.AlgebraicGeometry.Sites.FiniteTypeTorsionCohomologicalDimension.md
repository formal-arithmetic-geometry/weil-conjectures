## What changed

Closed `AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType`
by applying the existing affine-to-global reduction with the existing affine finite-type bound.
A private proved helper converts the field hypothesis from derived-category cohomology to
`Sheaf.H`; the resulting bound is transported back along the same global-sections comparison
isomorphisms. Added only the proof import
`WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived`.
Updated the target node's proof and proof origin; its original two proof dependencies remain.
No existing signature, definition, visibility, or public import changed.

## Proved and sorry left

Holes closed: one, in
`AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType`
(node `thm-sc-finite-type-torsion-cd`). Holes added: none. No `sorry` remains in the module.
The private helper `subsingleton_H_of_subsingleton_derivedCohomology` is also proved.
A scratch copy containing `#print axioms` for both declarations compiles and reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for each; there is no `sorryAx` dependency.

## No longer needed

None relative to the repository: both original proof dependencies and their imports remain
used. The second reading replaced the first worker's candidate import
`WeilConjectures.AlgebraicGeometry.Sites.LerayVanishing` with the general comparison module;
this does not prune a module from the target closure. No unit node is bypassed.

## Where the brief, the DAG or earlier work was wrong

The target uses ordinary derived-category cohomology, while its two provided intermediate
bounds use `Sheaf.H`. Existing general global-sections comparison isomorphisms bridge them.
The first worker's DAG update cited `lem-sc-leray-vanishing-bound`, whose declaration is the
Leray rectangle bound; that declaration is not used by this proof. The second reading removed
that inaccurate dependency and recorded the elementary comparison transports explicitly.
The unit record `dag/units/sk-prop-sf-finiteness.json` has pre-existing empty `realized` arrays;
this delivery preserves its route and does not change the unit record.

## New nodes

None. No change records are needed: no existing statement or definition changed.

## Second reading by G4

1. **Visible declarations: pass.** Read the entire diff against the repository and checked
   the target signature byte for byte. No existing signature, definition, visibility or
   public import changed. The only added declaration is a private proved comparison helper.
2. **Proof: pass.** The final module and a separate scratch copy with `#print axioms` for
   the helper and target compile cleanly through `lcompile.py`. Both declarations use only
   `propext`, `Classical.choice`, and `Quot.sound`. No holes or forbidden declarations remain.
   The isomorphisms transport vanishing of the same sheaf in the same degree, in the correct
   direction; no data are chosen from an unproved existence theorem.
3. **Split statements: pass.** None were added. Checked the helper also in degree zero:
   its transport applies uniformly in every natural degree. Checked `d = 0`, `c = 0`, zero
   coefficients, and the empty-scheme boundary: the intermediate bounds accept dimension
   inequalities, and the proof adds neither a positivity nor a nonemptiness hypothesis.
4. **Route and pruning: pass.** Read both intermediate declarations, the source theorem
   `Scheme.subsingleton_H_of_two_mul_add_lt`, the target blueprint proof, and the unit route.
   The source theorem is precisely the same composition of the two intermediate bounds;
   using it would add an import without shortening the mathematical route. Local searches
   and an independent `msearch.py ... grep` search found no direct Mathlib alternative.
   The final proof uses the two original dependencies and a direct general comparison import;
   no original import or dependency can be pruned. The unit's comparison/Leray route stays.
5. **DAG: pass after repair.** Removed the incorrect dependency on the Leray rectangle
   theorem, whose declaration was not applied, and described both comparison transports
   separately from the two affine/reduction dependencies. Verified the node differs only
   in allowed proof metadata and that its statement and Lean record are unchanged.

Second-reading changes: replaced the candidate LerayVanishing import and its specialized
comparison wrapper with the existing general sheaf comparison, repaired the DAG's dependency
metadata, and made the report explicit about closed/added holes and axiom results. The original
proof's affine and affine-to-global steps were retained.
