## What changed

Proved `AlgebraicGeometry.Scheme.affineCoverIdeal_map_germ` in
`Sheaf.AlgebraicGeometry.AffineCoverIdealStalk`, preserving its signature and visibility.
The proof refines the arbitrary cover to a finite principal cover and uses elementary
localization calculations rather than constructing and gluing module subsheaves.
Two private, fully proved helpers perform denominator clearing and the finite
principal-open stalk comparison. Added the proof-only import `Mathlib.Data.Fintype.Order`
for `Finite.exists_le`; the existing public import is unchanged.
Updated `lem-sbc-affine-cover-ideal-stalk` to describe the actual proof and dependencies.

The finite-refinement and localization facts are in [Stacks Tag 01HR](https://stacks.math.columbia.edu/tag/01HR),
Lemma 26.5.1(2) and Lemma 26.5.4, and [Tag 00E8](https://stacks.math.columbia.edu/tag/00E8).
The finite-exponent assembly is an argument written by R2 and completely checked in Lean.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.affineCoverIdeal_map_germ`
(`lem-sbc-affine-cover-ideal-stalk`). No holes added or split off; no `sorry` remains.
The private helpers `exists_pow_mul_mem_of_germ_mem` and `finiteBasicIdeal_map_germ`
are also completely proved from Mathlib. This is a proof, not a decomposition.

The module compiles through `lcompile.py` without warnings. The delivery dry run checks
all declaration axioms against the allowed three axioms. Empty covers/open sets cause
no issue because the point hypothesis supplies a covering chart; zero and top ideals,
repeated charts and arbitrary index universes are handled without extra hypotheses.
The finite helper does not require its principal opens to cover U. The final intersection
comparison uses the finite cover to test all stalks of every original chart, so the proof
never exchanges localization with an infinite intersection.

## No longer needed

No pre-existing imports were removed: the original file had only its public Mathlib import.
The four planned proof dependencies are not needed by this proof:

- `lem-weil-pbc-spec-module-tilde-sections` — `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `lem-weil-pbc-spec-tilde-stalk-localization` — `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `lem-weil-pbc-affine-tilde-gamma-adjunction` — `Mathlib.AlgebraicGeometry.Modules.Tilde`.
- `lem-weil-pbc-glue-sheaves-of-modules` — `Sheaf.Topology.GlueSheavesOfModules`.

They have been removed from this node's `proof_deps`. This is pruning for this item;
other users may still require these modules. The replacement finite-cover dependency
`lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` is already a Mathlib leaf.
No new nodes, public declarations, definitions or forced adaptations were added.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The DAG's subsheaf-gluing plan is valid but unnecessary:
finite principal refinement plus denominator clearing proves the exact statement directly
from Mathlib. The unit's statement and realized steps are unchanged. The existing docstring
continues to describe the valid original route; the node and inline comments describe the
implemented route.

## Second reading by R2

1. Compared the delivered module with the repository version. The target declaration signature and visibility are unchanged; only a proof-only import, private helpers, and the target proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. The target and both private helpers contain no `sorry`, axioms, unsafe declarations, opaque declarations, or hollow definitions. An explicit scratch-copy `#print axioms AlgebraicGeometry.Scheme.affineCoverIdeal_map_germ` reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. No statements were split off and no new declarations are public. The proved target is the original statement, including empty and degenerate ideal cases. Verdict: pass.
4. The proof uses finite principal-open refinement and localization lemmas directly. The unit statement and realized route remain represented by the existing node; the proof dependency list was pruned to the finite basic-open dependency. Verdict: pass.
5. The DAG node's proof, proof dependencies, and proof origin match the implemented proof and the target signature is unchanged. Verdict: pass.

Changed in this reading: added this review record; no Lean code or DAG statement changes were needed.
