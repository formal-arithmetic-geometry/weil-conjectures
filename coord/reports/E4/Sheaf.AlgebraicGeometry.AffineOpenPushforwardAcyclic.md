## What changed

Proved `AlgebraicGeometry.affine_open_pushforward_rightAcyclic` without changing its
signature or public imports. Added the proved comparison theorem
`AlgebraicGeometry.open_pushforward_rightDerived_comparison` in
`Sheaf.AlgebraicGeometry.OpenPushforwardDerivedComparison`. It computes derived
composition on an open-pushforward-acyclic module using an injective resolution.
The target establishes affineness of the inclusion with Mathlib
`IsAffineHom.of_comp`, uses affine vanishing on the inclusion, applies the
comparison, and uses affine vanishing on the composite.

Removed the first worker's degreewise restatement, its module and its proposed
node. Updated the original node's proof, proof_deps and proof_origin. No existing
statement or definition changed, and no change record is needed.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.affine_open_pushforward_rightAcyclic`
(node `lem-pc-affine-open-pushforward-acyclic`): 1 of 1 original holes closed.
Also proved `AlgebraicGeometry.open_pushforward_rightDerived_comparison`
(node `lem-pc-open-pushforward-derived-comparison`).

Holes added: none. Holes left in delivered modules: none. Split off: none.
The proposed sorry theorem
`AlgebraicGeometry.affine_open_pushforward_higher_direct_image_isZero` was removed,
not delivered. This is a proof, not a decomposition. Explicit `#print axioms`
checks of both delivered theorems show exactly `propext`, `Classical.choice`,
`Quot.sound`, without `sorryAx`.

## No longer needed

Removed these proof-only imports from the target module:
- `Sheaf.CategoryTheory.GrothendieckComposablePair`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`

Every old proof dependency not directly used by the new proof:
- `lem-weil-pbc-separated-affine-open-intersection`: Mathlib `IsAffineHom.of_comp`
  supplies the inclusion's affineness directly.
- `prop-pur-kinjective-resolutions-exist`: injective resolutions on W come from
  the proved upstream `Scheme.Modules.isGrothendieckAbelian`; no new resolution
  construction is needed. Its module remains indirectly available through the
  unchanged public `RingedSpaceDerivedDirectImage` import.
- `def-sp-composite-acyclicity`
- `thm-sp-grothendieck`

Retained `lem-pc-affine-morphism-hi`, used for both vanishing arguments. Added
`lem-pc-scheme-modules-grothendieck-abelian` and the proved comparison node.
These are removed explicit imports and dependencies; no claim is made that the
modules leave the whole targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The earlier degreewise vanishing theorem simply unfolded the target's universal
quantifier, retaining its full geometric and homological content. It was not a
strictly smaller intermediate argument. Its previous second reading was therefore
incorrect. The first worker also left the original node's proof unchanged.

The spectral-sequence route is unnecessary below the unit level: the comparison
can be computed directly using the established acyclic-resolution machinery.
The acyclic affine-open resolution remains the route used by its parent; no unit
statement or realized step changes. `dag/units/sk-thm-picard-semicon.json` has empty
realized entries, and this delivery does not modify them.

## New nodes

`lem-pc-open-pushforward-derived-comparison` records the proved comparison for any
scheme morphism f and any open inclusion j, assuming M is j_*-acyclic and the two
source categories have injective resolutions. The proof pushes an injective
resolution through j_*, uses preservation of injectives by the restriction
adjunction, and computes both sides from the same complex. The node includes the
verbatim Lean statement, its full proof route, source and all required search kinds (plus Loogle).
No change records.

## Second reading by E4

1. Compared the target with the repository by `diff`; its existing theorem
   signature is byte for byte unchanged. Only proof text, the explanatory proof
   docstring and proof-only imports change. No definitions are delivered.
2. Compiled both modules through `lcompile.py --all`, with no errors or warnings.
   Inspected all delivered Lean for forbidden declarations and sorries: none.
   Explicit `#print axioms` checks give only the three standard axioms for both
   theorems. The delivery tool also runs its declaration-wide axiom probe.
3. Removed the non-progress degreewise restatement. The replacement comparison
   is fully proved, with no split-off statements. Checked degree zero, identity
   inclusion, empty open and zero module: the resolution comparison applies in
   all these cases and positive affine vanishing handles the target. Repeated
   LeanSearch (unavailable: Internal Server Error), leanfinder, loogle and grep searches with composition/acyclic-resolution terms;
   searched lean/Sheaf and upstream sources. Used the existing acyclic-resolution
   and quasi-isomorphism lemmas instead of restating them.
4. Read the proof top downward: Mathlib supplies affineness, upstream affine
   vanishing supplies both acyclicity statements, and the proved resolution
   comparison connects them. Removed all three unused explicit plan imports.
   Listed every unused old proof dependency above. The unit route stays intact;
   no realized node is bypassed.
5. Updated the original node to match the proof actually written and checked the
   new comparison node against its Lean signature and resolution proof. Existing
   node changes are confined to proof, proof_deps and proof_origin. New node has
   the required source, searches, blueprint, creation and Lean records.

Second reading changed: replaced the degreewise restatement with a fully proved
open-pushforward derived comparison, completed the geometric target proof,
pruned the three explicit plan imports, repaired DAG records and this report.
