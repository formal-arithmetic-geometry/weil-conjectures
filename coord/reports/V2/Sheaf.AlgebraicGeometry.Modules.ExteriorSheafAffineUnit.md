## What changed

Replaced the sorry in `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafAffineUnit` by a proof
that the exterior presheaf is affine-localizing, followed by the existing
`isIso_sheafificationUnit_app_of_affine_localizing` theorem and
`ConcreteCategory.bijective_of_isIso`. The localization of quasi-coherent sections is the
proved upstream `isLocalizedModule_basicOpen`. The exterior restriction's pure-wedge
formula comes directly from `exteriorSheafRestriction_existsUnique`.

Added proof-only imports of `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, and the new algebraic module
`Sheaf.LinearAlgebra.ExteriorPowerLocalization`. Updated the item's node to this route.
Every existing signature, public import, and definition is unchanged. No adaptations.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.Modules.exteriorSheaf_affine_unit_bijective`
(node `new-q1-exterior-sheaf-affine-unit-bijective`), by reduction to algebraic localization
and the existing affine-localizing sheafification theorem. No sorry remains in the item.

Added and still sorry: `exteriorPower.isLocalizedModule_of_wedge`
(node `new-v2-exterior-power-localization`), in
`Sheaf.LinearAlgebra.ExteriorPowerLocalization`. Its entire proof is `by sorry`.
This is strictly the algebraic localization step: it has no schemes, quasi-coherence,
affine opens, sheafification, or sheafification-unit conclusion. Its docstring and node
contain the fraction argument. The item supplies its hypotheses using actual library
maps and then applies the independently proved geometric sheafification theorem.

This delivery is a decomposition: one hole closed and one added, not a net completed proof.
Both modules compiled together without warnings. Degree zero gives ring localization;
localizing at a submonoid containing zero gives zero modules. The algebraic statement
requires no finite-generation, projectivity, flatness of M, or local-freeness assumption.

## No longer needed

No original import was removed, and no module is claimed globally pruned.
The direct proof dependency `lem-weil-pbc-affine-tilde-gamma-adjunction` is replaced by the
existing basic-open localization package and affine-localizing sheafification theorem;
it remains an indirect dependency of the localization package. The direct exterior-algebra
dependency `def-weil-pbc-exterior-algebra` moves to the new algebraic node. The definition
node `def-sc-sheaf-exterior-power` remains directly used. No unit statement or realized
unit step is bypassed. The new proof-only imports are all used.

## Where the brief, the DAG or earlier work was wrong

The original plan's algebraic localization step had no separate Lean theorem. It is now
isolated with a precise pure-wedge compatibility hypothesis. Its sheafification step
already has a reusable theorem in the library, so a new associated-sheaf comparison is
unnecessary. No mathematical statement was found false.

Implicit inference of the two section rings in the localization lemma application caused
expensive elaboration. Supplying R and B explicitly reduced the item compile to about four
seconds with the normal heartbeat and wall-clock limits; no definition or time limit changed.
LeanSearch was unavailable; LeanFinder, Loogle, source grep, and blueprint searches were used.

## New nodes

`new-v2-exterior-power-localization` states the algebraic localization of exterior powers,
characterized by the image of each pure wedge. It is the algebraic content of step 2 of
`new-q1-exterior-sheaf-affine-unit-bijective`. Its module is
`lean/Sheaf/LinearAlgebra/ExteriorPowerLocalization.lean`; its source, complete fraction
proof, searches, and exact Lean signature are recorded in the node. No change record is
needed because no existing interface changed.

## Second reading by V2

1. Compared both delivered modules with the repository versions. Existing theorem
   signatures and definitions are unchanged; additions are proof imports, proofs, and
   the separately declared localization theorem.
2. Compiled both modules with `lcompile.py --all`. The build is clean. The only remaining
   `sorry` is the named `exteriorPower.isLocalizedModule_of_wedge`; no forbidden
   declarations or hollow definitions occur.
3. Checked the split-off localization statement against its fraction construction and
   boundary cases (degree zero and a submonoid containing zero). It is strictly the
   algebraic localization step, has a complete docstring proof, and has the matching DAG
   node; searches found no existing duplicate declaration.
4. Read the proof from the target downward. It uses the existing affine localization and
   affine-localizing sheafification results, with the new algebraic theorem supplying
   exactly the pure-wedge compatibility step. No shorter available library route was
   found, and no unused imports were identified.
5. The DAG proof and proof dependencies match the Lean proof. The item's unit route is
   preserved: affine-localizing sheafification remains explicit and the new theorem
   realizes only its algebraic prerequisite.

Changed only this report section during second reading; no Lean statements or definitions
were altered.
