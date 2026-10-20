## What changed

Proved `AlgebraicGeometry.ProEtale.VaryingRing.modulePi_complement_zero` in
`Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero`, preserving its statement.
Two proved private helpers transfer the existing constant-coefficient disjoint-direct-image
vanishing to varying-ring systems using `moduleEvalG` and `moduleEvalP`, then use the
ordinary pull/direct-image and extension/restriction adjunctions to prove disjoint
restriction of extension is zero. The desired morphism has that zero target.

Added the proof-only `import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`
to reuse its proved private `StrictTower.module_disjoint_direct`; no other module is
changed. The transparency settings apply only to the two private helper declarations.
Updated the existing node's proof, proof dependencies and proof origin to match.

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.ProEtale.VaryingRing.modulePi_complement_zero`
(node `new-lem-sp-varying-ring-module-pi-complement-zero`).
Added 0 holes; no `sorry` remains in the delivered Lean module. Both private helpers,
`disjoint_direct` and `disjoint_extension`, have complete proofs. Existing dependencies
are used as stated, including the ordinary evaluation comparison in
`Sheaf.AlgebraicGeometry.VaryingRingOperations`.

The single-file compile passed. Edge cases require no extra hypotheses: empty opens,
zero coefficient rings and arbitrary coefficient transitions are covered by the existing
constant-ring vanishing theorem and evaluation of actual system sections. The private
extension vanishing helper even allows arbitrary c, while the public statement is unchanged.

## No longer needed

Removed the unused proof import
`Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic`.

The proof no longer directly invokes the planned dependencies
`lem-weil-proetale-weakly-etale-localization` and
`lem-pur-site-restriction-module-adjunction-exact`, or imports their modules
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization` and
`Sheaf.CategoryTheory.LocalizedModuleExactForSystems` directly. Their geometric
calculation is already encapsulated in the proved constant-coefficient helper.
These dependencies can still be needed transitively; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG proposed repeating the test-object calculation
on systems. Reusing the proved constant-coefficient calculation and the existing ordinary
evaluation comparisons makes that repetition unnecessary. Joint faithfulness is used only
for ordinary system sections, never for derived evaluations. No new nodes or interface
changes were needed.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
