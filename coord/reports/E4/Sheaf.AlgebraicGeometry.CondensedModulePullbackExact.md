## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.module_pullback_additive_exact` in
`Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`, with its signature unchanged.
The source library already proves exactness of `mapMod` and of the composite pullback.
For scalar extension, transferred finite-limit preservation from inverse restriction
along `Mod.extendScalarsIsoComapInv`; finite-colimit preservation is its existing
left-adjoint instance. Assembled all seven clauses from those instances.

Updated the declaration docstring and the existing node's proof, proof dependencies,
and proof origin to describe this shorter route. Removed obsolete tensor/lift tool
approvals from that node. No definitions, statements, visibility, or public imports
changed; no new modules or nodes.

The final module compiles through `lcompile.py` with only its original public import.
A separate compiler probe printed exactly `propext`, `Classical.choice`, and `Quot.sound`
for the theorem's axioms. Thus its proof has no transitive sorry dependency either.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.ProEtale.CondensedRing.module_pullback_additive_exact`
(node `det-prop-sfb-module-pullback-exact-main`).

Holes added: 0. Holes remaining in the delivered Lean module: 0.
Split-off statements: 0.

## No longer needed

Removed all proof-only imports (the original public import suffices):

- `Sheaf.CategoryTheory.SheafTensorClosed`
- `Sheaf.CategoryTheory.ModuleObjects.LiftExact`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`
  (both duplicate import lines)
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal`
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`

The WeilConjectures constructions and their instances remain available transitively
through the public definition module; removing their redundant direct imports does
not claim those underlying constructions are unnecessary.

Removed the following direct proof dependencies from the node:

- `lem-weil-pbc-site-sheaves-enough-injectives`
- `det-def-sfb-sheaf-tensor-closed`
- `sk-def-sfb-pulled-back-coefficients`
- `def-sfb-finite-upper-star-monoidal`
- `lem-sfb-finite-upper-star-braided`
- `lem-sfb-modobj-abelian`
- `def-sp-abelian`
- `def-sfb-finite-lower-star`
- `def-sfb-finite-upper-lower-star-adjunction`
- `det-prop-sfb-module-pullback-exact-lifted`
- `def-sfb-modobj-restriction-equivalence`

The two Sheaf tensor/lift modules are unnecessary for this proof: the existing source
instances already prove the required properties. The remaining removed nodes describe
ambient structure or internal steps of those existing proofs, and are no longer separate
obligations of this theorem. This does not withdraw other users' dependencies on them.
The definition import and the unit's route remain intact.

## Where the brief, the DAG or earlier work was wrong

The six-step plan did not account for already proved exactness instances in the
current source library. The generic lift theorem is therefore unnecessary here.
`def-sfb-modobj-extension-along-iso` has no current Lean attachment, but its exact
construction already exists as `CategoryTheory.Mod.extendScalarsIsoComapInv` in
`WeilConjectures.CategoryTheory.ModuleObjects.MapMod`; no replacement was created.
There is no statement error. No additional geometric or coefficient hypotheses
were required, including for the identity morphism, empty schemes, and the zero ring.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
