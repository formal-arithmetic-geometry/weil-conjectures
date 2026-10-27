## What changed

Proved `SheafOfModules.exists_epi_coproduct_jShriek` in
`Sheaf.CategoryTheory.QuotientJShriek`, with its signature unchanged.
Sheafify Mathlib's canonical free Yoneda presheaf coproduct and its epic evaluation
map, then compose with the sheafification counit. Preservation of coproducts and
epimorphisms follows from the left adjoint instance; the counit is an isomorphism.
Functoriality proves the prescribed component equations.

Updated the existing node's proof, proof dependencies, proof origin and obsolete
tool use to record this route. No statements or definitions changed.

## Proved and sorry left

Closed the sole original hole:
`SheafOfModules.exists_epi_coproduct_jShriek`
(node `lem-pc-sites-modules-quotient-j-shriek`).
One of one original holes proved; zero holes added, zero split off, zero remain.
The reduced-import module compiles using the remote single-file compiler.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed these private proof imports:
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `Sheaf.CategoryTheory.RingedSiteModules`

This proof does not need `lem-weil-pbc-module-sheaves-colimits-forgetful` or
`def-weil-extension-by-zero-presheaf`: the presheaf coproduct and epimorphism are
already proved by Mathlib, and its left adjoint API supplies preservation.
The general category node `def-weil-sheaf-of-modules-category` remains a statement
dependency; no separate abelian-category or cokernel argument is used in the proof.
Removed the obsolete `lem-weil-pbc-module-sheaves-colimits-forgetful` tool use.
These are dependencies pruned from this proof only; none of their modules or
public declarations is withdrawn. Existing public Mathlib imports are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The old DAG described a longer cokernel argument;
Stacks explicitly also permits sheafifying the presheaf construction. Mathlib's
`fromFreeYonedaCoproduct`, its Epi instance, and its coprojection equations
already provide the presheaf construction. The unit's realized route is unchanged.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
