## What changed

Proved `CategoryTheory.Mod.lift_additive_exact` in
`Sheaf.CategoryTheory.ModuleObjects.LiftExact`, with its signature unchanged.
Transport additivity and finite-limit/finite-colimit preservation of the composite
along `h`, then cancel the target forgetful functor using Mathlib's
`Functor.additive_of_comp_faithful`,
`preservesFiniteLimits_of_reflects_of_preserves`, and
`preservesFiniteColimits_of_reflects_of_preserves`.
The needed additive, faithful, preservation and reflection instances are already
proved in `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` and its public imports.
Updated the item's DAG proof to describe this shorter route. No definitions,
public imports, existing signatures or consumers changed.

## Proved and sorry left

Closed 1 of 1 holes: `CategoryTheory.Mod.lift_additive_exact`
(node `det-prop-sfb-module-pullback-exact-lifted`). Added 0 holes; split off 0.
No sorry remains in the delivered Lean module.
The final sandbox compiles without warnings; an explicit `#print axioms` check
reported only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the proof imports `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
and `Mathlib.CategoryTheory.Preadditive.LeftExact`.
The separate kernel/cokernel constructions and the final kernel/cokernel criterion
are unnecessary for this proof: removed direct proof dependencies
`lem-sfb-modobj-kernels`, `lem-sfb-modobj-cokernels`, and
`lem-sfb-kernel-cokernel-finite-exactness`.
The first two are replaced by the existing stronger finite-(co)limit API in
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` and `.Limits`;
the last is replaced by direct finite-(co)limit cancellation through reflection.
This is pruning of this item's direct dependencies; other users may still need
these nodes and modules. The blueprint unit's pullback-exactness statement and
its use of this lift theorem are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned reconstruction of kernels, cokernels
and their reflection was unnecessary given the already proved library instances.
The unit record `dag/units/sk-prop-sfb-module-pullback-exact.json` is absent;
read the corresponding current-blueprint `_section.md` and lift proof instead.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
