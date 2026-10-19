## What changed

Proved `CategoryTheory.Mod.nonempty_equalizerInternalHomAdjunction` in
`Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`, with its signature unchanged.
The existing `ihom'Adjunction R M` supplies the equalizer construction and its natural
Hom bijections (steps 1–9 of `def-sfb-modobj-internal-hom`). For step 10, private,
fully proved helpers construct the monoidal tensor cofork in module objects, verify
its coequalizer universal property after forgetting the action, and compare it
naturally with `Mod.tensorLeft M`. Composing this comparison with
`BraidedCategory.tensorLeftIsoTensorRight M` in the inverse direction and applying
`Adjunction.ofNatIsoLeft` yields the requested adjunction.

The comparison follows the existing private `relativeTensorπ`,
`relativeTensorCofork`, `isColimitRelativeTensorCofork`, and `relativeTensorRightIso`
proofs in `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
Their private visibility prevents direct reuse. No public definitions, signatures,
or other modules change. The unit's equalizer-internal-Hom route is retained.

Validation: the module compiles cleanly through `lcompile.py` (2.3 seconds), including
a temporary `#print axioms` check, which reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. The temporary check is removed from delivery. A resumed compile also passed cleanly
in 2.8 seconds.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Mod.nonempty_equalizerInternalHomAdjunction`
(node `def-sfb-modobj-internal-hom`).

No `sorry` remains in the item. No holes were added and no statements were split off.
All four private construction helpers are fully proved.

## No longer needed

Removed the redundant proof-only import
`WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`; its declarations are already
publicly imported by the existing statement import
`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.
No dependency nodes or modules are pruned: the proof follows the stated ten-step route,
using the upstream equalizer adjunction for the first nine steps and the relative
monoidal tensor and its symmetry for the last step. All original public imports remain.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. A direct application of `ihom'Adjunction`
does not suffice, exactly as the existing docstring warns: `Mod.tensorLeft M` and
`MonoidalCategory.tensorLeft M` are distinct functors and have opposite factor orders.
The required comparison and symmetry are now supplied explicitly.

The compile server initially returned busy/unreachable timeouts; subsequent requests
compiled successfully. No launcher or project tools were changed.

The first resumed dry run passed compilation but required a change record for the
private helper section's `open` and `variable` commands. The commands are scoped and
change no public signature. The record is
`coord/changes/U9-module-equalizer-internal-hom-private-context.md`; it documents both
direct importers, neither of which needs adaptation. This is a process correction,
not a mathematical change.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
