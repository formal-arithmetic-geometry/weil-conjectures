## What changed

Retire `Sheaf.Algebra.Homology.TensorPullbackStalkComplex` in favor of its adopted
source twin. Its sole consumer, `Sheaf.Algebra.Homology.KFlatPullback`, now imports
`WeilConjectures.Algebra.Homology.TensorPullbackStalkComplex` and binds the ring map
with `RingedSpace.tensorPullbackStalkRingHom` and the isomorphism with
`CochainComplex.tensorPullbackStalkComplexIso`. The theorem `isKFlat_pullback` keeps
its exact signature and all other proof lines.

The existing node `lem-pc-tensor-pullback-stalk-complex` now points to the source
complex-isomorphism definition. Its mathematical statement and proof route stay
unchanged: pairing this isomorphism with its explicit ring map proves precisely the
old existential conclusion. No source-library file changes.

Change record: `coord/changes/retire-tensor-pullback-stalk-complex-n4.md`.

## Proved and sorry left

This is a zero-hole retirement, not a new proof or decomposition: 0 holes before,
0 holes closed, 0 holes added, 0 holes left, and 0 split off. The already-proved
`CochainComplex.exists_tensorPullback_stalk_complex_iso` is withdrawn. The already-proved
`CochainComplex.isKFlat_pullback` remains proved with its original signature.

Compiled the original item, then checked the original consumer against an empty
item module (it fails at the removed declaration), and compiled the adapted consumer
against that same empty module (it succeeds in 5.8 seconds without warnings).
A separate scratch theorem with the exact old existential signature checks that
pairing the upstream ring map and complex isomorphism supplies it with no hypothesis
or universe change; `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound`. The delivery dry run performs the axiom and signature checks.

## No longer needed

Withdraw `lean/Sheaf/Algebra/Homology/TensorPullbackStalkComplex.lean`, listed in
`deleted.txt`. Remove its private import from `Sheaf.Algebra.Homology.KFlatPullback`.
The declaration `CochainComplex.exists_tensorPullback_stalk_complex_iso` is no longer
used: its consumer uses the upstream ring map and isomorphism directly.

The node `lem-pc-tensor-pullback-stalk-complex` stays and is reattached to the source
implementation. All three proof dependencies remain necessary in that implementation:
`lem-pc-ringed-inverse-image-stalk-scalar-transport`,
`lem-weil-pbc-stalk-change-of-rings-tensor`, and `def-pc-module-stalk-functor`.
No dependency node or source declaration is pruned. The withdrawn module's four public
imports and two proof imports remain supplied by the source twin; there is no claim
that those source dependencies are unnecessary.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed module; the current queue instead marks
this module `retire` with zero holes and one consumer. The source twin replaces the
old existential theorem API with explicit ring-map and complex-isomorphism definitions.
Changing the import alone cannot adapt the caller; it must bind both objects directly.
The node's old Lean attachment named the redundant Sheaf theorem and is now corrected.
The source statements and the unit's proof route are preserved.

LeanFinder found only general stalk pullback comparisons, Loogle did not know the
project-specific source definition, and the remote Mathlib grep returned no hit.
Reading the adopted source twin supplied the exact comparison needed here.

## Forced adaptations

`Sheaf.Algebra.Homology.KFlatPullback` is held by P5. Replacing this item's module
by an empty module makes its original proof fail at line 214:
`Unknown identifier exists_tensorPullback_stalk_complex_iso` and then a dependent
`rcases` failure. The adaptation replaces only line 13's private import and the
local existential elimination by bindings of the source ring map and source
complex isomorphism. It compiles without warnings; all public signatures, visibility,
and public imports are identical. The change record lists every downstream user.

## Forced adaptations

### Sheaf.Algebra.Homology.KFlatPullback
Original against changed dependencies failed:
```
/tmp/forced-adaptation-anzs7iok/lean/Sheaf/Algebra/Homology/KFlatPullback.lean:214:21: error(lean.unknownIdentifier): Unknown identifier `exists_tensorPullback_stalk_complex_iso`
/tmp/forced-adaptation-anzs7iok/lean/Sheaf/Algebra/Homology/KFlatPullback.lean:214:9: error: Tactic `rcases` failed: `x✝ : ?m.159` is not an inductive datatype

(with the modules compiled into /tmp/forced-adaptation-anzs7iok/.lbuild) [31.8 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
