# Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases

## Reason

Finish the listed duplicate retirement by withdrawing the unused compatibility
stub. The reviewed Q8 retirement already moved the node attachment and both
consumers to the official source theorem. The remaining Sheaf file introduces
no declarations, and the current library and quarantine contain no imports of
it. Keeping its two public imports serves no remaining proof or statement.

This withdrawal removes only the re-export module. It preserves the mathematical
node, its statement, proof and dependencies, and its existing upstream Lean
attachment. It does not prune or alter any adopted source-library declaration.

## Old

The module contains no declarations and has these imports:

```lean
public import WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
```

## New

The file is listed in `deleted.txt`. The delivery tool replaces it with its
standard empty withdrawn module:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The replacement theorem remains
`AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases` in
`WeilConjectures.AlgebraicGeometry.KoszulSelfExtStalkBases`. Its existing proof
constructs the two finite stalk bases from the local self Ext frame and the
conormal exterior frame. Both parent proofs already specialize that theorem,
unfold its let bindings, and transport the exterior basis by
`exteriorSheaf_eq_exteriorPower` before their finite-rank argument. These are
existing complete replacement arguments, preserved verbatim.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases | S2 | Withdraw its unused re-export stub. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | not adapted | DAG parent already imports the official theorem directly; compiles unchanged in 5.3 s. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | not adapted | DAG parent already imports the official theorem directly; compiles unchanged in 9.7 s. |

`tools/downstream.py` reports zero downstream modules and zero uses in the
withdrawn module. A full import search of `lean/` and `quarantine/` confirms zero
importers. The two mathematical DAG parents above remain attached to their
existing declarations; neither parent uses this compatibility file. The unit
record does not realize any statement or step through this empty wrapper.
No parent dependency needs changing: both still cite the same retained node,
whose Lean attachment already names the official upstream module. The node's
Lean note records this distinction between withdrawing the wrapper and retaining
the mathematical result.

## Status

landed 20261021T011036-L-2031897 2026-10-21 (merge of deliver/S2/Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases)
