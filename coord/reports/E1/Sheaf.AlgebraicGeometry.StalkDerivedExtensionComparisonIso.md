## What changed

Restored Sheaf.AlgebraicGeometry.StalkDerivedExtensionComparisonIso from its
quarantine archive and added `public import Sheaf.Algebra.Homology.KFlat`.
The import makes the existing public `IsAcyclicTensorKFlat` hypothesis visible.
The complete theorem signature, docstring and proof are otherwise unchanged.
Change record: coord/changes/E1-stalk-derived-comparison-iso-kflat-import.md.

The archived original fails server compilation with `Invalid field
IsAcyclicTensorKFlat` at line 83. The repaired module compiles successfully in
4.9 seconds, with no errors or warnings. Read both declared dependency theorems
and their nodes: the original proof constructs the comparison transformation,
uses its representative equation to establish invertibility, and bundles it with
`asIso`, whose hom is definitionally the original transformation. The exact
representative equation is therefore retained. Mathlib searches confirm the
existing `asIso` API; no replacement route is needed.

## Proved and sorry left

Zero holes before and zero after. Closed: none. Added: none. Split off: none.
The existing proved declaration is
`AlgebraicGeometry.SingleComplexBaseChange.exists_stalkDerivedExtensionComparisonIso`
(node lem-pc-stalk-derived-extension-comparison-intermediate). This is an assigned
zero-hole compilation/interface repair, not a new proof or decomposition.
No sorry remains in the delivered module; no other Lean file is delivered.

## No longer needed

None. Both private proof imports are used by the unchanged proof; the public
stalk-transport import and added public KFlat import supply its statement.
No node, module or dependency is pruned or withdrawn. The existing DAG attachment,
proof steps and unit route remain correct and need no update.

## Where the brief, the DAG or earlier work was wrong

The rework error is accurate and was reproduced on the archived original.
A public signature cannot rely on its K-flat predicate being available only
through private proof imports. The two immediate dependency modules already
received the same public-import repair from M2 and M3; this module requires its
own direct public import as well. The quarantine archive and its mathematical
content have been preserved. No statement or definition repair was necessary.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
