## What changed

Proved `AlgebraicGeometry.Scheme.zmodSheaf_hasFieldInvertibleOrders` in
`Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders`, with its signature unchanged.
The sheafification unit gives a unital map from the lifted ZMod ring to each ring
of sections. Mapping its vanishing natural-number cast shows that n annihilates
each module of sections. The stalk-colimit universal property then identifies
multiplication by n with zero. The given n witnesses the invertible-order predicate.
No definitions, statements, or consumers were changed.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.zmodSheaf_hasFieldInvertibleOrders`
(node `lem-kun-zn-sheaf-invertible-orders`).
Added 0 holes; 0 sorries remain in the delivery. Nothing was split off.
The item compiles without warnings through lcompile.py.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
The proof uses Mathlib's `Point.presheafFiber_hom_ext` directly, for the very
`Point.sheafFiber` occurring in the conclusion. The additional wrapper's
`pointedEtaleStalk` and `pointedEtaleStalkDiagram` constructions and commutative
monoid colimit instance are unnecessary here. The geometric-stalk dependency
`def-weil-pbc-geometric-stalks` remains conceptually used through its Mathlib
stalk interface; no mathematical dependency nodes or unit steps are bypassed.
All other imports are retained for the stated coefficient, module, site, and
stalk interfaces or their directly used sheafification operations.

## Where the brief, the DAG or earlier work was wrong

The node plan is valid. Its third step also explains local torsion via identity
covers; the current `IsTorsionOfInvertibleOrder` definition asks only for the
geometric-stalk annihilators, so that separate cover argument is unnecessary.
The proof uses the same colimit argument as the plan and also works directly
with separably closed geometric points. The n=1 case forces the section modules
and stalks to vanish, and is covered without a nontriviality assumption.
The n=0 case is excluded by the original subtype, though the annihilation
calculation itself does not need positivity.

On resumption the assigned sandbox contained only dispatcher metadata, with no
proof packet or pending delivery. Unrelated logs in the shared repository were
not used as W8 validation. The original sandbox and budget were retained.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
