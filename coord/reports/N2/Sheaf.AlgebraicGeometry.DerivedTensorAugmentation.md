## What changed

Retired lean/Sheaf/AlgebraicGeometry/DerivedTensorAugmentation.lean via deleted.txt,
as required by its retire-first queue entry. Redirected the Lean attachment of
 def-sc-derived-tensor-augmentation to the existing upstream declaration
AlgebraicGeometry.Scheme.IsDerivedTensorAugmentation in
WeilConjectures.AlgebraicGeometry.DerivedTensorAugmentation. Change record:
coord/changes/retire-derived-tensor-augmentation.md.

The upstream definition has the identical body after the K-flat predicate rename.
The two K-flat predicates have identical defining bodies. A sandbox-only Lean theorem
proves by rfl that the upstream augmentation agrees with the old definition with its
K-flat conditions expanded; its axioms are propext, Classical.choice and Quot.sound.
Compilation succeeded in 6.9 seconds. There are no Lean consumers of the retired copy,
so no consumer compilation or adaptation is required. Upstream files are untouched.

## Proved and sorry left

Definition repair/retirement with zero holes before and zero holes after.
Holes closed: none (0 of 0). Holes added: none. Split off: none.
No declaration is left with sorry by this delivery. The existing upstream
AlgebraicGeometry.Scheme.IsDerivedTensorAugmentation is a concrete definition.

## No longer needed

The duplicate module Sheaf.AlgebraicGeometry.DerivedTensorAugmentation is withdrawn.
Its four imports are removed with it:
WeilConjectures.AlgebraicGeometry.DerivedCategory,
Sheaf.Algebra.Homology.KFlat,
WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed, and
Mathlib.Algebra.Homology.Monoidal. These dependencies may remain needed elsewhere;
this packet makes no claim that they are globally pruned.
No DAG node is removed. The augmentation definition node stays, attached upstream.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with sorry; this item is instead a
zero-hole retire-first repair. The stale DAG attachment pointed at the unused
Sheaf copy. The retirement inventory calls the body different because the upstream
K-flat predicate is named IsKFlatTensor instead of IsAcyclicTensorKFlat; comparing
the predicate bodies and checking the expanded proposition shows identical meaning.
The historical inventory lists nine consumers, all of which now import the upstream
twin; a fresh full-tree search finds no remaining consumer of the retired copy.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
