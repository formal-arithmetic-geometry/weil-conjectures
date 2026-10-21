## What changed

Proved `CategoryTheory.Functor.exactTensorFunctor_derived_braiding` without changing
its signature. Added five proved private helpers in its module: transport of
bifunctor components along isomorphisms, native braiding naturality, the signed
complex comparison square, invertibility of the K-flat tensor counit, and native
braiding normalization at the complex localization. The main proof cancels the
target model isomorphism and transports the resulting equality from K-flat
representatives to arbitrary unbounded derived objects. Updated the node proof
and declaration proof docstring to record this argument.

## Proved and sorry left

Closed 1 of 1 existing holes:
`CategoryTheory.Functor.exactTensorFunctor_derived_braiding`
(node `lem-sfb-exact-tensor-functor-derived-braiding`).
No holes added or split off. No `sorry` remains in the delivered module.

## No longer needed

Removed the unused proof import `Mathlib.CategoryTheory.Limits.HasLimits`.
Removed the proof import `Sheaf.CategoryTheory.MultivariableDerivedCalculus` and
the proof dependency `lem-sfb-multivariable-derived-calculus`. Its determination
clause is replaced by direct naturality along the K-flat representatives supplied
by the already declared and proved `CategoryTheory.kFlat_derivability`.
This does not withdraw that module or node, which have other users.
No statement imports, declarations, modules, or unit steps were removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's last step used more derived-functor
machinery than necessary: ordinary naturality and the resolution part of its
K-flat derivability dependency suffice. The middle steps can cancel the target
counit alone, without inverting the source counit or the prescribed comparison.
The independent source and target category and localization universes are kept.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
