## What changed

Proved `CategoryTheory.Mod.exists_kernel_module_structure` in
`Sheaf.CategoryTheory.ModuleObjects.KernelStructure`, preserving its full signature
and docstring from the current tracked scaffold.

The proof implements the five existing steps of `lem-sfb-modobj-kernels`: factor
the action through the underlying kernel, prove the unit and associativity laws
by cancelling its monic inclusion, prove uniqueness of the action, and construct
the linear universal lifts establishing the kernel property in the module category.
No helper theorem, definition, proof dependency, or DAG change was needed.

Removed four redundant direct public Mathlib imports, whose exports remain
available transitively through the retained public import. Change record:
`coord/changes/kernel-structure-imports.md`. No consumer needs adaptation.

The repaired module compiled successfully through `lcompile.py` (1.6 seconds,
exit code 0). The delivery preflight independently checks its axioms.

## Proved and sorry left

Closed `CategoryTheory.Mod.exists_kernel_module_structure`
(`lem-sfb-modobj-kernels`): proved 1 of 1 original sorries.
Added 0; split off 0; remaining 0. This is a complete proof.

## No longer needed

Removed four redundant direct public imports, all publicly available through
`WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian`:

- `Mathlib.CategoryTheory.Monoidal.Mod`
- `Mathlib.CategoryTheory.Preadditive.Basic`
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `Mathlib.CategoryTheory.Limits.Shapes.Kernels`

No mathematical node or module is pruned. The proof uses all three declared
proof dependencies: `def-weil-preadditive-category`,
`def-weil-pbc-additive-functor`, and `sk-def-sfb-module-objects`.
No adopted source-library module changes.

## Where the brief, the DAG or earlier work was wrong

Repaired the landing return for delivery `c5740e69c`: its old base lacked the item
file, which was subsequently created by `45eba2ae8c4`. Read the current tracked
module, applied the complete proof to that scaffold, and replaced the obsolete
source-restoration record with an import-cleanup record describing the actual
current-base changes. This delivery changes the existing theorem's proof; it
does not add or restore the module. Its statement, docstring, DAG attachment,
proof plan, dependency list, unit route, and targets are preserved.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
