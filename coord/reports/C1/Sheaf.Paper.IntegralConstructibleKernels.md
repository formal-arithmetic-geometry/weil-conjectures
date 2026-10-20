## What changed

Restored Sheaf.Paper.IntegralConstructibleKernels from its rework.tsv quarantine archive.
Added public import Mathlib.CategoryTheory.ObjectProperty.Kernels, the defining module of
ObjectProperty.IsClosedUnderKernels used in the existing public theorem's statement.
Every other archived line, including the complete kernel proof, is unchanged.
Change record: coord/changes/C1-integral-constructible-kernels-public-import.md.
The existing DAG attachment, proof steps, dependencies and unit route remain unchanged.

Validation: the restored module compiles cleanly on the compile server (28.1 seconds;
23.9 seconds when compiled for the consumer check). A separate public-consumer module
imports only this module, names ObjectProperty.IsClosedUnderKernels, and applies
integralConstructible_kernels; it compiles cleanly in 1.8 seconds. The consumer opens
the existing CategoryTheory.Obj and CategoryTheory.Functor scopes for their instances.
The recorded dependency signatures were read; LeanFinder, Loogle and grep searches found
no direct replacement theorem. The repair needs no replacement proof route.

## Proved and sorry left

This is a zero-hole interface repair. The archived item has zero sorry occurrences;
the repaired item has zero. Holes closed: none (0 of 0). Holes added: none (0).
No statement was split off. integralConstructible_kernels retains its existing complete
proof from integralMatrix_pivot_cover and the recorded local-presentation dependencies.
No claim is made that those dependencies are globally axiom-free.

## No longer needed

None. No import, declaration, node, dependency or quarantined module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The module already had a complete proof; its assigned rework defect is public visibility
of the kernel-closure class following source synchronization. The quarantine archive is
preserved and restored, rather than treated as an unused or withdrawn module.
The original module relied on a private transitive import for a public signature.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
