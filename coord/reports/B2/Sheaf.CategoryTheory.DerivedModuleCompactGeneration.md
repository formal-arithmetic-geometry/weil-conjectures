## What changed

Restored `lean/Sheaf/CategoryTheory/DerivedModuleCompactGeneration.lean` from its
quarantine attachment after the upstream sync. The existing theorem signature and
proof are preserved. The module compiles against the current source library and its
rank-one properties dependency.

## Proved and sorry left

No new `sorry` remains in this module. The declaration
`CategoryTheory.derivedModuleCompactGeneration` is proved by the existing singleton
family argument from `CategoryTheory.derivedModule_rankOne_properties`.
That lower declaration remains a named dependency and is outside this delivery.

## No longer needed

None. The module's proof uses the rank-one compactness and weak-generation result and
the coproduct singleton construction; no imports or DAG dependencies were pruned.

## Where the brief, the DAG or earlier work was wrong

The upstream sync quarantined this module because the global tree had an import
collision involving older `Sheaf.CategoryTheory` copies. The current source-library
boundary requires preserving this attachment. With the current imports, the restored
module compiles in isolation and in the sandbox import closure.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
