## What changed

Proved `CategoryTheory.derived_exists_perfectSmallClass_core` by applying the new alpha-compact class core theorem and unpacking its essential-smallness, repleteness, triangulated, coproduct, and presentability clauses. Added the proof-only import of `Sheaf.CategoryTheory.DerivedPerfectSmallClassCoreAlpha`. The new theorem `CategoryTheory.derived_exists_alphaCompactClass_core` isolates the well-generation/cardinal-bound argument that is not available in Mathlib or the existing library.

## Proved and sorry left

The parent theorem `derived_exists_perfectSmallClass_core` is proved. The newly added theorem `derived_exists_alphaCompactClass_core` remains one named `sorry`, representing the Neeman/Krause well-generation and common cardinal-bound argument; its DAG node is `new-sfb-derived-perfect-small-class-core-alpha`.

## No longer needed

No existing imports or dependency nodes were removed. The parent proof no longer directly needs `lem-grothendieck-derived-has-coproducts`; the existing public imports remain because they are part of the module interface and establish the ambient derived-category/coproduct notation used by the statement.

## Where the brief, the DAG or earlier work was wrong

The original parent proof plan compressed the entire well-generation and cardinal selection argument into one step without a Lean declaration. That step cannot be discharged from the currently available APIs, so it was split into the strictly smaller alpha-compact core theorem above. No target statement or existing declaration signature was changed.

## New nodes

`new-sfb-derived-perfect-small-class-core-alpha`: alpha-compact class existence and the cardinal bound for the given essentially small P. The statement is strictly smaller than the parent: it supplies the class as exactly the alpha-presentable objects and separately records that P objects are alpha-presentable. The proof remains the Neeman/Krause well-generation argument.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
