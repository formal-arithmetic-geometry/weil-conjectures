## What changed

Completed both theorem proofs in `Sheaf.CategoryTheory.LocalCoefficientLocalization`.
`localCoefficientRestriction_exact` transfers finite-limit and finite-colimit preservation
through the definitional comparison with abelian-sheaf restriction. The multiplication
naturality theorem uses the existing `PresheafOfModules.sectionsSMul_naturality` lemma.
Added proof-only imports for the sheafification preservation and continuous-site
restriction instances. Updated the item's DAG proof and proof origin to record this route.

## Proved and sorry left

Closed `CategoryTheory.localCoefficientRestriction_exact` and
`CategoryTheory.localSectionMultiplication_naturality`. The module contains zero `sorry`s;
no new holes were added.

## No longer needed

No proof-dependency modules were needed: `proof_deps` is empty. The original public imports
remain necessary for the definitions and derived-category construction. No DAG modules were
proved or imported solely for the abandoned plan.

## Where the brief, the DAG or earlier work was wrong

The item's DAG had an empty proof plan even though the restriction exactness follows from
the existing abelian-sheaf restriction and sheafification preservation instances. No
statement or definition was changed.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
