## What changed

Proved `CategoryTheory.exact_unit_derived_total_square` from the existing normalized
`nonnegative_derived_totalization` comparisons and the functorial cosimplicial injective
replacement theorem. Added proved private helpers for localization naturality, unit descent,
finite-summand extensionality, beta naturality and composition, and exact postcomparison
naturality and composition. All existing signatures and definitions are preserved.

The proof-only import of `LocalizedModuleExactForSystems` is replaced by
`CosimplicialInjectiveTotalReplacement`. The node proof now records the implemented argument.

## Proved and sorry left

Closed: `CategoryTheory.exact_unit_derived_total_square` (one original hole).
Added holes: none. Remaining holes in this delivery: none.
The existing imported comparison and resolution theorems retain their own proof obligations.
The complete item compiled through `lcompile.py`; the final delivery runs the required
consumer, declaration, node and independent-reader checks.

## No longer needed

Removed the proof-only import `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
The generic theorem already quantifies over every exact postcomposition, so its proof does
not instantiate slice-module restriction. Therefore `lem-pur-site-restriction-module-adjunction-exact`
and `def-pur-localized-ringed-site` are not proof dependencies, and the obsolete tool-use entry
is removed. The public imports and statement dependencies are preserved.
The additive/left-exact conventions of `def-sp-left-exact-additive` are supplied by the
existing instance hypotheses and need no separate proof dependency. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The proof needs the full functorial resolution theorem for the simultaneous augmented
replacement square; the weaker individual `augmentedReplacement` field alone does not
record a map between both replacements. The existing declared cosimplicial replacement
theorem supplies exactly the required common resolution functor.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
