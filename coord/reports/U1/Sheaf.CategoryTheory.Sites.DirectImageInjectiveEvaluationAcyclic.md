## What changed

Proved `CategoryTheory.ringedSite_directImage_injective_evaluation_isZero` in
`Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic`, preserving its
existing signature and visibility. The private `mapCech` definition constructs
the image Cech complex from the actual mapped objects, projections and index maps.
Its universal property now uses the existing proved
`CategoryTheory.mapped_product_universal` from
`Sheaf.CategoryTheory.ColimitSiteCechTransport`.

Repaired the return at head 254ffba8d: deleted both duplicated private lemmas
`CategoryTheory.product_ext` and `CategoryTheory.mapped_product_universal` from
the item, imported their original module, and exposed only its existing
`mapped_product_universal` theorem for reuse. Its signature and proof are unchanged;
it has an added source docstring. The original `product_ext` remains private.
The transport module was unclaimed. This visibility change is recorded in
`coord/changes/mapped_product_universal-public-reuse.md`.

The source and image section complexes agree definitionally. The proof uses
`injective_module_cech_cohomology_isZero`,
`Sheaf.isZero_H'_of_siteCech_vanishing`, and
`module_abelian_evaluation_comparison`, together with the proved Ext-to-derived
comparison from `WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections`.
The existing item node records this conversion and the concrete mapped-product
construction, including reuse of the shared theorem. No public import changes.

Compiled both changed modules through lcompile.py, and compiled the existing direct
consumer `Sheaf.CategoryTheory.ColimitSiteCechComplex` unchanged against the modified
transport module. The final delivery preflight checks declarations and axioms.

## Proved and sorry left

Closed the original single hole in
`CategoryTheory.ringedSite_directImage_injective_evaluation_isZero`
(node `lem-weil-pbc-ringed-site-direct-image-injective-evaluation-acyclic`).
The item has zero remaining sorries. Added zero sorries and zero split-off obligations.
The adapted transport module also has zero sorries. This proves the item from its
existing dependencies; `module_abelian_evaluation_comparison` retains its own
separately tracked hole. This repair adds no new mathematical assumptions.

## No longer needed

Removed proof imports `Sheaf.CategoryTheory.SiteCechVanishingCriterion` (retired
re-export; the actual declaration is used from
`WeilConjectures.CategoryTheory.SiteCechVanishingCriterion`) and
`Sheaf.CategoryTheory.SiteCoveringAxioms` (its additional `IsSiteForCoverings`
definition is unused; the existing Precoverage instances supply the hypotheses).
Deleted the two duplicate local helper proofs; their existing shared implementation
is used through its module instead. The colimit-site theorem itself is unused;
only its generic product-preservation helper is used. No mathematical dependency
node from the original plan is discarded. No module is claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The previous attempt reproduced private product-transport lemmas that the library
already proved word for word. Their private visibility prevented ordinary reuse;
this repair makes the needed theorem public at its existing declaration and imports
it, resolving both duplicate-declaration findings in the return.

The plan is correct for empty covering families and degree one. Empty families admit
no tuples in any degree, so the product conditions are vacuous. No nonempty-cover or
nonzero-ring assumption is added. The original DAG omitted the explicit conversion
from Ext-defined `Sheaf.H'` to right derived abelian evaluation. The existing proved
node `lem-sc-site-cohomology-right-derived-sections` supplies it and is recorded in
the updated proof dependencies. The blueprint unit's route is retained.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
