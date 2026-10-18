## What changed

Filled both proofs in `Sheaf.CategoryTheory.NormalizedDerivedComparisonCommonResolution`.
The first proof expands the existing canonical resolution comparison to obtain
`c_w = RF(Q(r(u))) ≫ c_v` and `c_u = RG(Qu) ≫ c_id` on homs. Naturality of
`r.mapDerivedCategoryFactors.inv` and `β.hom` then transports the comparison from
N to J. Cancelling `c_w` reduces the result to the supplied normalization at J, v.
The transition proof substitutes this result for both inverse arrows, expands the
existing transition definition, and cancels the resolution and endpoint isomorphisms.

No signatures, definitions, visibility, imports, or other modules changed. The original
four-step DAG plan and the unit route are preserved, so no node update is required.

Validation: `lcompile.py` compiled the complete module with no errors or warnings
in 5.5 seconds. Read Stacks `derived.tex`, `lemma-K-injective-defined` (Tag 070Y),
and the existing resolution definitions. LeanFinder and Loogle searches returned
objectwise injective-resolution naturality and exact-functor localization APIs;
none replaced this supplied normalized comparison theorem.

## Proved and sorry left

Closed 2 of 2 original holes:

- `CategoryTheory.Functor.normalizedDerivedComparison_commonResolution`.
- `CategoryTheory.Functor.normalizedDerivedComparison_commonResolution_transition`.

Both belong to node `lem-sf-normalized-derived-comparison-common-resolution`.
Zero holes remain in the item; zero holes added; zero statements split off.
This is a proof of both declarations using the existing resolution constructions,
not a decomposition. The existing dependencies still have their own open theorems.

## No longer needed

No imports, nodes, or modules pruned: both existing public imports occur in the
unchanged statements and definitions. The proof uses the resolution-map and transition
constructions directly, so it does not require the holed map-computation, functoriality,
transition-computation, transition-laws, or transition-naturality theorems of
`Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`. That module remains necessary
for `kInjectiveDerivedResolutionTransition`, and both declared dependency nodes remain
used exactly as in the DAG plan.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface errors found. No K-injectivity of rJ is assumed or used.
No definition or statement repair, forced adaptations, or new nodes were needed.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
