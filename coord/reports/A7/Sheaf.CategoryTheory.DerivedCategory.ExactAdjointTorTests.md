## What changed

Proved `CategoryTheory.ExactAdjointTorTests.exact_adjoint_derived_tor_tests`
without changing its signature or any definition body. The proof follows all four
steps of `lem-sf-exact-adjoint-derived-tor-tests`: naturality of the transported
unit, tensorator and counit gives joint projection naturality; naturality of alpha
and `mapDerivedCategorySingleFunctor` gives the heart comparison square; inverse
cancellation and tensor bifunctoriality give the specified comparison square;
`mapDerivedCategoryHomologyFunctorIso` and preservation of zero objects transfer
the same interval. All calculations apply to unbounded derived objects and also
to an empty interval (a > b).

Replaced the unused public open-normalization import with the exact-derived
functor and degreewise-adjunction modules actually needed by the existing public
definitions. The cohomology comparison remains a private proof import. See
`coord/changes/exact-adjoint-tor-tests-imports.md`; no consumers require adaptation.
The DAG's mathematical proof, dependencies and unit route already describe this
proof exactly, so no node change is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.ExactAdjointTorTests.exact_adjoint_derived_tor_tests`
(node `lem-sf-exact-adjoint-derived-tor-tests`). Added 0 holes. No sorry remains
in the item and no new module or theorem is added.

The complete proof with the final pruned imports compiled through lcompile.py
in 2.2 seconds with no errors or warnings. The delivery checks also compile the
packet and inspect declaration axioms.

## No longer needed

Removed `Sheaf.SixFunctors.OpenTensorNormalizationData` from this module's public
imports. Its open-immersion data and normalization theorems are unused by this
abstract argument. Its existing declarations remain intact for other consumers;
this delivery removes only the import edge. The definition-node dependency
`def-weil-exact-derived-adjunction` is retained mathematically: the item-owned
universe-generalized `exactDerivedOfUniverses` is the same specified localization
construction, using `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`.

No stated proof dependency or unit step is pruned. Both exact-functor nodes are
used, through `mapDerivedCategorySingleFunctor` and
`mapDerivedCategoryHomologyFunctorIso`. No new resolutions or K-flat lemmas are
needed, because invertibility of the canonical projection is already assumed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original public open-normalization import was
unnecessarily broad. Library search found a related projection comparison in
`WeilConjectures.PoincareDuality.Abstract`, but its stated naturality covers only
the second variable; a direct unit/tensorator/counit calculation proves the needed
joint square without importing that additional module. The DAG's four-step plan
works as stated, including the unbounded cohomology comparison.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
