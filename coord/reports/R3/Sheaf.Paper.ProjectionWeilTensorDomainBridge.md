## What changed

Completed `WeilConjectures.sfProjectionWeilRationalTensorBridge` in
`Sheaf.Paper.ProjectionWeilTensorDomainBridge`. Private proved helpers identify the
completed rational tensor functor after the ambient constructible inclusion, identify
its Frobenius component, and combine those identifications for arbitrary rational Weil
structure maps. The functor comparison first uses a proved generic lemma for restricting tensor
through full subcategories, then descends from integral arrows by currying and
injectivity of precomposition with raw scalar localization. The component comparison
uses the specified integral normalization and `wfRationalTensorPullback_exists`.
The pure-tensor and pullback-component calculations are proved at a general adic
coefficient datum before specialization, keeping the concrete coefficient constructions
out of repeated kernel reductions.

Added a private `import all Sheaf.Paper.WeilTensorProduct` to use its proved localization
injectivity and pure-tensor lemmas. Existing declaration signatures and public imports are unchanged.

In the unclaimed `Sheaf.CategoryTheory.ScalarLocalization`, named the existing
tensor Hom type `CategoryTheory.ScalarLocalization.tensorHom` and used it in the
category instance's Hom field. Unfolding this reducible alias recovers the old category
verbatim. This avoids repeated expansion of concrete tensor Hom types. The change
record `coord/changes/scalar-localization-tensor-hom.md` lists all 36 explicit search
matches, their holders and effects, plus this item. Consumers need no adaptation.
The existing scalar-localization definition node records the new implementation helper.

Local irreducibility attributes inside the private
normalization section prevent unfolding the large tensor and coefficient-category
implementations; required outer reductions are explicit. The final composition
calculation is proved for arbitrary categories, then for an arbitrary adic coefficient
datum, before specialization. Object equalities are transported through components
with a generic lemma rather than by expanding the concrete tensor functor. Updated the node's
rational proof step to follow this argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfProjectionWeilRationalTensorBridge`
(node `lem-sf-projection-weil-tensor-domain-bridge`).

No holes added or split off. No `sorry` remains in either delivered module. The proof uses
the already stated `wfTensorCompletionFrobenius_exists` comparison package; its
existing upstream obligations are unchanged.

## No longer needed

Removed the unused private import
`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`. The module is not
withdrawn and may still be needed elsewhere. The existing
`Sheaf.Paper.SfWeilSheafComplex` import remains necessary for coefficient-prime
invertibility in the operation-domain clauses.

The rational clause does not need `wfTensorCompletionFrobenius_unique` or the
outer unique-existence wrapper: it uses the existing existence theorem directly.
All other declared proof dependencies are retained. No unit realization is bypassed;
`sk-rem-sf-pf-done` has no separately realized steps. No new intermediate statements are
required.

## Where the brief, the DAG or earlier work was wrong

The node recorded the rational clause as pending. Its integral normalization already
suffices: no integral representative of a rational Weil isomorphism is needed, because
localization precomposition determines the full bifunctor action, while rational objects
retain their integral carriers. The proof keeps the statement unchanged.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
