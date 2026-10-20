## What changed

Proved `AlgebraicGeometry.Etale.supportedProductLocalization_openRows` in
`Sheaf.AlgebraicGeometry.SupportedProductLocalization`, without changing any public
signature or definition. The proof constructs the ordinary morphism of support
sequences, derives its three components, and identifies the resulting third component
with the prescribed cut-complement comparison.

Private lemmas prove the needed unbounded boundary naturality from termwise injective
K-injective models. This is necessary because the existing boundary pullback theorem
is stated on bounded-below derived objects, whereas `openRows` is unbounded. They also
identify the independently normalized derived support comparisons using their units.

Added private proof imports for `RightDerivedFunctor.ShortExactPullback`,
`RightDerivedFunctor.MapDerivedComp`, `Sheaf.CategoryTheory.UnboundedInjectiveModel`,
`WeilConjectures.SixFunctors.BaseChange.GlobalSections`, and
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`. These supply pullback
composition, exact-functor comparison, unbounded injective models, the ordinary
restriction square, and preservation of injectives by open inverse image.

The construction applies to arbitrary open immersions and arbitrary unbounded
complexes. It uses no nonemptiness condition on supports or opens, so empty and full
supports and identity and empty open immersions are included.

## Proved and sorry left

Closed one of the five original holes:

- `AlgebraicGeometry.Etale.supportedProductLocalization_openRows`
  (node `lem-pur-supported-product-localization`).

Added zero holes and split off zero statements. Every private helper is proved.
The four original holes below remain unchanged:

- `AlgebraicGeometry.Etale.supportedProductLocalizationFirst_map`
  (node `lem-pur-supported-product-localization-first-map`).
- `AlgebraicGeometry.Etale.supportedProductLocalizationSecond_map`
  (node `lem-pur-supported-product-localization-second-map`).
- `AlgebraicGeometry.Etale.supportedProductLocalization_openFirst`
  (node `lem-pur-supported-product-localization`).
- `AlgebraicGeometry.Etale.supportedProductLocalization_openSecond`
  (node `lem-pur-supported-product-localization`).

This is a partial delivery of a module with several holes, not a decomposition.
The completed row-naturality theorem does not use any of those four unfinished results.

Validation: the complete item module compiled through `lcompile.py`; the final
compile and delivery preflight check the assembled proof. No other library module
is changed.

## No longer needed

None. No existing import, module, declaration, or node is withdrawn. The untouched
exterior-product assertions still need the existing coefficient-Hom and cone-pairing
route. The row-naturality proof follows the existing restriction-of-support-sequences
step directly, so it needs no additional coefficient-pairing dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The bounded-below pullback boundary
API cannot directly prove the unbounded `openRows` statement. Its proof extends using
the existing unbounded injective models and the normalization of the actual support
boundary; the private `boundary_pullback` lemma carries out that extension.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
