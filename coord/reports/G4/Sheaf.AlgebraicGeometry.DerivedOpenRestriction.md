## What changed

Proved `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion`
in `Sheaf.AlgebraicGeometry.DerivedOpenRestriction` by specializing the proved source
library theorem `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_etale`.
`IsPullback.of_iso_pullback` uses the chosen isomorphism and both projection equations;
the inferred etale instance for the open immersion supplies the remaining hypothesis.
The canonical exchange map and every existing signature and public import are unchanged.
Added one private proof import, `WeilConjectures.SixFunctors.BaseChange.EtaleDerived`,
and updated the item's node proof, proof dependencies and proof origin to match.
The existing theorem's proof realizes the blueprint's sectionwise comparison, preservation
of injectives under restriction, and bounded-below injective-resolution argument.
The unit `sk-def-sf-operations` has no realized statement or proof steps to bypass.

The module compiled cleanly through `lcompile.py`. Separate `#print axioms` checks of
both the delivered theorem and the source theorem report exactly `propext`,
`Classical.choice`, and `Quot.sound`. The import-direction check permits the new import.
Identity opens, empty opens/schemes, the zero ring and the zero complex require no
extra hypothesis: the source theorem is valid for arbitrary etale base change and
arbitrary commutative coefficient rings, and the square conversion preserves all maps.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMapPlus_of_openImmersion`
(node `lem-weil-pbc-derived-open-restriction`).
No sorry remains in the item. Added 0 holes and 0 split-offs.
This is a proof from a fully proved library theorem, not a decomposition.

## No longer needed

Removed these five private proof imports:

- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`
- `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The proof does not directly use these six former declared proof dependencies:

- `def-weil-pbc-direct-image`
- `def-weil-pbc-inverse-image`
- `lem-weil-pbc-etale-inverse-image-restriction`
- `lem-weil-pbc-etale-site-localization-open`
- `lem-pur-site-restriction-module-adjunction-exact`
- `prop-weil-pbc-kinjective-resolutions-exist`

Their direct uses are replaced by the existing, stronger, fully proved etale
localization exchange theorem (node `lem-weil-pbc-etale-localization-exchange`).
Some definitions and source modules remain transitively necessary to type or prove
that theorem; these are removed direct obligations, not a claim of global unreachability.
In particular neither the generic localized-module exactness theorem nor the full
unbounded K-injective-resolution package is needed as an open obligation of this item.
All three existing public imports remain because this is solely a proof change.

## Where the brief, the DAG or earlier work was wrong

The planned argument is mathematically correct but already implemented in the stronger
source-library theorem above, which is recorded on the existing etale localization
exchange node. Repeating its resolution construction would add unnecessary work.
The original explicit localized-module import is a retired re-export; the dependency
node has since moved to an independent-universe systems interface. This delivery
avoids that interface entirely. No statement or definition repair was needed.

The reused etale localization exchange node is in another unit, but is Lean-closed;
this is specialization of a completed generic tool, preserving the unit route.
There are no new nodes, changed statements, consumer adaptations or change records.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
