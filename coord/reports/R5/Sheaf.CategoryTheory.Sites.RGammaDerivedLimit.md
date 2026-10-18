## What changed

Proved `CategoryTheory.site_rgamma_derivedLimit` with its original signature and
all existing public declarations unchanged. Added a proved private helper,
`siteModuleDerivedSections_preservesCountableProducts`, in the same module.
No definition or instance was changed.

The helper adapts the existing proved ringed-space product-cone argument in
`Sheaf.Topology.RingedSpaceRGammaDerivedLimit` to independent site, coefficient,
and localization universes. It uses the declared termwise K-injective product
theorem directly. The natural derived unit transports the termwise sections
product cone, and exact products of abelian groups allow localization of that
cone. The main proof uses `PreservesProduct.iso`, checks the transition
endomorphism after every product projection, and transports the image
triangle along the explicit comparison isomorphisms. Functoriality gives the
last projection clause.

Updated the existing node's proof, proof dependencies and proof origin to
record these Lean constructions and the narrower product-only dependency.
All public imports were retained; only proof imports were pruned or replaced.
The module compiles without warnings through `lcompile.py` (about 10 seconds).

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.site_rgamma_derivedLimit`
(node `lem-kun-site-rgamma-derived-limit`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered
Lean module. The private product-preservation helper is also fully proved.
This is a proof from the already declared dependencies, including the
recorded ringed-site K-injective resolution theorem; it does not claim to
close holes belonging to those imported modules. An explicit `#print axioms`
probe reports `propext`, `Classical.choice`, `Quot.sound`, and inherited
`sorryAx`; the probe was removed from the delivered source.

## No longer needed

Removed proof imports:
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: no direct use remains;
  the existing K-injective API and termwise-product theorem supply the proof.
- `Sheaf.Algebra.Homology.KInjectiveProducts`: retired empty compatibility module.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`: replaced with the
  narrower `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.

The proof no longer needs node `lem-weil-derived-limit-existence`, its
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence` module,
or the derived-limit existence, uniqueness and tower-computation portions
of that node. It uses existing node `lem-weil-derived-limit-products-core`
for the termwise product universal property only. Removed the obsolete
`lem-weil-derived-limit-existence` entry from `tool_uses`.

The lower product-core theorem is already recorded as Lean-closed. No
blueprint unit statement or realized step is bypassed (the item's unit
has empty realized statement and step lists). The ringed-space theorem's
module was read for reuse of its proof, and is not imported.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The full derived-limit-existence dependency
was unnecessarily broad: its product-core theorem suffices. The retired
KInjectiveProducts compatibility import supplies no declaration. The
existing declared termwise-product theorem permits reusing the product
construction without repeating the Hom-bijection proof in this module.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
