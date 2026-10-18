## What changed

Proved `CategoryTheory.Sheaf.Torsor.etale_pushout_extension` from the categorical pushout
short exact sequence and the universal properties of `ExtensionPresentation` and
`ContractedProductPresentation`. Added two strictly lower split obligations in separate
modules.

## Proved and sorry left

Closed the item theorem `etale_pushout_extension`. The following named obligations remain:
`extension_presentation_shortExact` (node `lem-sc-extension-presentation-short-exact`) and
`extension_presentation_generator_bijOn` (node `lem-sc-extension-presentation-generator-fibre`).

## No longer needed

No proof-dependency imports were removed; the proof uses the recorded pushout theorem,
torsor presentation, and contracted-product presentation.

## Where the brief, the DAG or earlier work was wrong

The item proof plan implicitly requires short exactness and the fibre bijection for every
`ExtensionPresentation`; these were not declarations in the original dependency modules.

## New nodes

`lem-sc-extension-presentation-short-exact` and `lem-sc-extension-presentation-generator-fibre`
are split from the missing Steps 0--3 obligations, with their own modules and source in
Stacks Project Lemma 03AJ. Change record: `coord/changes/proof-imports-etale-torsor-pushout.md`.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
