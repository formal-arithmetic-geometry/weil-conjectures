## What changed

Constructed the natural restriction map on geometric stalks by the pointed-etale presheaf-fibre colimit. Its representative formula and naturality are proved. Added the strictly smaller support-image statement `properSupport_geometricStalk_image` as the remaining extension-by-zero/support argument, with its proof left as a named split theorem.

## Proved and sorry left

Closed the original hole of `AlgebraicGeometry.Etale.properSupport_geometricStalk` by reducing its second conjunct to `properSupport_geometricStalk_image`. The restriction map construction, representative formula, and naturality compile without sorry. One split theorem remains sorry: `AlgebraicGeometry.Etale.properSupport_geometricStalk_image` (node `lem-cbc-proper-support-geometric-stalk-image`).

## No longer needed

The proof does not use the compactification, proper geometric-point exchange, or extension-by-zero imports from the original DAG route; the explicit map is built from `geometricFibreSectionRestriction` and the pointed-etale colimit. These route nodes remain available to the split theorem but are not needed by the proved part.

## Where the brief, the DAG or earlier work was wrong

The DAG presents the full Stacks Tag 0F76 argument as one Lean theorem, but the library exposes no statement implementing its support-image/extension-by-zero construction. This delivery isolates that argument as a strictly smaller named theorem. The representative restriction and naturality portion is directly formalizable from the existing fibre-colimit APIs.

## New nodes

Change record: `coord/changes/proper-support-geometric-stalk-image.md`.

`lem-cbc-proper-support-geometric-stalk-image` records the remaining support-image and extension-by-zero argument and is declared in the item module.

## Forced adaptations

None.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
