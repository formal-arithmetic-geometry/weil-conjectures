## What changed

Proved the restricted affine diagonal coordinate equation by constructing a single
actual Rees-family presentation and applying its normalized DNC reading.

`RestrictedAffineSourceVectorCoordinates` constructs the free bundle, its global
frame, and an initial source presentation by translation of the section to zero.
`VectorSectionReesCoordinates` transports the published standard-pair Rees
isomorphism through that initial presentation. The coefficientwise Rees comparison
is an isomorphism because its Cartesian square has an isomorphism below. Base
change of the free frame then gives a section-preserving constant vector family.
Pullback to the actual fibres supplies the final source and normal presentations,
with their endpoint equations. This avoids a separate calculation at t=1.
`VectorSectionReesReadings` proves the endpoint readings by section-exchange pasting.
The item applies the existing normalized DNC reading and counit naturality, then
uses uniqueness to identify the two presentations of the normalized delta.

The existing helper definition and the item's theorem signature are unchanged.
Only proof imports, private proof helpers, and the theorem proof are added to the
item. Small canonical sheaf-colimit instance caches are scoped to the private
helpers, so the public signature uses its original instances. The normalization
helper is imported through `import all`, with the same private-name mechanism
already used in the library. No other existing module or interface changes.

Validation: all three support modules compile cleanly, and the item compiles
cleanly against the published build in 15.3 seconds. The original helper and
public theorem signature were compared with the repository and are unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.PurityFiniteSetting.restrictedAffineDiagonalDncVectorCoordinates`.
The item has zero remaining holes and this delivery adds zero holes.

The three new public lemmas are also proved:
`affineTowerSection_vectorCoordinates`, `vectorSection_reesCoordinates`, and
`vectorSection_reesReadings`. Their private pullback, naturality and pasting
helpers are proved. All maps and structures have concrete definitions; no data
is selected from an unproved existence theorem in a definition.

## No longer needed

No original public import is removed and no existing node or module is withdrawn.
The original dependencies remain relevant, directly or through the geometric and
normalization steps. The new geometric module does not need the larger
`DeformationSpace.Coordinates` import. The proposed new polynomial-Rees/gluing
obligation is unnecessary: the source library already proves
`Scheme.Hom.isIso_deformationSpaceToAffineSpace`. Its one-fibre formula is also
unnecessary, because the final source presentation is defined by that fibre's
pullback universal property. No trace or integration compatibility lemma is used.
The global `AffineDiagonalDncCoordinateIdentity` is not imported: its presentation
differs and importing it would create a cycle.

## Where the brief, the DAG or earlier work was wrong

No existing statement correction was necessary. The standard-pair Rees
isomorphism was already in the adopted source library. Using its actual fibre
pullbacks closes the geometric step without another split. The proof preserves
the unit route through standard-pair DNC normalization and covers rank zero and
empty bases by the same universal properties.

## New nodes

`lem-pur-restricted-affine-source-vector-coordinates`: the proved global free frame
and initial source presentation, in
`Sheaf.Paper.RestrictedAffineSourceVectorCoordinates`.

`lem-pur-vector-section-rees-coordinates`: the proved geometric family and its
actual endpoint presentations, in `Sheaf.Paper.VectorSectionReesCoordinates`.

`lem-pur-vector-section-rees-readings`: the proved endpoint mate-pasting identity,
in `Sheaf.Paper.VectorSectionReesReadings`.

The item's original node records this proof route. No change record is needed:
all existing statements, definitions, attributes, and public imports are preserved.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
