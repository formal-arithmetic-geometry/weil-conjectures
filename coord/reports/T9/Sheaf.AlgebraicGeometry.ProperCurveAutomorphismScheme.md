## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.exists_proper_curve_automorphism_scheme` in
`Sheaf.AlgebraicGeometry.ProperCurveAutomorphismScheme`, preserving every existing
public signature and definition. Added only proved private helpers.

The proof represents the separated dimension-at-most-one space by a scheme using
`SeparatedSpaceDimensionOneScheme`. It proves the represented-point homeomorphism
and transfers separatedness, local finite type and universal closedness to that
scheme. Proper-curve projectivity and `ProjectiveCurveIsomGraphs` then provide the
representing scheme. An explicit slice representation, the iterated-slice
equivalence and Yoneda identify its automorphisms multiplicatively with the stated
presheaf automorphisms. An evaluation formula proves compatibility with the stated
base-change operation. Finally `GrpObj.ofRepresentableBy` constructs the group
object and its multiplication formula proves the representing equivalences are
group isomorphisms.

Added proof imports for the scheme representation, binary-product preservation,
cartesian slice categories, and the already proved source-library field-base-change
dimension bound. Updated the existing node's proof route, dependencies and origin.
No source-library file was changed. No statement or definition repair was needed.
The file compiled through `lcompile.py`; delivery performs the final checks.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.AlgebraicSpace.exists_proper_curve_automorphism_scheme`
(node `lem-sfb-proper-curve-automorphism-scheme`).

The item has zero remaining `sorry` declarations. Added zero holes and split off
zero statements. Every private helper is proved or has fully constructed data.
The proof uses the existing declared scheme-representation, projectivity and
Isom-graph results; their existing proof obligations remain their own items.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.DimensionExtension` and the
item's proof dependency and obsolete `tool_uses` approval
`lem-kun-dimension-extension`. Its field-extension normal-form result is unnecessary:
`AlgebraicGeometry.topologicalKrullDim_pullback_le_of_field` from the already proved
`WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension` supplies precisely the
geometric-fibre upper bound for any field-valued point. The node records this
field-base-change route under `lem-pc-dim-base-change`.

The group-space-to-scheme result Stacks Tag 0B8F is unnecessary: the existing
projective Isom-graph theorem gives a scheme directly. All other planned proof
dependencies remain used, either explicitly or through Mathlib instances. No
module is withdrawn, and no adopted source declaration is removed.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect definition was found. The proof plan omitted the
formal bridges from a representing presheaf isomorphism to scheme-level properness
and point topology, and from scheme automorphisms to the literal slice restriction
in the statement. These bridges are now fully proved private helpers.

The published Mathlib convenience isomorphism for a represented group presheaf
requires the presheaf values to share the hom-set universe. Here the presheaf
automorphisms live in a larger universe. `GrpObj.ofRepresentableBy` itself supports
that universe, so the proof uses it and checks the multiplication equation directly.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
