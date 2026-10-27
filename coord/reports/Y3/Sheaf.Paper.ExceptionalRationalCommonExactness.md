## What changed

Replaced the proof hole of
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_common_exact_shifts`
without changing its statement or `RationalCommonShiftData`.

The proof localizes each integral left shift using canonical rationalization shifts,
proves normalized finite exactness by the localization precomposition criterion,
and uses `sfLocalizationShiftDescent` to construct the common left shift. It proves
common exactness directly on included finite distinguished triangles. The common
right shift, exactness, unit and counit squares follow from the existing adjunction
and Mathlib's triangulated adjunction API.

Private proved helpers construct an endpoint inclusion correction by the localization
universal property and compute its shift map on integral representatives. A second
proved calculation transports the restriction square from normalized finite shifts
back to the supplied finite shifts. `P.shiftX` and `P.shiftY` make these corrections
independent of compactification. The inverse right restriction square follows from
the existing proved `mate_shift` lemma and the actual descended counit components.
The empty compactification family is handled separately.

Added the proved support module `Sheaf.Paper.ExceptionalRationalCommonShiftTransport`
for the normalization and transport helpers, with the proved public theorem
`commonRationalizationSurjective`. Keeping these helpers separate follows the
60-second-per-file rule after local definition and instance improvements.

Added the proof-only module `Sheaf.Paper.ExceptionalRationalNormalizedScalarShift`.
Its single obligation is the finite scalar comparison square for a family already
normalized by canonical rationalization. It constructs no common-field data and
asserts no exactness or adjunction. Updated the item's DAG proof to this route.
No existing public signature, definition, instance, attribute, or public import changed.
The three files compile individually in import order. With profiling enabled the
proved transport module took 36.2 s and the item took 33.9 s; the new scalar-square
module previously compiled in 9.8 s. Profiling options were then removed. The final
delivery command recompiles and runs the project preflight checks.

## Proved and sorry left

Original holes: one. Its body is now a complete Lean reduction:
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_rational_common_exact_shifts`
(node `lem-sf-rational-common-exact-shifts`).

Added holes: one, exactly
`WeilConjectures.ConstructibleExceptionalCoefficients.rational_common_normalized_scalar_shift`
(node `lem-sf-rational-normalized-scalar-shift`), in the new module.
There are no holes in the item module or in the support module. The support
module proves `commonRationalizationSurjective` and all its private helpers.
This is a decomposition (one upper hole closed, one strictly smaller finite square
added), not a net reduction of the hole count. In particular the endpoint correction,
localization shift construction, finite and common exactness, adjunction shift
construction, and recovery of both supplied restriction squares have proved bodies.

## No longer needed

Removed the unused proof import of `Mathlib.CategoryTheory.Triangulated.Adjunction`
from the support module after the successful check; only the item uses that API.

No original import was removed: the original sole public import of
`Sheaf.Paper.ExceptionalRationalCommonCoherence` remains verbatim.

The item's proof does not use `lem-sf-qbar-localization-exact-descent`
(`Sheaf.Paper.SfQbarLocalizationExactDescent`): the finite-triangle argument proves
exactness directly and needs no extra finite adjunction/unit datum.
It does not use `lem-sf-ring-stage-rational-left-composition` directly
(`Sheaf.Paper.ExceptionalRationalScalarComposition`): shift normalization uses
localization of the integral operation, and the remaining scalar-shift square is
stated separately. That composition result remains needed transitively by the
already constructed common coherence; no withdrawal is requested.
No other module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The rational scalar composition dependency proves tower coherence, not the needed
normalized shift square. The new node isolates precisely that finite square; it
does not repeat the common-field existence statement.

The original proof plan is mathematically usable, but its endpoint-ratio argument
can be implemented by Mathlib's localization universal property, avoiding an
additional descent proof on tensor representatives. Likewise the right scalar
shift family need not be descended separately: the actual common adjunction gives
the right shift and `mate_shift` proves its restriction square.

For elaboration, the normalized finite helpers must take an abstract finite
coefficient field first. Expanding the common-field construction while synthesizing
coefficient-ring instances caused timeouts; specializing the already elaborated
helpers avoids that expansion. No shared definition was changed to address this.

## New nodes

`lem-sf-rational-normalized-scalar-shift`, in
`dag/nodes/sec-six-functors/lem-sf-rational-normalized-scalar-shift.json`, states only
step 2's finite scalar shift square after canonical localization normalization.
The node and theorem docstring give its source and complete localization proof in
words. The zero shift, negative shifts, identity extension, and repeated stages
are included; all use the existing integer shift laws. It is needed only to supply
the transition hypothesis of `sfLocalizationShiftDescent`. The rest of that descent,
the endpoint corrections, all exactness assertions, and the adjunction comparisons
are proved in the item's module. The local-attribute advisory is documented in
`coord/changes/y3-rational-common-proof-settings.md`; there are no forced adaptations.

`lem-sf-common-rationalization-object-surjective`, in
`dag/nodes/sec-six-functors/lem-sf-common-rationalization-object-surjective.json`, is
proved in `ExceptionalRationalCommonShiftTransport`. It records the literal
integral representative used by the endpoint-transport proof. Its proof constructs
the preimage using `integralRepresentative`; this new node adds no hole.

The final delivery attempt initially found a DAG cycle because the representative
node cited the high-level coefficient assembly theorem. Its statement dependencies
now cite the foundational construction and raw-localization data instead; the
mathematics and Lean statement did not change. LeanSearch records were added
alongside the actual Loogle/LeanFinder and source-grep searches. The related-module
check reported `INFRA (73 s)` for the sole direct importer, so no importer pass is
claimed here.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ExceptionalRationalCommonExactness": "b386afb6cc04aea9d331e6e790a80cfa0c9be9c8", "Sheaf.Paper.ExceptionalRationalCommonShiftTransport": "d51fda9aabdee3b5f1de54e096c8f2393cb3f267", "Sheaf.Paper.ExceptionalRationalNormalizedScalarShift": "0e70919e73868b18e6722a269802e053baccb68e"}, "results": {"Sheaf.Paper.ExceptionalCommonStageFromRational": {"hash": "29a9766b30b9457948262ca2451b6bebab4494d2", "status": "INFRA"}}, "seconds": 75, "time": "2026-10-28T05:47:20+0800", "transitive": 0, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
