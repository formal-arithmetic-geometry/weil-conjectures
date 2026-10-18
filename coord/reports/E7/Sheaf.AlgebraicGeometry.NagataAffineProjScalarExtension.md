## What changed

Proved `AlgebraicGeometry.lem_nagata_affine_proj_scalar_extension`. The proof constructs the
irrelevant-ideal inequality from `hgraded`, forms the canonical `Proj.map`, proves the pullback
square using the existing coefficientwise base-change theorem, and obtains the chart formulas,
cover, and uniqueness from the Mathlib Proj API. Added the proof-only import
`WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor`.

## Proved and sorry left

Closed the module's only sorry, `AlgebraicGeometry.lem_nagata_affine_proj_scalar_extension`.
No sorry remains and no new sorry was added.

## No longer needed

The explicit localization, overlap-cocycle, and scheme-gluing route in the original proof plan
is not needed: the existing `Proj.isPullback_map_of_isGradedBaseChange` theorem packages the
chart pullbacks and gluing. The imports and nodes for the unused explicit chart construction are
therefore not used by this proof beyond the dependency record retained for the statement.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan predates the completed upstream `RelativeProj.Affine` theorem. The shorter
route is valid because the hypotheses `β` and `hgraded` construct its
`GradedRingHom.IsGradedBaseChange` witness directly.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
