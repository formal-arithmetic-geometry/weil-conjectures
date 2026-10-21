## What changed

Filled the nine theorem proofs in `Sheaf.CategoryTheory.CommonStageKaroubiInverse`.
The inner Karoubi transitions, comparisons and transformations use Mathlib's
`functorExtension₂`; their coherence follows by naturality and idempotence.
Private helpers make the fixed-stage map to the canonical quotient a functor,
restrict a local component isomorphism to a projector, and identify the descended
component and its transported representatives. The final theorem follows the
node's ten steps, including both Karoubi layers and presentation conjugation.
All existing statements, definitions and public imports are preserved.

## Proved and sorry left

Nine original holes closed:
- `CategoryTheory.CommonStage.localInverse_extension_additive`
- `CategoryTheory.CommonStage.Diagram.innerUnit`
- `CategoryTheory.CommonStage.Diagram.innerLeft`
- `CategoryTheory.CommonStage.Diagram.innerRight`
- `CategoryTheory.CommonStage.Diagram.innerPentagon`
- `CategoryTheory.CommonStage.Family.innerCoherent`
- `CategoryTheory.CommonStage.innerCompatible`
- `CategoryTheory.CommonStage.innerRestriction_formulas`
- `CategoryTheory.CommonStage.commonStage_inverse_through_karoubi`

All realize `lem-sbc-common-stage-inverse-through-karoubi`.
No holes added, no split-off statements, and no remaining sorry.

## No longer needed

None. Both original public imports are used, and all declared proof dependencies
remain needed. The proof follows the existing node route and preserves the unit
route. No modules or DAG nodes are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The canonical descent structure exposes
all required quotient composition, identity, equality and transformation formulas.
The proof uses its existing specification; it does not select arbitrary data from
an unproved existence theorem. Invertibility is used only at the specified raw
object. The projector calculations include zero and identity projectors; the
stage formula includes the repeated stage; presentation conjugation holds for
any isomorphism.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
