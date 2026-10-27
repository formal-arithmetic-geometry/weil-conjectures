## What changed

Filled `AlgebraicGeometry.Scheme.Modules.flatModulePresentationAfterBoundaryBlowup`
without changing its signature or any definition. The proof follows the existing
four-step route of Stacks 0815, final paragraph, 080Y, third paragraph, and 081N.
It obtains the boundary ideal and density, applies
`moduleAdmissibleBlowupPermanence` for the canonical quotient isomorphism,
finite type, relative flatness and qcqs base, proves compactness and
retrocompactness of the inverse-image open, and applies
`flat_finite_type_dense_presentation`.

A proved private helper transports finite presentation through restriction of
tensor pullback by comparing it with native module pullback, composing native
pullbacks around the restriction square, and using preservation of finite
presentation by native pullback. The proof also explicitly converts finite type
of the ideal module to finite generation of its affine ideals, and converts
scheme-theoretic dominance of a quasi-compact open inclusion to injective
restriction on sections. All additional imports are private proof imports.

The item's node now records these interface arguments and the existing nodes
used for the ideal-module conversions. No other existing module or node changes.

Validation: the complete delivered Lean file compiled without warnings in
28.1 seconds through `lcompile.py`. All four added proof imports passed the
import-cycle check. The original theorem signature is verbatim unchanged and
all Lean lines have at most 100 characters.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Modules.flatModulePresentationAfterBoundaryBlowup`
(node `lem-trf-flat-module-presentation-after-boundary-blowup`).
The private helpers `finitePresentation_restrict_tensorPullback` and
`schematicallyDenseOpen_of_dominant` are also proved.

Original holes: 1. Closed: 1. Holes added: 0. Holes remaining in this delivery: 0.
The proof intentionally uses the existing stated
`AlgebraicGeometry.Scheme.Modules.moduleAdmissibleBlowupPermanence`, whose proof
remains assigned below this item; no dependency theorem is restated or moved.

Edge cases: the construction and pullback comparisons handle empty schemes and
empty opens. For U equal to the whole base the restriction hypothesis applies
everywhere; for U empty, the boundary blowup has empty dense interior, as the
existing density and permanence conclusions require. No compactness of X,
Noetherian assumption, flatness of f, or additional condition on the chosen
boundary ideal is introduced.

## No longer needed

No original imports or dependency nodes are removed. All six originally listed
proof dependencies are used. The finite-affine-cover argument for retrocompactness
is replaced by Mathlib's `IsCompact.isRetrocompact`, which directly expresses
quasi-separatedness of the underlying space. No new retrocompactness lemma,
comparison theorem with a hole, or decomposition module is needed.

The composition theorem `moduleAdmissibleBlowupCalculus` itself is not used;
clause (2) of the same node is supplied by `moduleAdmissibleBlowupPermanence`.
Its module and node remain needed. During development a proof import of
`WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType` was replaced by
the narrower `WeilConjectures.AlgebraicGeometry.FiniteTypeIdealModule`, avoiding
an unnecessary import of the curve divisor development.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The stage-2 signatures use two
finite-type encodings: `IdealSheafData.ofFiniteType` for admissibility and boundary
density, and `I.toModules.IsFiniteType` in this item's interface. The existing
plan did not spell out their conversion. The proof supplies it from the actual
ideal inclusion and affine finite-generation criterion. Likewise, the dense-open
criterion uses `SchematicallyDenseOpen`, whereas boundary density uses
`IsSchemeTheoreticallyDominant`; injectivity of the quasi-compact open inclusion's
maps on sections gives the required conversion. These are proved glue, with no
statement changes or new nodes.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
