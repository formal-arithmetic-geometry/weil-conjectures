## What changed

Proved all four theorem holes in `Sheaf.Paper.PurityFrameClass`, preserving every existing
signature and mathematical construction. A proof-only import of
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionBaseChange` supplies
`Scheme.isPullback_zeroLocusSubschemeι_union`. The range of the tuple is the union of the
prefix range and last singleton, so that theorem gives the intersection isomorphism;
monicity gives uniqueness. `choose_spec` gives its defining equation.

For the empty tuple, the identity factors through its zero subscheme, proving its immersion
is invertible. The proved private helper `frameCoefficientRestriction_isIso` identifies the
specified coefficient restriction with the canonical sheafification comparison, rather
than merely constructing some isomorphism between the objects. Integer cast simplification
proves degree addition.

Profiling found expensive kernel reduction of degree-zero derived objects. The new generic
`frameSingleTensorMap` keeps the named single functor as a parameter until a proved equality
identifies it, and `frameTensorNext` specializes this same canonical tensor map.
`frameFold` similarly keeps the dependent result family abstract while implementing the
identical `Nat.rec`; `frameBoundaryProduct` specializes that recursor.
`frameSingleUnit` substitutes the zero-twist coefficient equality in the sheaf category
before mapping the inverse coefficient restriction and applying the zero-shift comparison.
Explicit source and target objects avoid inference-driven unfolding in `frameEmptyClass`.
`frameCupSheaves` calls `supportedCup` with explicitly constructed bounded-below objects,
whose underlying objects are precisely `(cupSingle P X).obj F` and its analogue for `G`.
These are definitionally equal presentations of the original constructions; every existing
signature, coefficient map, shift convention and public import is unchanged. The tensor/cup
revision compiled without errors or warnings in 38.6 seconds. The added fold wrapper
compiled in 48.7 seconds, with one unused binder warning now corrected.
A scratch check against the published definitions proved both changed constructions
definitionally equal to their originals by `rfl` (44.4-second compile). The fold also
passes a `rfl` equality check against the published recurrence (31.4-second compile).
The empty product also passes its `rfl` equality check against the published construction
(19.2-second compile). The complete final variant passed the delivery compilation and
axiom probe. The required dry run passed compilation and preflight
(commit `40544c9201`, review class CODEX).

The change record is `coord/changes/K6-purity-frame-class-elaboration-scheduling.md`.
Elaboration is scheduled sequentially within this file (`Elab.async false`), without
changing its output or importer options. No downstream module needs adaptation. The
proof-only import passes the import-cycle check.

## Proved and sorry left

Closed four original holes, all attached to `def-pur-frame-class`:

- `WeilConjectures.PurityFiniteSetting.frameIntersection_existsUnique`
- `WeilConjectures.PurityFiniteSetting.frameIntersectionIso_over`
- `WeilConjectures.PurityFiniteSetting.frameEmptyRestriction_isIso`
- `WeilConjectures.PurityFiniteSetting.frameDegreeNext`

Zero holes remain in the item; zero holes were added or split off. The private helper and
the generic tensor, unit and fold constructions are complete. This is a proof, not a
decomposition.

## No longer needed

None. No imports, nodes or modules were removed. All existing construction dependencies
remain necessary for the frame class. The source-library pullback theorem avoids a new
affine quotient or gluing lemma; none was added.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The existing source-library zero-locus union theorem
already proves the geometric intersection assertion needed here. The empty-tuple argument
also covers the empty scheme, and the intersection argument includes `d=0`. No mathematical
construction, existing public interface, blueprint unit or planned unit step was changed.

Continuation metadata: the sandbox reference start changed from `1792426207.5458171` to
`1792437810.7406821` during provider-error resumptions. The worker did not edit `.budget` and
retained the original session deadline.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
