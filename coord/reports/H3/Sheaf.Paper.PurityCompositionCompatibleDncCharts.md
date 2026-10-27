## What changed

Replaced the proof hole in
`WeilConjectures.PurityFiniteSetting.compatibleNu_etale_restriction` by an explicit
assembly of ordinary etale base change and ordinary/pro-etale comparison coherence.
All existing public signatures, definitions, attributes and public imports are unchanged.
The private tensor-composition helper was moved before its new use, and a proved
private bifunctor-naturality and inverse-square helpers were added.

Added proof imports of `Sheaf.Paper.StandardSectionPastingBaseChange`,
`Sheaf.Paper.ComparisonTensorPullback`, and
`Sheaf.SixFunctors.ComparisonOpenTensorCoherence`. The last module's proved
`comparison_tensor_compatible` applies to arbitrary morphisms: no open-immersion
hypothesis appears in its signature. The new tensor-coherence module identifies
its comparison with `Dnc.pullComparison`, and cancels the invertible tensor maps.
The item proof then uses naturality of that pullback comparison, naturality of
the comparison tensor, and genuine tensor-bifunctor composition to obtain the
specified two `compatibleStandardPullback` factors.

## Proved and sorry left

The original module had one hole, in
`WeilConjectures.PurityFiniteSetting.compatibleNu_etale_restriction`; its body is
now complete. There are no holes left in that module.

One new hole remains:
`WeilConjectures.PurityFiniteSetting.standardSectionPasting_baseChange`, in
`Sheaf.Paper.StandardSectionPastingBaseChange`, node
`lem-pur-standard-section-pasting-base-change`.
This is precisely the ordinary etale zero-section calculation, with no change
of site or pro-etale tensor constraints. Its docstring and node give the
sigma-base-change, pullback-tensor and mate-pasting proof, including empty schemes
and zero ranks. It is an equality of specified maps, not chosen geometric data.

The new theorem
`WeilConjectures.PurityFiniteSetting.comparisonTensorPullback`, node
`lem-pur-comparison-tensor-pullback`, is fully proved from the existing proved
comparison coherence theorem. Its private comparison-identification lemma and
the item's private bifunctor-naturality and inverse-square helpers are also
fully proved.

Hole accounting: one original hole closed, one strictly geometric hole added,
zero net holes removed. This is a decomposition of the original hole, not a claim
of a completed proof without remaining mathematical obligations.

## No longer needed

None. No original imports, modules, declarations, node dependencies or unit-route
steps are withdrawn. The existing dependencies still support the already proved
chart, tangent, normal, diagonal and DNC parts. No source-library file is changed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The final restriction step in the
existing DAG described both the ordinary geometric calculation and the change
of site at once. The delivery isolates the ordinary calculation and formally
proves the site-transport part. The unit's statement and proof route are preserved.

## New nodes

`lem-pur-standard-section-pasting-base-change` records the remaining ordinary
etale base change of the specified standard zero-section pasting map. Its module
is `Sheaf.Paper.StandardSectionPastingBaseChange`. It is strictly the geometric
part of Step 8; the item contains the separate, fully formal comparison-site
transport and tensor-composition argument.

`lem-pur-comparison-tensor-pullback` records the proved arbitrary-object tensor
square for `Dnc.pullComparison`. Its module is
`Sheaf.Paper.ComparisonTensorPullback`; it uses the already proved general
comparison calculation recorded by `lem-sf-comparison-open-tensor-coherence`.
The parent node's proof, proof dependencies and proof origin were updated.
The six-functor node is used only as a generic comparison-coherence tool: the
smooth-purity unit supplies the geometric route, but has no declaration giving
this arbitrary-object tensor square. No maintainer tool approval is added here.
All three sandbox modules compiled through lcompile. The final main-module check
was clean and took 31.3 seconds; the tensor-coherence module also compiled cleanly.
No profiler settings remain. No definition or statement repair and no change
record is needed.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
