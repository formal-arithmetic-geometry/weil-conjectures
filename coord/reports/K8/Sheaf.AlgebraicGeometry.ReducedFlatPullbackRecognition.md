## What changed

Proved `AlgebraicGeometry.reduced_flat_pullback_recognition` in
`Sheaf.AlgebraicGeometry.ReducedFlatPullbackRecognition` without changing its signature
or public imports. The proof uses the existing base-change ideal-image theorem,
flat-pullback exactness, and reduced-induced uniqueness. It explicitly compares the
two chosen adjunctions by `leftAdjointUniq`; naturality shows that precomposition by
an isomorphism relates their ideal maps and preserves the image. An isomorphism to
the kernel ideal then proves injectivity on every open. The support equality uses
`Scheme.Pullback.range_snd`, `support_ker`, and closedness of the original image.
Updated the item's proof, proof dependencies and proof origin to match this Lean proof.
Server validation: `lcompile.py` compiled the final file cleanly in 5.1 seconds
(exit 0). The declaration signature was checked byte-for-byte against the original.

The source statements were checked against Stacks Schemes Tag 01JU
(`lemma-fibre-product-immersion`) and Tag 01J3 (`lemma-reduced-closed-subscheme`).
The argument handles the empty closed subscheme and does not assume reducedness of
T or Y; reducedness is used precisely on the pullback in the uniqueness theorem.
No shared definition, interface, existing dependency node or adopted source file changes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.reduced_flat_pullback_recognition`
(node `lem-trf-reduced-flat-pullback-recognition`).
Zero holes remain in the item; zero holes are added or split off.

## No longer needed

Removed the proof import `WeilConjectures.AlgebraicGeometry.Modules.VeryAmple` and
its associated planned proof dependency `lem-pc-closed-imm-base-change`. The attachment
only supplies `IsVeryAmple.pullback_of_field`, which is unnecessary for this proof.
Removed that obsolete node from the item's `tool_uses` list. The correct existing
ideal-image and flat-exactness declarations replace this planned dependency.
No module is withdrawn; this report makes no claim that the very-ampleness module
is globally unused. The existing base-change-image and reduced-induced nodes remain
needed. All remaining proof imports are used. Public imports retain their visibility.

## Where the brief, the DAG or earlier work was wrong

The planned flat clause of `lem-pc-closed-imm-base-change` does not occur in its
recorded Lean attachment: `IsVeryAmple.pullback_of_field` only establishes stability
of very ampleness under field extension. The needed general image formula already
exists as `closedSubscheme_baseChange_ideal_image`; flat exactness already exists as
`flat_module_pullback_exact_pushforward_injective`. Their structure-map adjunction
choices require the explicit naturality calculation supplied in this proof.
The mathematical statement and unit route are unchanged. No new nodes are needed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
