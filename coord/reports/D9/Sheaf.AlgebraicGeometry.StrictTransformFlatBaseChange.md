## What changed

Proved `AlgebraicGeometry.Scheme.IdealSheafData.strictTransform_flat_baseChange`
without changing its signature. Two proved private helpers supply quasi-compactness
from the declared finite-centre theorem and compare preserved-open kernels in a
cartesian square. The main proof constructs and verifies both pullback squares,
uses the existing flat-image kernel theorem, and cancels pullback along the
canonical blowup isomorphism. Only the item module and its proof-node copy change.

The node route and theorem docstring describe this direct kernel argument.
Validation: the complete proof compiled cleanly through `lcompile.py` in 3.7 s,
with exit code 0 and no warnings. The delivery tool performs the final compile and
axiom preflight on the submitted packet.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.IdealSheafData.strictTransform_flat_baseChange`.
Holes closed: 1 of 1. Holes added: 0. Holes remaining in this module: 0.
No split-off statements or definitions were added. The proof still uses the existing
`AlgebraicGeometry.finiteCenterOpen_closure_kernel_data`, whose proof is `sorry`;
this delivery proves from that declared dependency as requested.

## No longer needed

Removed the private import `WeilConjectures.Blowup.Complement`: its complement
isomorphism is unnecessary for a kernel argument.

Bypassed `lem-trf-blowup-base-change-preserved-open-diagram`, module
`Sheaf.AlgebraicGeometry.BlowupPreservedOpenDiagram`: the two cartesian squares
and preserved-open equations are constructed directly with pullback pasting and
restriction, using the already proved canonical blowup comparison.

Replaced the density-only route `lemma-nagata-dense-flat-pullback` with the existing
more directly applicable node `lem-sfb-scheme-image-flat-base-change`. Both attach
to the same proved source-library kernel theorem; no new import is needed for this
replacement. The quotient, density, intersection, recognition and ambient-kernel
clauses of `lem-trf-finite-center-open-closure-kernel-data` are not used; its
quasi-compactness clause remains necessary. No modules or declarations are withdrawn.
All public imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The older plan was longer than needed:
the source library already provides flat base change for arbitrary quasi-compact
scheme-theoretic image kernels (`Scheme.Hom.ker_of_isPullback`), including the
ambient image of the preserved open. There is therefore no need to construct the
base-changed closed subscheme and prove its density separately. The generic-point
hypothesis is unnecessary but remains unchanged, as required. The unit record
`sk-i-curve-zero` has no realized entry requiring either bypassed auxiliary node.

Checked degenerate centres I = 0 and I = O_X, empty schemes and opens, nonreduced
schemes, and arbitrary non-quasi-compact bases: the kernel comparison retains the
scheme structure and requires only quasi-compactness of the relevant open inclusions,
which follows from finite type of the centre. There are no additional hypotheses.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
