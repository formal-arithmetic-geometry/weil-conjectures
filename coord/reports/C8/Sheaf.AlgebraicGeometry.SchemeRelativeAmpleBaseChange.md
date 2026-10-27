## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isAmple_on_affineOpens_tensorPullback_baseChange`
in the assigned module, following all five steps of Stacks Morphisms Tag 0893 and
its DAG plan. A proved private helper handles one subordinate pair of affine opens:
restrict the pullback square with `Scheme.Hom.isPullback_resLE`, apply affine pullback
of ampleness, and transport across the tensor-pullback composition isomorphisms.
The main proof derives quasi-compactness, constructs the cover indexed by all such
pairs, and applies `scheme_relative_ample_affine_cover`.

Added the private proof import `WeilConjectures.AlgebraicGeometry.AmpleIso` and recorded
its already proved node `lem-sc-ample-iso` in the item's proof dependencies. Updated
the item's node to describe the Lean implementation. No signature, definition, public
import, shared module, or unit route changed. Empty schemes and empty members of the
cover are allowed: the cover argument is pointwise and makes no nonemptiness assumption.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.isAmple_on_affineOpens_tensorPullback_baseChange`
(node `lem-trf-scheme-relative-ample-base-change`).

Added 0 holes; split off 0 statements. The item's module has 0 remaining `sorry`s.
The private helper `isAmple_restricted_baseChange` is fully proved. The proof uses the
existing stated affine-cover criterion; it does not claim to close that dependency's hole.

Validation: `lcompile.py` compiled the complete module successfully in 4.5 seconds,
with exit code 0 and no diagnostics. The new AmpleIso import passes the import-cycle
check. The public theorem signature is byte-for-byte unchanged.

## No longer needed

Removed private imports `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`. Quasi-compactness is proved
using Mathlib's affine-open criterion directly. The upstream `nonempty_tensorPullbackComp`
already supplies the composition comparisons needed here; their normalization on
sections is irrelevant to transport of ampleness. Neither removed module is withdrawn.

No mathematical node of the original five-step plan is pruned. In particular
`def-pc-module-pullback` is still used through the existing tensor pullback and its
composition comparisons. No other module is claimed to become globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG omitted the explicit isomorphism-invariance
lemma used to implement its module-identification step; `lem-sc-ample-iso` now records
that dependency. The existing normalized-adjunction import was stronger than needed.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
