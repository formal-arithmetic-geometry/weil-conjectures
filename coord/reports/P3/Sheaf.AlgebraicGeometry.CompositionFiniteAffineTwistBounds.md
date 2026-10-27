## What changed

Proved `AlgebraicGeometry.Scheme.Modules.exists_finite_affine_cover_eventually_isAmple_tensorPullback`
in `Sheaf.AlgebraicGeometry.CompositionFiniteAffineTwistBounds`, preserving its signature.
Added proof imports `WeilConjectures.AlgebraicGeometry.AmplePullback` and
`WeilConjectures.AlgebraicGeometry.AmpleIso`.

The proof enumerates Mathlib's finite affine cover by `Fin (Fintype.card s)`, obtains
finite-type and quasi-compact restriction instances from the canonical pullback,
and transports the relative ampleness hypothesis through the explicit isomorphism
between the nested inverse-image scheme and the inverse image of the affine open's
image in Y. Two tensor-pullback composition comparisons identify the relevant
modules. The existing eventual-twist theorem supplies each local bound.
The finite-set construction permits the empty cover, with no nonemptiness assumption.
Updated the existing node's restriction step and proof dependencies to record these
already proved transport tools. No definitions, statements or public imports changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.Modules.exists_finite_affine_cover_eventually_isAmple_tensorPullback`
(node `lem-sfb-composition-finite-affine-twist-bounds`).
No holes remain in the item; no holes were added or split off.
The proof uses the existing theorem
`AlgebraicGeometry.Scheme.Modules.isAmple_tensorPullback_tensorPow_of_relative`
(node `lem-sfb-relative-ample-absolute-twist`), whose existing proof remains `sorry`
in its separate module and is not changed by this delivery.

## No longer needed

None. All five originally planned proof dependencies are used. No modules or nodes
are withdrawn, and no imports were removed. The two new proof imports both supply
lemmas explicitly used in the nested restriction transport. Existing public imports
continue to support the statement's module, tensor and tensor-power interfaces.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The DAG's third step described restrictions as
identical; in Lean the nested open schemes and tensor-pullback modules require explicit
isomorphisms. The implemented proof supplies those comparisons using existing proved
tools, and the node now records them. The original unit route is retained.

Searches: launcher LeanFinder for finite affine covers and relative ample restrictions;
Loogle for `"IsAffineOpen", "map"`; launcher grep for
`isAffineOpen_iff_of_isOpenImmersion|morphismRestrict`; local source searches for
ampleness, pullback composition, invertibility and affine-cover APIs. Mathlib supplies
the cover and morphism permanence; the existing library supplies the ampleness tools.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
