## What changed

Replaced the hole in
`AlgebraicGeometry.ProEtale.CondensedRing.profinite_coefficient_slice_base_change`
by the unbounded derived lift of an ordinary coefficient comparison. The original theorem
statement and all existing definitions are unchanged. Private proved helpers compare functors
on a resolving localization, descend cochain transformations through the homotopy quotient,
and transport K-flatness along a ring-sheaf isomorphism.

The proof imports the existing exact slice restriction/K-flat theorem, flat scalar restriction,
the explicit tensor comparison, and the existing resolving localization theorem. The only
new module, `Sheaf.AlgebraicGeometry.ProfiniteCoefficientSliceOrdinary`, states the remaining
ordinary comparison. The argument combining it with the existing declarations is complete
Lean: the two cochain counits become isomorphisms on resolving objects and their ratio descends
by fully faithful localization whiskering.

## Proved and sorry left

Original holes closed: one,
`AlgebraicGeometry.ProEtale.CondensedRing.profinite_coefficient_slice_base_change`.
Holes added: one,
`AlgebraicGeometry.ProEtale.CondensedRing.profinite_coefficient_slice_ordinary`
(node `lem-zl-profinite-coefficient-slice-ordinary`). No holes remain in the assigned module.
This is a decomposition (net zero holes), not a fully sorry-free proof of the mathematics.
The remaining statement has no complexes, derived functors, resolving classes, or localization
in its conclusion. It is strictly the ordinary tensor/sheafification part of the original
argument; the entire unbounded derived lifting step is proved in this delivery.

## No longer needed

No original imports were removed. The original direct dependency
`lem-weil-pbc-ringed-pullback-preserves-kflat` is unnecessary: the more specific, already proved
`lem-sfb-ringed-site-restriction-kflat`, followed by scalar transport along an isomorphism,
supplies precisely the K-flat preservation needed. Its module
`Sheaf.Paper.KFlatRingedToposPullback` is not imported.

The original direct dependency `lem-pc-kflat-resolution` need not be imported separately:
`lem-weil-pbc-site-derived-tensor-descent` already gives the localization by resolving
objects, which is sufficient. Resolution theory remains needed inside that existing theorem;
this delivery does not claim to prune it from the whole library.

The original ordinary dependencies `lem-weil-pbc-site-constant-restriction` and
`lem-pur-sheaf-ring-coefficient-ordinary-adjunction` belong to the new ordinary node,
rather than being direct proof dependencies of the parent. Neither is globally pruned.
No modules are withdrawn, and the unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan used a general ringed-topos pullback result
where exact restriction to a slice and scalar transport along a ring isomorphism suffice.
The existing derived-descent theorem also eliminates the need to construct resolutions and
prove naturality on roofs again in this module. The ordinary step still needs both the
coefficient-ring identifications and compatibility with the actual internal-module mapMod;
a scalar-only or constant-module-only comparison would not suffice.

## New nodes

`lem-zl-profinite-coefficient-slice-ordinary` states the ordinary coefficient-extension
comparison (original proof steps 1-2), for the ordinary functors of the fixed cochain models.
Its source and complete balanced-tensor/sheafification argument are recorded in both the
module docstring and the node. Searches of Mathlib and the whole blueprint found no identical
comparison. Edge cases include zero coefficients and the empty profinite slice. No existing
public interface is changed, so no change record is needed.

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
