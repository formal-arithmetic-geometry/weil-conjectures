## What changed

Proved both remaining theorems of `Sheaf.Paper.ScalarModelFiniteFlatResolution`.
The DVR proof constructs a scalar presentation using `Submodule.basisOfPid`, proves
exactness of the actual independent-coefficient constant and scalar-extension
functors, transports the presentation to finite powers of the sheaf unit, and
constructs its augmentation as a quasi-isomorphism. The existing
`FiniteFreeResolution.finiteFreeResolution_tensor` supplies K-flatness and the
derived tensor comparison; additive tensor functors carry the same double
complex and differential to the stated tensor complex.

The field proof maps `Module.finBasis` through the scalar-model functor and uses
`FiniteFreeResolution.finiteFree_iso_augmentation`. All glue is proved in private
helpers. Existing public signatures, definitions, and public imports are preserved.
The node proof and dependency list now describe this route. New helper instances,
opens, and elaboration options are scoped to a private-helper section or a single
theorem; no global instances are added. The required command-scope change record
is `coord/changes/J3-scalar-model-proof-scopes.md`.

The first delivery compiled successfully but preflight required that change
record for the added commands. This packet supplies it and localizes the helper
instances. The public theorem signatures and public imports were also compared
textually with the base and are unchanged.

## Proved and sorry left

Closed 2 of the 2 original holes:

- `SheafOfModules.scalarModel_finite_flat_resolution_dvr`.
- `SheafOfModules.scalarModel_finite_free_field`.

No holes remain in the item; no holes were added or split off. The delivery
compile and 12-public-declaration axiom probe succeeded before the scope cleanup;
the only subsequent rejection was a warning about proposition-valued `def`s,
which are now private theorems with local instance registrations. The existing
finite-free tensor declarations are used as stated, as required by stage 3;
their pre-existing holes are not closed or newly introduced by this delivery.

## No longer needed

Removed the proof imports:

- `Mathlib.CategoryTheory.Abelian.FunctorCategory` (already publicly available).
- `Mathlib.CategoryTheory.Sites.Sheafification` (already publicly available).
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`.

The last three are no longer direct dependencies: the stated finite-free tensor
comparison packages the needed homological input. The proof does not import
`Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension` or use node
`lem-sfb-constant-finite-free-presentation-extension`: exactness and the unit/power
comparisons are proved directly for the independent-coefficient functor in this
item. No module is withdrawn; other consumers may still need these modules.

Removed the obsolete direct `tool_uses` entries:
`lem-weil-pbc-site-r-module-presheaf-sheafification-exact`,
`lem-pc-bounded-above-flat-kflat-site`, `lem-pc-kflat-resolution`,
`lem-weil-pbc-site-derived-tensor-descent`, and
`lem-pur-kflat-tensor-quasiiso-independent`.
Exact sheafification is used through the existing Mathlib instances, and the
homological results are packaged by the retained finite-free tensor dependency.
The scalar-resolution Mathlib leaf and finite-free tensor node remain needed.
The already proved independent-coefficient tensor-colimit node is also recorded
for its `siteSheafTensorRightIso` presentation used in transporting the differential.

## Where the brief, the DAG or earlier work was wrong

The planned constant-extension declaration uses coefficient universe `max u v`
and the `constantModuleHomFunctor` presentation. The item has independent
coefficient universe `r` and its own existing constant-module presentation, so
that declaration does not directly apply. Its held module is untouched; the
necessary exactness and finite-power comparisons are proved here without
changing any interface. The existing tensor helper's augmentation clause uses
its own presentation of the two-term complex; an explicit augmentation and the
proved additive-functor double-complex isomorphism retain precisely the
`HomologicalComplex.double` required by this item.

Rank zero is covered by the empty categorical product and its zero-object
property. The DVR flatness hypothesis is used to preserve the scalar short exact
sequence; the field case only maps an isomorphism and does not use flatness.
No target, unit route, statement, or definition was changed. No new nodes and
no forced adaptations were needed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
