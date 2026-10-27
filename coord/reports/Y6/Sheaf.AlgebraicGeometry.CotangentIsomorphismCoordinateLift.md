## What changed

Proved `AlgebraicGeometry.Scheme.Hom.exists_compatible_etale_coordinates_of_cotangent_isomorphisms`
in `Sheaf.AlgebraicGeometry.CotangentIsomorphismCoordinateLift`. The supplied-chart theorem
is now placed first so the compatible-chart theorem can use it. Both signatures and all
public imports are unchanged.

Choose a smooth local normal-form chart on the second ambient scheme, and compose it with
the map of affine spaces induced by the target-open inclusion. Base change proves that
this map is étale. Apply the existing supplied-chart theorem. Its functions give the first
chart, and its smaller second ambient open gives the restricted second chart. The two
projection identities follow from `homOfVector_over`, `map_over`, `resLE_comp_ι` and
`homOfLE_ι`; its compatibility equation gives the required equation by associativity.
The dimension, affineness and full inverse-image conditions are retained verbatim.

The original module compiled on the server after this proof change in 5.6 seconds.
The final import cleanup is compiled again by the delivery checks.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.Scheme.Hom.exists_compatible_etale_coordinates_of_cotangent_isomorphisms`.

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.Hom.exists_lift_of_etale_coordinates_of_cotangent_isomorphisms`
(node `lem-trf-cotangent-isomorphism-coordinate-lift`). Its source and six-step proof remain
in its docstring and DAG node. The newly proved theorem uses this stronger existing
statement; it therefore still depends transitively on `sorryAx`. No claim of an axiom-free
compatible-coordinate construction is made.

Added holes: zero. Split-off statements: zero. No definitions were changed or introduced.

## No longer needed

Removed unused private imports:
`Sheaf.AlgebraicGeometry.EtaleAtPointFromDifferentials`,
`Mathlib.AlgebraicGeometry.OpenImmersion`, and `Mathlib.RingTheory.Kaehler.Basic`.
The required open-immersion and étale APIs are already available through the public imports.

No DAG nodes or modules are withdrawn. In particular, the differential-basis theorem,
chosen-coordinate étale criterion and principal-localization facts remain dependencies
of the supplied-chart clause's unfinished six-step argument. Removing its currently unused
private import does not declare that criterion mathematically unnecessary. The DAG retains
those dependencies and records the implemented compatible-chart assembly as Step 7.

## Where the brief, the DAG or earlier work was wrong

No false statement or incorrect proof step was found. The original two declarations permit
a shorter assembly of the first clause using the already-stated stronger second clause.
This is a partial delivery explicitly allowed for a module with several holes; the
supplied-chart construction remains open. The unit statement and route are unchanged.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
