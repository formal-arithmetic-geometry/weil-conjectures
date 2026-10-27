## What changed

Filled `AlgebraicGeometry.isIso_of_finite_birational_normal` in
`Sheaf.AlgebraicGeometry.FiniteBirationalNormalIso`, preserving its statement and all
public imports. Added the private proof import
`Mathlib.RingTheory.LocalProperties.IntegrallyClosed`.

The proof follows Stacks Tag 0AB1 and the existing three-step DAG plan. On each
nonempty affine target open, the target section ring is integrally closed by
`IsIntegrallyClosed.of_localization_maximal` and the affine stalk localization
identification. Transporting the source germ map backwards along the given
function-field ring equivalence gives an injective algebra map into the target
function field. Finiteness makes its image integral, so integral closedness gives
surjectivity of the section map; compatibility of germs gives injectivity.
The empty-open case uses the zero section rings. The affine section-map criterion
and locality of isomorphisms on the target complete the argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isIso_of_finite_birational_normal`
(node `lem-trf-finite-birational-normal-iso`).

No holes remain and no holes were added. No split-off statements or new modules.

Validation: the complete module compiled cleanly through `lcompile.py` in 7.1 seconds.
The original declaration signature and public-import list were checked verbatim.

## No longer needed

None. All existing public imports are retained. The proof uses the existing DAG
proof dependencies (integral schemes, function fields, finite morphisms, normal
rings, affine function-field fractions, affine stalk localizations, finite
algebras being integral, and the local criterion for integral closedness).
No nodes or modules are withdrawn or bypassed, and the unit route is unchanged.
The proved source-library normal-sections theorem was considered during search;
the direct Mathlib localization argument keeps the existing dependency route.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface correction was necessary. The theorem is proved
with its original hypotheses and conclusion. The domain part of `hnormal` is
already supplied by integrality; retaining it preserves the original signature.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
