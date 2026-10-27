## What changed

Proved `AlgebraicGeometry.etale_of_faithfullyFlat_fieldExtension` in
`Sheaf.AlgebraicGeometry.EtaleFaithfullyFlatLocal`, preserving its exact signature,
public imports and existing docstring. Added the private proof import
`Mathlib.AlgebraicGeometry.PullbackCarrier` for the image of a map of pullbacks.
All new helpers are private, proved theorems in the item module.

The proof follows the node's two steps. First use
`locallyOfFinitePresentation_near_of_fieldExtension` and choose compatible affine
charts with finitely presented coordinate algebra. Present their base changes as
tensor-product spectra using `pullbackSpecIso`. The pullback range formula lifts
the specified point to the source chart upstairs, and the projection equations
show that its prime contracts to the chosen prime downstairs. Formal étaleness
of the stalk map transfers from the supplied neighbourhood to these charts;
localization identifies it with `Algebra.IsEtaleAt`. Apply
`Algebra.IsEtaleAt.of_fieldExtension`. Finally
`Algebra.exists_etale_of_isEtaleAt` supplies an étale principal neighbourhood;
the open chart and its image identify this with a neighbourhood in the original
scheme. Every chart comparison and localization argument is proved here.

Validation: `lcompile.py` compiled the complete module without errors or warnings
in 16.6 seconds. Source inspection found no `sorry`, admitted private helper,
extra axiom, or changed public signature. The delivery preflight supplies the
independent declaration and axiom probes. The proof assumes no nonempty affine
chart or algebra beyond the designated point; zero rings in unrelated charts
and arbitrary (including inseparable) field extensions are allowed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.etale_of_faithfullyFlat_fieldExtension`
(node `lem-sc-etale-faithfully-flat-local`).

No holes remain in this module. Added zero holes and split off zero theorems.
The proof uses the existing statements
`AlgebraicGeometry.locallyOfFinitePresentation_near_of_fieldExtension` and
`Algebra.IsEtaleAt.of_fieldExtension`; their existing proofs are still `sorry`
in their own modules and are not changed or duplicated by this delivery.

## No longer needed

None. Both existing private dependency imports are used, and all seven declared
proof dependencies continue to serve the existing affine proof plan. No module,
node or public import is withdrawn. Mathlib's global fpqc descent for étale
morphisms was considered, but does not directly turn the neighbourhood of the
single specified point into a neighbourhood downstairs.

## Where the brief, the DAG or earlier work was wrong

No correction was necessary. The existing statements suffice. Mathlib provides
the affine spectrum, localization and open-immersion comparisons needed to
implement the plan, with private proved helpers bridging their interfaces.

The latest blueprint text and the unit record were read. This delivery changes
no unit statement or route. No statement, definition, consumer or DAG dependency
changes are required, and there are no new public declarations or new nodes.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
