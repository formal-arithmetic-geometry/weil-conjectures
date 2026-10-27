## What changed

Proved `AlgebraicGeometry.Scheme.finitePerfectAdic_etale_level_descent` without changing
its signature, definitions, or public imports. Its proof first converts the given
termwise models to exact derived constant realizations, descends the quotient, checks
bounds and finite local constancy on the model cover, and takes the geometric stalk
of a covering model. A supplied constant model pulls back along any further chart,
giving the required transport field.

Added three proved helper modules under `Sheaf.Paper`: `FiniteCoefficientDerivedConstantCoordinates`,
`FiniteCoefficientSliceDerivedCoordinates`, and `FinitePerfectChartEtaleOrigin`.
The first cancels actual derived scalar extension against restriction by uniqueness
of left adjoints. The second constructs the fixed-scalar slice equivalence and its
derived comparison. The third applies finite-model heart descent and bounded derived
origin, and reflects arbitrary supplied constant models. It requires neither a compact
base nor a bounded algebraic model in its comparison conclusion.

## Proved and sorry left

Closed the original single hole in
`AlgebraicGeometry.Scheme.finitePerfectAdic_etale_level_descent` (1 of 1).
Added no holes and split off no unproved statements. All private helpers are proved.
The three new public theorems are proved:

- `AlgebraicGeometry.Scheme.finiteCoefficient_derived_constant_coordinates`;
- `AlgebraicGeometry.Scheme.finiteCoefficient_slice_derived_coordinates`;
- `AlgebraicGeometry.Scheme.finitePerfectChart_etale_origin`.

There are no `sorry` declarations left in any delivered module. Existing dependencies
are used as library declarations; this count does not claim to close their remaining
obligations.

## No longer needed

No original Lean imports were removed: the item originally imported only its data module,
which its statement still needs. Removed the exploratory
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso` import
from the new constant-coordinate module; its proof uses localization and the
constant-sheaf comparison instead. No existing module or declaration is withdrawn.

The item's proof no longer needs `lem-weil-pbc-finite-ring-constructible-derived-origin`
(`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`): the local models directly give
finite constant cohomology, and bounded etale origin is obtained using
`etale_origin_of_finite_models` and `plusEtaleOrigin_of_etaleOriginHomology`.
It also does not need `lem-weil-pbc-completed-constant-sheaf-reduction`
(`Sheaf.Paper.CompletedConstantSheafReduction`): the actual scalar-extension adjunction
and inverse restriction equivalence give the constant comparison at this single level.
Neither dependency is declared globally unused, since other consumers may retain it.

Weakly etale localization and site comparison remain needed indirectly in the new
coordinate/origin helpers. Their dependencies are recorded there instead of as direct
proof dependencies of the item. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The existing `finiteCoefficient_etale_slice_origin` theorem has a `[CompactSpace X]`
parameter, absent from the assigned statement. The new origin proof uses local model
covers and bounded comparison, so no compactness assumption is added and no shared
interface is changed. Ringed restriction in the statement uses chosen complex
representatives; the proof explicitly compares it with the exact derived restriction
using `Q.objObjPreimageIso` and the derived factorization isomorphism.

The statements were checked against the empty-chart and zero-ring cases. Coordinate
comparison and scalar cancellation require no nonemptiness, finiteness or bounds.
In the origin theorem a possibly unbounded supplied algebraic complex is handled by
reflecting bounds of its constant sheaf realization, rather than assuming bounds of
the algebraic complex itself. A covering chart over the specified geometric point
supplies the small perfect fibre.

## New nodes

`lem-weil-pbc-finite-coefficient-derived-constant-coordinates` records the natural
constant-complex comparison. Its proof uses exact inverse scalar restriction,
uniqueness of derived left adjoints, the module-sheafification unit, and localization.
It is fully proved in `FiniteCoefficientDerivedConstantCoordinates`.

`lem-weil-pbc-finite-coefficient-slice-derived-coordinates` records reflection of slice
isomorphisms under the fixed-scalar coordinate equivalence, together with the proved
constant comparison. It is fully proved in `FiniteCoefficientSliceDerivedCoordinates`.

`lem-weil-pbc-finite-perfect-chart-etale-origin` records only etale origin and reflection
of constant models from the local bounded perfect charts. Bounds, finite local
constancy and the perfect geometric fibre required by the item are assembled in the
item itself. It is fully proved in `FinitePerfectChartEtaleOrigin`.

No change records are needed: the existing changes are confined to the item's proof,
its proof imports, and its own node's proof route; the other modules and nodes are new.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
