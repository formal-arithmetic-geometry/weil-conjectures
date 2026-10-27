## What changed

Filled the proof of `scalarTensorPullback_normalization_kFlat` by a representative-square calculation.
Added `ScalarSheafTensorPullback` for ordinary balancing invertibility and its pullback square,
and `UpperStarSingleTensorRepresentative` for the counit square with a degree-zero sheaf.
Added `ScalarTensorRepresentativeCalculus` and `ScalarTensorRepresentativePullback` for proved
representative formulas with an explicit equality transport to the scalar tensor functor.
Added `ScalarRestrictionGeometricRepresentative` for the proved exact restriction square
and `ScalarSheafTensorPullbackComplex` for the proved degreewise ordinary square.
All existing statements and definitions are unchanged. Existing private exact-representative
lemmas are reused through `import all`; no existing dependency module is edited.

The tensor representative is defined through a general categorical construction. The normalization
and cochain-square calculations are first proved with abstract category data, avoiding repeated
unfolding of concrete sheaf instances. The self-contained representative API is then specialized
in its own module.

The cancellation argument transfers invertibility from the source K-flat representative through
the tensor square, avoiding an additional K-flat preservation obligation.

Validation: all seven delivered Lean modules compiled through `lcompile.py`; the final
main-module run passed without warnings and within the enforced per-file limit.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.scalarTensorPullback_normalization_kFlat` (one original hole).
Added: `AlgebraicGeometry.Etale.upperStar_single_tensor_representative`
(`lem-pur-upper-star-single-tensor-representative`, one hole).
This is a decomposition: one hole closed and one strictly smaller tensor counit equation added.
The new equation has no scalar extension, restriction, arbitrary comparison morphism or
representative-normalization hypothesis. The assigned module contains zero holes;
the delivery contains one hole.

Also proved: `scalarSheafTensorMap_isIso`, `scalarSheafTensorPullback_square`,
`scalarCoefficientSinglePullbackIso_eq`, `scalarTensorIso_representative`,
`scalarTensorRepresentative_isIso`, `scalarTensorRepresentative_pullback`,
`scalarRestrictionPullbackIso_geometric_representative`, and
`scalarSheafTensorPullbackComplex_square`
(all in `AlgebraicGeometry.Etale`).

## No longer needed

No original public import is removed: both are needed for the unchanged statement.
The proof does not use the declared `lem-pur-change-of-rings-tensor-comparison`
(`WeilConjectures.Algebra.Homology.ChangeOfRingsTensorComparison`): the ModuleCat-valued-sheaf
balancing map is the existing generic sheafified unit projection, whose invertibility and
monoidal base-change formula give the required ordinary calculation directly.
It does not use `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`): the statement already specifies
the source library's etale tensor comparison, so its defining counit square is the relevant API.
These dependencies are pruned only from this node's proof route; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original proof dependencies describe general ringed-site results, whereas the statement
uses ModuleCat-valued sheaves and a particular existing tensor comparison. The supplied
specialized scalar/tensor normalization and the source library's monoidal-adjunction API
are more direct here. No statement is disputed and no target is changed.

Edge cases reviewed: zero and unbounded complexes, identity pullback, empty schemes, the zero
coefficient ring, and nonflat scalar maps. The ordinary balancing square uses no flatness;
the new tensor counit square is valid for arbitrary complexes and coefficient sheaves.

## New nodes

`lem-pur-scalar-sheaf-tensor-pullback` records the proved ordinary balancing isomorphism and
its monoidal pullback square (parent step 3).

`lem-pur-upper-star-single-tensor-representative` records the remaining tensor counit square
with a coefficient sheaf in degree zero (parent step 2), following Stacks 0FPH. Its ordinary
map and all representative maps are concrete constructions. No data is chosen from existence.

`lem-pur-scalar-tensor-representative-calculus` records the explicit endpoint transport, proved
normalization and K-flat invertibility. It adds no theorem holes.

`lem-pur-scalar-tensor-representative-pullback` records the proved specialization of the general
tensor counit square to the scalar coefficient, with explicit endpoint transports. It adds no
theorem holes.

`lem-pur-scalar-restriction-geometric-representative` records the proved forward form of the
existing exact restriction square. It adds no theorem holes.

`lem-pur-scalar-sheaf-tensor-pullback-complex` records the proved degreewise lift of the ordinary
square, before localization. It adds no theorem holes.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
