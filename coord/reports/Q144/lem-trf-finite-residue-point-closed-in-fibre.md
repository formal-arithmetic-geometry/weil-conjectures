## Worker report

The module `Sheaf.TraceFormula.FiniteResiduePointClosedInFibre` states
`AlgebraicGeometry.Scheme.Hom.isClosed_singleton_asFiber_of_finiteDimensional`.
It uses the Mathlib scheme-theoretic fibre `f.fiber (f x)` and its canonical point
`f.asFiber x`. The hypothesis `[LocallyOfFiniteType f]` renders the node's
“morphism locally of finite type” assumption. The explicit hypothesis
`@FiniteDimensional (S.residueField (f x)) (X.residueField x) _ _
(f.residueFieldMap x).hom.toAlgebra.toModule` renders that
`κ(f x) → κ(x)` is a finite field extension, with the algebra induced by the
residue-field map. The conclusion
`IsClosed ({f.asFiber x} : Set (f.fiber (f x)))` says that the point induced by
`x` in the scheme-theoretic fibre is closed.

The proof is postponed with `sorry`, as required for stage 2. Its docstring
records the three source-proof steps: formation of the fibre and base-change
local finite type; the affine-neighbourhood, stalk/residue-field identification,
and finite-type-over-a-field closed-point argument; and the specialization
argument returning global closedness.

Dependency declarations used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and scheme morphisms.
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-scheme-fibre`: Mathlib `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, and `asFiber` from
  `Mathlib.AlgebraicGeometry.Fiber`.
- `def-weil-residue-field`: Mathlib `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` from `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-pc-field-extension`: Mathlib `Algebra` / `FiniteDimensional` encoding of
  a finite field extension.

The proof dependencies are represented by the imports and declarations already
recorded in the DAG: `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange`,
`AlgebraicGeometry.locallyOfFiniteType_iff`,
`AlgebraicGeometry.Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`,
`AlgebraicGeometry.Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField`,
and `AlgebraicGeometry.closedPoint_iff_residueField_trdeg_zero_and_finite`.

Edge cases checked: the fibre may be empty (the singleton conclusion is then
vacuously represented by the canonical point, which exists for every `x : X`);
no nonemptiness or separability hypothesis is added; arbitrary residue
characteristic is allowed; and zero-dimensional and degree-one extensions are
included by `FiniteDimensional`.

Searches made:

- `msearch.py ... leanfinder "finite residue field point is closed in a scheme locally of finite type over a field"`: returned `AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType`, a related Jacobson-space criterion, not this finite-residue fibre statement.
- `msearch.py ... loogle "IsClosed singleton locallyOfFiniteType"`: parser error / unavailable query; no absence conclusion drawn.
- `msearch.py ... loogle "AlgebraicGeometry.isClosed_singleton_iff_locallyOfFiniteType"`: returned the related Mathlib theorem at `Mathlib/AlgebraicGeometry/Morphisms/Finite.lean:221`.
- `msearch.py ... grep "isClosed_singleton_iff_locallyOfFiniteType|isClosed_singleton_of_finite|finite.*residue" Mathlib/`: found only the related Jacobson and finite-type declarations, not the target statement.
- `rg -n "finite.*residue|closed.*fiber|fiber.*closed" WeilConjectures`: found generic finite-residue/closed-point results in `ClosedPoints.lean` and `PointCount.lean`, but no theorem about a point closed in a scheme-theoretic fibre.
- `grep -rn "lem-trf-finite-residue-point-closed-in-fibre" WeilConjectures`: no match.

No existing declaration states this exact relative-fibre result, so a new
statement module was written. No new definition node or dependency module was
needed.

## Second reading by Q144

I reread the node and the module. `f : X ⟶ S` and
`[LocallyOfFiniteType f]` are exactly the morphism and local-finite-type
hypotheses. The point `x : X` maps to `f x : S`; the fibre is exactly
`f.fiber (f x)`, and its induced point is exactly `f.asFiber x`. The finite
extension clause is rendered by the residue-field map's induced algebra and
`FiniteDimensional`, with no separability, nonemptiness, or characteristic
restriction. The conclusion is exactly closedness of the singleton in that
fibre. The module compiled cleanly with `scompile.py`; only the expected
`sorry` proof remains.
