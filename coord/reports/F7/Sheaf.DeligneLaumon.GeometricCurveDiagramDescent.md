## What changed

Replaced the hole in `AlgebraicGeometry.WeilSheaf.exists_geometric_curve_diagram_descent`
by a proof in the source pro-etale Weil category. The diagram is obtained by the explicit
`poweredGeometricPullback` functor: the existing power functor followed by inverse image with
the displayed Frobenius commutation. Its construction contains no postponed data.
The new functor definitions have an irreducible boundary; consumers use their proved carrier
equations, exactness, generic named cokernel comparison and simplicity-transport API.
`exactFunctorCokernelIso` is the standard Mathlib comparison with abstract category data;
its irreducible boundary avoids the kernel repeatedly expanding the concrete Weil functor.
The proved `exists_poweredGeometricPullback` interface returns this very functor with
its defining equality and exactness. The final proof uses that interface to keep the
construction abstract, uses explicit equality transports for the stalk formulas and identifies only the
marked-point images. The generic composite-restriction and isomorphism lemmas keep
the model and cokernel data abstract when transporting simplicity.
Exactness preserves both monomorphisms and supplies the cokernel isomorphism. Geometric
simplicity reflects across the curve isomorphism and implies arithmetic lisse simplicity.
The source theorem `FrobeniusModule.IsReal.of_charpoly_eq_pow` supplies all reality implications.

Added `PoweredGeometricPullback`, `MarkedGeometricCurveModel`, and
`PoweredGeometricPullbackStalk`. The marked model data are bundled in
`MarkedGeometricCurveModel`, so the dependent field and scheme instances are shared during
kernel checking. The marked model uses the already proved
`exists_smooth_closed_curve_finiteField_model`; it does not choose a curve from a new hole.
The single-object stalk theorem isolates the local Frobenius calculation for an explicit
functor, independently of curves, diagrams, irreducibility and reality. Updated the item's
proof dependencies to match this route. The original theorem signature is unchanged.

Validation: `lcompile.py --all` compiled all four delivered modules cleanly, with no warnings.

## Proved and sorry left

The original hole in `exists_geometric_curve_diagram_descent` is closed by a complete Lean
combination. Its replacement local comparison
`AlgebraicGeometry.WeilSheaf.poweredGeometricPullback_stalk`
(node `lem-zl-powered-geometric-pullback-stalk`) remains `sorry`.
The item has 0 holes remaining, down from 1; the added modules have 1 hole in total.
This is a decomposition of one hole into one strictly smaller hole, not a net hole closure.
`AlgebraicGeometry.exists_marked_geometric_curve_model` is proved from the existing model theorem.
All constructions, exactness instances, carrier equations, preservation of lissity,
geometric-to-arithmetic simplicity, and reflection of geometric simplicity along an
isomorphism in `PoweredGeometricPullback` are proved.

## No longer needed

The item's source had no proof imports to remove. The new functor module drops the unused
`WeilConjectures.WeilSheaf.LisseLocus` and
`WeilConjectures.WeilSheaf.UpperStarExact` imports and keeps exactness, filtration and reflection
imports private. The main module also drops its redundant direct
`LisseFiltration`, `UpperStarPointwise` and `StalkIso` imports, already public
through `RealCurve`, and its direct
`Adic.IrreducibleLisse` import, now used only by the functor API. The marked model drops direct
`Noetherian`, `Morphisms.Smooth` and `Geometrically.Integral` imports already public
through `RealCurve` or its geometric-model dependency. The local comparison needs no direct
geometric base-change import. This proof does not use these planned
common-stage dependencies:

- `lem-zl-constant-extension-weil-heart-equivalence`,
  module `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`: the source power and inverse-image
  functors construct the needed Weil diagram directly.
- `lem-zl-classical-weil-filtration-heart-transport`,
  module `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport`: exact source pullback supplies
  the monomorphisms and actual cokernel without common-stage heart transport.
- `lem-zl-curve-restriction-filtration-spectrum`,
  module `Sheaf.Paper.CurveRestrictionFiltrationSpectrum`: the required remaining comparison
  is isolated for one explicit source object, and reality follows from the proved source
  polynomial-power lemma.

These are removed from this item's proof route, not withdrawn from the library; other
consumers still require them. In particular, the filtration-transport node remains a
realization of the unit's first step; this item performs the third-step curve restriction
and does not remove that realization or its other imports.
`lem-zl-geometric-closed-curve-smooth-model` remains needed
through the marked-model theorem. The unit's two-point curve-restriction route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned common-stage lemmas are stated in a different category from the source Weil
sheaves appearing in the item. Applying them would require a comparison not supplied by
those signatures. The source category already supplies the power functor, exact adic
inverse image and reality under polynomial powers, so this delivery constructs the needed
source functor and does not assume a common-stage equivalence.

The finite-field model theorem uses a subfield of the original closure, while the source
stalks use a separate `AlgebraicClosure` of each base field. The marked-model theorem records
this closure comparison and both projection squares explicitly. Coincident marked points
are permitted. The stalk statement permits zero sheaves, arbitrary rank, nonsemisimple
Frobenius and repeated images; the residue exponent is independent of the sheaf.

## New nodes

`def-zl-powered-geometric-pullback` records the explicit source-category functor, its exactness,
lissity and simplicity API in `PoweredGeometricPullback`. The object is a real composition
of existing functors, with no existence theorem choosing unspecified data.

`lem-zl-marked-geometric-curve-model` records the scheme-only finite-field model comparison
in `MarkedGeometricCurveModel`, built from the already proved geometric model theorem.
It contains no sheaves, local representations, diagram or reality assertion.

`lem-zl-powered-geometric-pullback-stalk` records the single-object local calculation in
`PoweredGeometricPullbackStalk`. It is the only added hole: the functor, map, base fields
and their compatibilities are inputs, and only the residue-degree and stalk calculation
remain. Its docstring supplies the complete natural-language point-transport argument.

No existing definition or statement was changed, and no change record or forced consumer
adaptation is required.

## Second reading by F7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
