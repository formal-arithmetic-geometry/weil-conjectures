## Worker report

The module `Sheaf.TraceFormula.ReducedCurveNormalizationGenus` states the normalization
formula for a nonempty proper reduced pure one-dimensional scheme over an algebraically
closed field.  Its index `Fin v` is explicitly equivalent to the irreducible components.
Each component is the reduced induced closed subscheme supplied by
`Scheme.IdealSheafData.vanishingIdeal`; `hI` records its integrality so the recorded
normalization declaration can be applied.  The theorem states smoothness, properness and
connected-curve properties of every normalized component, finiteness of the canonical
coproduct normalization, and the cokernel `F` of the canonical structure-sheaf map.  It
also states finite support and the Euler-characteristic formula.  The stalk dimensions
are rendered by the explicit `k`-scalar restriction along the structure morphism's
`ΓAlgebra` and the presheaf stalk.

The hypotheses render as follows: `[Field k]` and `[IsAlgClosed k]` are the algebraically
closed base field; `[X.Over (Spec (.of k))]` supplies the structure morphism; `[IsProper
(X ↘ Spec (.of k))]`, `[IsReduced X]`, and `[Nonempty X]` are the properness, reducedness,
and nonemptiness hypotheses; `hPure : Scheme.IsPureDimension X 1` is pure dimension one.
The component clause is the equivalence `e : Fin v ≃ {Z : Set X // Z ∈
irreducibleComponents X}` and the reduced induced subscheme expression.  The normalized
component clauses use `Scheme.fromNormalization`, `Smooth`, `IsProper`, and
`IsConnectedCurve`.  The global map is `Limits.Sigma.desc` of the component maps and is
required `IsFinite`.  The quotient clause is the cokernel of
`SheafOfModules.unitToPushforwardObjUnit` for that map.  The support clause is
`Set.Finite {y | δ y ≠ 0}`.  The displayed equality uses `Scheme.Modules.eulerChar`,
`Scheme.Hom.genus`, and `∑ᶠ` over closed points; `δ` is definitionally the finite rank of
the quotient stalk after restricting scalars to `k`.

Dependency declarations used:

- `def-pc-euler-characteristic`: `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.Modules.eulerChar`.
- `def-pc-reduced-scheme`: Mathlib `AlgebraicGeometry.IsReduced`.
- `def-sc-curves`: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.IsCurve` / `AlgebraicGeometry.IsConnectedCurve`.
- `def-sc-genus`: `WeilConjectures.AlgebraicGeometry.Curve`,
  `AlgebraicGeometry.Scheme.Hom.genus`.
- `def-sc-normalization`: `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`,
  `AlgebraicGeometry.Scheme.normalization` and `fromNormalization`.
- `def-sc-ringed-space-module-cohomology`: `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology` (recorded dependency interface).
- `def-weil-algebraic-closure`: Mathlib `AlgebraClosure` / `IsAlgClosure`.
- `def-weil-field`: Mathlib `Field`.
- `def-weil-irreducible-components`: Mathlib `irreducibleComponents`.
- `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.IsProper`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `lem-weil-pbc-reduced-induced-closed-subscheme`: `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`,
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.

Edge cases checked against the statement and source: one smooth connected component gives
`F = 0` and `p_a = g`; two disjoint projective lines give `v = 2`, all delta terms zero,
and `p_a = -1`; a cuspidal rational cubic gives one normalization component and one local
quotient contribution; a nodal rational cubic gives the same one-dimensional local
contribution; empty support gives a zero `∑ᶠ`; the empty scheme is excluded by `[Nonempty X]`.
No connectedness or nodality hypothesis was added for `X`.

Searches made before writing: `msearch.py leanfinder` and `leansearch` for normalization
arithmetic-genus and normalization quotient/cohomology formulas (successful searches,
only relative-normalization API hits, verdict no match); `msearch.py loogle` for
`AlgebraicGeometry, normalization` (relative normalization hits only, no match);
`msearch.py grep` for `normalization.*genus|genus.*normalization|deltaInvariant|arithmeticGenus`
in Mathlib AlgebraicGeometry (zero hits); `rg` over `WeilConjectures` and the shared
`lean/Sheaf` tree for normalization/genus and quotient terms (no declaration of this full
formula).  The Mathlib normalization declarations and `Scheme.Hom.genus` signatures were
read in full.  The Q72 stage-1 split and reviewed report were also read; no existing
stage-2 Lean declaration was present.

## Second reading by Q11

I reread the node statement, all eleven statement dependencies, their recorded Lean
interfaces or Mathlib matches, and the completed Q72 stage-1 proof split.  The Lean theorem
binds the base field, algebraic-closedness, scheme-over-base, properness, reducedness,
nonemptiness, and pure dimension hypotheses.  The component equivalence, reduced induced
closed subschemes, componentwise normalizations, finite coproduct map, cokernel quotient,
finite support, and every summand of the formula are present in the signature.  The source's
smooth/proper/connected normalization conclusion is rendered using the existing curve and
normalization declarations; the original scheme remains unrestricted by connectedness or
nodality.  The empty-support and disconnected-projective-line cases were rechecked.  The
file compiles cleanly with `scompile.py`.

## Maintainer review fix

The support clause `Set.Finite {y | δ y ≠ 0}` was weaker than the node's "F is supported on
finitely many closed points": `Module.finrank` is `0` on an infinite-dimensional stalk, and
closedness of the support points was not stated.  The fix adds finite dimensionality over `k`
of every stalk of `F` (implicit in the node's `δ_X(y) = dim_k F_y ∈ ℕ`, proof step 7), which
makes `{y | δ y ≠ 0}` the support of `F`, and the clause `δ y ≠ 0 → IsClosed {y}`.  The rest
of the statement is unchanged; the file compiles cleanly with nt_compile.py.
