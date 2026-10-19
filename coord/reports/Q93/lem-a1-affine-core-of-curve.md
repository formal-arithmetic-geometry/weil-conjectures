## Worker report

The node is recorded as an existing source-library declaration; no duplicate `Sheaf` module is
written.  The exact declaration is
`AlgebraicGeometry.IsCurve.exists_isAffineOpen_dense_finite_compl` in
`WeilConjectures.AlgebraicGeometry.Curve.AffineCore` (the synchronized source file is
`lean/WeilConjectures/AlgebraicGeometry/Curve/AffineCore.lean`).  Its theorem signature is:

```lean
theorem IsCurve.exists_isAffineOpen_dense_finite_compl {k₀ : Type u} [Field k₀]
    {C : Scheme.{u}} (p : C ⟶ Spec (.of k₀)) [IsCurve p] [SmoothOfRelativeDimension 1 p]
    [GeometricallyConnected p] :
    ∃ V : C.Opens, IsAffineOpen V ∧ (V : Set C).Nonempty ∧ Dense (V : Set C) ∧
      (V : Set C)ᶜ.Finite
```

This renders every clause of the node statement: `k₀` is a field; `p` makes `C` a curve via
`[IsCurve p]`; `[SmoothOfRelativeDimension 1 p]` is the smooth curve hypothesis; and
`[GeometricallyConnected p]` is geometric connectedness.  The conclusion supplies an open
`V : C.Opens`, `IsAffineOpen V`, nonemptiness of `(V : Set C)`, density `Dense (V : Set C)`,
and finiteness of the complement `(V : Set C)ᶜ.Finite`.

The dependency `def-sc-curves` uses `AlgebraicGeometry.IsCurve` from
`WeilConjectures.AlgebraicGeometry.Curve`; its declaration is the separated, locally finite
type, quasi-compact curve predicate with `topologicalKrullDim C ≤ 1`, as read from its full
source declaration and docstring.  The dependency `def-weil-pbc-scheme-conventions` is a
convention node and has no declaration of its own; the theorem uses the source-library scheme
and morphism conventions directly.

The source theorem's proof confirms the edge cases used by the statement: geometric
connectedness supplies a nonempty underlying space, relative dimension one rules out
zero-dimensional and empty cases, and the conclusion permits an arbitrary field (not only an
algebraically closed or finite field).  The finite-complement clause is the finite-set form
provided by the canonical theorem; finite type over the field gives the corresponding
finite-over-base interpretation in the source convention.

Searches performed:

- `msearch.py ... leanfinder "affine core of a smooth geometrically connected curve"`: no
  direct Mathlib theorem; only unrelated affine-curve and generic affine-open hits.
- `msearch.py ... loogle "IsCurve, IsAffine, IsOpenImmersion, finite complement, GeometricallyConnected"`:
  no hits (`IsCurve` unknown to Loogle).
- `msearch.py ... grep "exists_isAffineOpen_dense_finite_compl|IsCurve.exists_isAffineOpen" Mathlib/AlgebraicGeometry`:
  no Mathlib hits.
- `rg` over the synchronized project and `dag/lean_names_upstream.json` found the exact
  canonical declaration and its blueprint tag in `WeilConjectures.AlgebraicGeometry.Curve.AffineCore`.
- `scompile.py --source WeilConjectures.AlgebraicGeometry.Curve.AffineCore` retrieved and
  checked the source declaration and signature.

No statement correction, new node, dependency module, or `STATEMENT-DISPUTED` flag is needed.

## Second reading by Q93

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
