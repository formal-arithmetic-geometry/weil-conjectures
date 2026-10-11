## Worker report

The module `lean/Sheaf/AlgebraicGeometry/GenusWellDefined.lean` states
`AlgebraicGeometry.genus_well_defined`. It renders the hypotheses as a field `k`, a
scheme `X : Scheme.{u}` with `[X.Over (Spec (.of k))]`, the smooth-projective-curve
structure on the structure morphism `(X ↘ Spec (.of k))`, and geometric irreducibility
of that same morphism. The conclusion is
`FiniteDimensional k (Scheme.Modules.H (SheafOfModules.unit X.ringCatSheaf) 1)`, which
is the finite-dimensional interpretation of `dim_k H^1(X, O_X) < infinity`. The
structure sheaf is `SheafOfModules.unit X.ringCatSheaf`; `Scheme.Modules.H ... 1` is
its first sheaf cohomology object. The proof is `sorry`, as required for stage 2.

The dependency declarations used are:

- `def-pc-smooth-projective-curve`: `AlgebraicGeometry.Scheme.Hom.IsSmoothProjectiveCurve`,
  imported from `Sheaf.AlgebraicGeometry.SmoothProjectiveCurve`.
- `def-pc-geometrically-irreducible`: Mathlib's
  `AlgebraicGeometry.GeometricallyIrreducible`, imported from
  `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`.
- `pqf-def-cohomology`: the cohomology notion is rendered by
  `AlgebraicGeometry.Scheme.Modules.H` from `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`.
- `def-weil-vector-space-dimension`: finite-dimensionality is the standard
  `FiniteDimensional` predicate (dimension itself is Mathlib's `Module.finrank`).

Edge cases checked: `u` is shared by `k` and `X`, so the scalar field acts on the
cohomology object without an independent universe mismatch; `p = 1` is explicit; the
empty scheme is excluded by the curve structure's integral/nonempty conditions; no
algebraic-closedness assumption is added, matching the node.

Searches made: `rg` over `WeilConjectures` and `lean/Sheaf` for genus, arithmetic genus,
`finiteDimensional_H_of_isCurve`, and structure-sheaf cohomology; these found the
related sorry-backed `AlgebraicGeometry.finiteDimensional_H_of_isCurve` and the
recorded cohomology infrastructure, but no exact theorem for this node. The node's
recorded Lean searches (LeanSearch, Loogle, and grep) likewise report no exact match;
Mathlib's `GeometricallyIrreducible` and `Module.finrank` are exact dependency matches.
Compilation with `scompile.py` succeeded with no errors or warnings beyond the expected
`sorry` declaration warning.

## Earlier second reading (a previous round; superseded)

Checked the signature against the node clause by clause and verified the dependency declarations and universe levels. The module compiled remotely; the stage-2 preflight signature and branch metadata are now aligned.

## Second reading by P1

The node introduces a field `k`, a scheme `X` over `Spec k`, a smooth-projective-curve
structure on the structure morphism, and geometric irreducibility of that morphism. Its
single conclusion is finite-dimensionality over `k` of first cohomology of the structure
sheaf. The Lean binders render these objects exactly:

- `(k : Type u) [Field k]` is the base field, with the same universe as `X`;
- `(X : Scheme.{u}) [X.Over (Spec (.of k))]` is the scheme over the field;
- `[Scheme.Hom.IsSmoothProjectiveCurve (X ↘ Spec (.of k))]` is the recorded smooth,
  projective integral curve condition;
- `[GeometricallyIrreducible (X ↘ Spec (.of k))]` is Mathlib's geometric
  irreducibility predicate on that structure morphism;
- `FiniteDimensional k (Scheme.Modules.scalarCohomology (f := X ↘ Spec (.of k))
  (SheafOfModules.unit X.ringCatSheaf) 1)` is the finite-dimensional `H^1(X,O_X)` clause,
  with the scalar action restricted from global sections along the structure morphism.

The prior module used `Scheme.Modules.H`, which is the abelian-sheaf Ext construction,
not the O_X-module cohomology named by `pqf-def-cohomology`. I changed it to the recorded
`Scheme.Modules.scalarCohomology`, whose underlying object is
`RingedSpace.moduleCohomology` with the canonical k-module structure, and added the
existing dependency node `def-sc-field-linear-module-cohomology-operations`. No other
hypothesis or clause changed. The empty scheme remains excluded by the curve instance;
`n = 1` is explicit; no characteristic or algebraic-closedness hypothesis is added; and
the shared universe covers the field-extension edge cases.

Searches of Mathlib, `WeilConjectures`, and `lean/Sheaf` found no exact genus theorem.
They did find the existing `Scheme.Modules.H` Ext construction and the recorded
`RingedSpace.moduleCohomology`/`scalarCohomology`; the latter is now used. The corrected
module compiles cleanly with `scompile.py`, with only its intentional `sorry`.
