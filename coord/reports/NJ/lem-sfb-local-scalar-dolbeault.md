## Worker report

The delivery states the unchanged node in two named theorems in
`Sheaf.Analysis.Complex.LocalScalarDolbeault`: `ComplexManifold.local_scalar_dolbeault`
and `ComplexManifold.scalar_dolbeault_zero_iff_holomorphic`. Both proofs are `sorry`.
All definitions have explicit data. The additional definition module is
`Sheaf.Analysis.Complex.ScalarDolbeaultForms`.

Clause-by-clause correspondence:

- Usual real and complex fields: Mathlib `ℝ`, `ℂ`, including their `Field` instances,
  use the `Field` match of def-weil-field. The full class signature and docstring in
  Mathlib.Algebra.Field.Defs were read.
- Dimension `n ≥ 0`: `(n : ℕ)`, with no positivity assumption. Complex Euclidean space
  is `Fin n → ℂ` with its usual normed space structures.
- Open domain: `U : Set (Fin n → ℂ)` and `hU : IsOpen U` in both theorems.
- Prescribed point: `a : Fin n → ℂ`, `ha : a ∈ U` in local exactness. The degree-zero
  assertion is a statement on all of U, with no unnecessary chosen point.
- The increasing wedge indices are precisely `Fin q ↪o Fin n`; a coefficient family
  `ScalarAntiholomorphicForm n q U` is a function from those indices to `U → ℂ`.
  Thus there is no ambient extension data or identification of boundary values.
- Smoothness of each coefficient is `IsSmoothScalarForm α`, expanded as
  `∀ J, ContDiffOn ℝ ∞ (scalarCoefficientExtension U (α J)) U`. On open U this is
  exactly ordinary real smoothness of the function on U. The zero extension is
  unconstrained at the boundary and smoothness is tested only at interior points.
- `scalarDolbeault` uses the existing `ComplexManifold.wirtingerBarPartial` from
  `Sheaf.Geometry.Manifold.KahlerCoordinateData`. Its full signature and docstring,
  and `realCoordinateVector`, were read: it is `(D_x + i D_y)/2`, within U.
  In the coefficient of an increasing tuple K, the term differentiating the tuple
  with its r-th entry deleted has sign `(-1)^r`. This is the sign for moving the
  newly prepended `dbar z_(K r)` past r entries. Repeated indices contribute zero.
- Every positive degree is expressed as `q + 1` for `q : ℕ`, so its predecessor is
  exactly q, avoiding truncated subtraction. `hclosed : scalarDolbeault α = 0`
  tests every coefficient and point on U.
- The conclusion existentially quantifies V, its openness and `hVU : V ⊆ U`, then
  requires `a ∈ V` and a degree-q β on V. It requires `IsSmoothScalarForm β` and
  the exact equation `scalarDolbeault β = restrictScalarForm hVU α` on V.
- For degree zero there is exactly one increasing empty tuple J. The second theorem
  says `scalarDolbeault α = 0 ↔ ∀ J, DifferentiableOn ℂ (extension (α J)) U`.
  This is exactly the kernel criterion for the single scalar function coefficient;
  holomorphicity on an open set is complex differentiability throughout that set.
  The extension has no effect on the germ at any point of U.

Dependency interfaces: `Field` (Mathlib.Algebra.Field.Defs),
`ComplexManifold.wirtingerBarPartial` (Sheaf.Geometry.Manifold.KahlerCoordinateData,
recorded on def-sfb-kahler-coordinate-data), and the new coefficient-form declarations.
Plain proof imports are Mathlib.Analysis.Calculus.DifferentialForm.Basic
(`extDeriv_extDeriv_apply`, recorded mathlib match of
lem-sfb-chart-exterior-derivative-square-zero),
Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
(`differentiableAt_iff_restrictScalars`, recorded match of
lem-sfb-real-derivative-complex-linear), and
Sheaf.Analysis.Complex.CutoffCauchyTransform
(`Complex.exists_cutoffCauchyTransform_parameters`). Their signatures and docstrings
were read; there is no extra analytic solvability hypothesis. The theorem docstrings
carry the full descending-coordinate proof and the real-to-complex derivative argument.

Source verification: downloaded Demailly's agbook.pdf into this sandbox and read the
coordinate decomposition and CR criterion, printed p.24; Lemma (3.29), printed pp.28--29;
and Exercise 8.5, printed p.61. These give the exact scalar smooth specialization used.
The Exercise writes the highest differential on the right; the node and our proof put
it on the left, and consistently use that convention in both decomposition and primitive.
The local result translates the prescribed point to zero. No statement correction or
STATEMENT-DISPUTED issue was found.

Edge cases: n=0 permits the unique empty coordinate vector. Positive-degree index types
are empty and all forms vanish. When q>n, injectivity of an order embedding rules out
any index and the form space has one element, so zero β suffices, including the top-degree
primitive case. Degree zero has a single empty index and hence one scalar coefficient.
For n=1, the one-form coefficient has dbar equal to zero automatically; the conclusion
is the genuine local inhomogeneous CR solution. For a two-index coefficient the formula
is `∂bar_(K 0) α_(K 1) - ∂bar_(K 1) α_(K 0)`, checking the wedge sign. Empty U has no
chosen point for exactness; the degree-zero equivalence is vacuous on both sides.
Disconnected domains are allowed, and no compactness or global exactness is asserted.

Searches: msearch LeanFinder with the local closed scalar-form query returned
Complex.IsExactOn, holomorphic primitive theorems, extDeriv_extDeriv, and harmonic
one-variable results, none the Dolbeault assertion. msearch LeanSearch with
"Smooth scalar zero q differential forms and their antiholomorphic Dolbeault derivative
in complex coordinates" returned exterior-derivative facts and unrelated conformality
and algebraic Kaehler differentials. msearch Loogle `"Dolbeault"` returned zero hits.
msearch grep `Dolbeault|Wirtinger|barPartial|antiholomorphic` returned four conformality
comments. `rg -n` on WeilConjectures for the item id and those patterns gave no matching
coordinate notion. `rg -n` on Sheaf found the Hermitian manifold forms and the existing
Wirtinger operator, which we reused. The upstream-name index has no new declaration
name collision. DAG definition-id searches found only def-sfb-hermitian-dolbeault-data
among Dolbeault/antiholomorphic/differential-form definitions. `blueprint_refs.py search
Dolbeault` returned zero blueprint nodes; `search scalar` returned 310 unrelated
coefficient and scalar-functor nodes. `blueprint_refs.py ancestor` reports None for this
inherited node; the new node preserves its inherited ancestor chain.

Validation: scompile.py compiled each of the two files separately against the published
live library, with no errors or non-sorry warnings (about 1.3--1.4 seconds per file).
All variable binders are explicit and there are no new universe parameters, local
notations, local instances, private definitions, or diagnostic commands.

## New nodes

`def-sfb-scalar-dolbeault-forms` defines the coordinate coefficient representation of
scalar (0,q)-forms, its smoothness predicate, domain restriction, and actual Dolbeault
coefficient formula, from Demailly I §3.C (3.14)--(3.17). The existing Hermitian forms
are real alternating tensor fields on arbitrary manifolds with a separate metric and
operator structure; they do not give the increasing-index scalar coefficient family
on an arbitrary open subset, or construct this differential. In particular imposing
DolbeaultOperators would assume square-zero data before constructing this operator.
The new node imports and cites def-sfb-kahler-coordinate-data for the already defined
Wirtinger derivative, rather than duplicating it. The three Mathlib search kinds and
project/DAG searches are recorded with actual output in its mathlib_searches.

## Second reading by NJ

This is a second pass by the same worker; the dispatch brief prohibits starting other
agents and assigns the independent review to the maintainer. Reopened the node and
both files after compilation. Checked n, open U, a ∈ U, all positive degrees, smooth
coefficients, the exact CR normalization, closedness, all three neighborhood conditions,
smooth β of predecessor degree and equality on V, and the entire degree-zero iff.
Checked deletion signs and the empty-index cases separately. No mismatch or change
was needed. The new node adds only the missing coordinate coefficient construction;
its domain-subtype representation avoids spurious off-domain data. Both postponed
theorems match the two clauses of this one node, and definitions contain no sorry.
