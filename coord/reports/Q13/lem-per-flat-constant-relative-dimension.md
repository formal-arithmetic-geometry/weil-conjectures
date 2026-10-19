## Worker report

The module `Sheaf.AlgebraicGeometry.FlatConstantRelativeDimension` states
`AlgebraicGeometry.topologicalKrullDimAt_eq_add_of_flat_constantRelativeDimension`.
Its only theorem has proof `sorry`; it introduces no definitions or auxiliary theorems.
Only the item's `lean` record is changed. No correction or dependency repair is needed.
No repair note exists for this item.

I read Stacks Project `literature/stacks-project/morphisms.tex`,
`definition-relative-dimension-d` and `lemma-rel-dimension-dimension` (Tag 0AFE).
The source assumes flatness, local finite type, locally Noetherian source and target,
and relative dimension d. For these fibres, which are locally of finite type over
residue fields, the node spells out relative dimension as local topological
dimension d at every point. The Lean statement follows that explicit node formulation.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| Schemes X and Y and a morphism f : X → Y | `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)` |
| Both schemes are locally Noetherian | `[IsLocallyNoetherian X] [IsLocallyNoetherian Y]` |
| f is flat | `[Flat f]` |
| f is locally of finite type | `[LocallyOfFiniteType f]` |
| A natural number d | `(d : ℕ)` |
| For every a in X, take b = f(a) and its scheme-theoretic fibre | `∀ a : X` and `f.asFiber a : f.fiber (f a)` |
| Local topological fibre dimension at that point equals d | `hd : ∀ a : X, topologicalKrullDimAt (f.asFiber a) = (d : WithBot ℕ∞)` |
| For every x in X with y = f(x) | `(x : X)` and `f x` |
| dim_x X = dim_y Y + d | `topologicalKrullDimAt x = topologicalKrullDimAt (f x) + (d : WithBot ℕ∞)` |
| Dimensions are minima of open-neighbourhood dimensions | Existing `topologicalKrullDimAt` is exactly their infimum in the well-ordered `WithBot ℕ∞`, hence their minimum |
| Infinite dimension plus finite d is infinite | Addition and the natural-number cast are in `WithBot ℕ∞` |
| No smoothness, surjectivity, separatedness or global finite type | None of those properties is a binder; no quasi-compactness or nonemptiness binder is present |

Dependency declarations used, with their source signatures and docstrings read:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. Mathlib's every-affine-open definition
  agrees with the node's affine Noetherian cover definition, as its recorded note states.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; `Flat.iff_flat_stalkMap` identifies it with flatness of
  every stalk map, precisely the node's definition.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`. Only the local finite type clause is used.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`,
  `fiberHomeo`, `asFiber`. The fibre is the pullback along `Y.fromSpecResidueField`;
  `asFiber` uses the inverse fibre homeomorphism at the original point, so the
  hypothesis uses the canonical corresponding point rather than an arbitrary lift.
- `def-kun-topological-dimension-at-point`:
  `WeilConjectures.Mathlib.Topology.KrullDimension`, `topologicalKrullDimAt`.
  Its definition is `⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U`.

All five statement dependency modules are public imports. Recorded proof modules
are ordinary imports: `Sheaf.AlgebraicGeometry.Dimension`,
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`,
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`,
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`,
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties`, and
`Mathlib.Topology.KrullDimension`. The other proof dependencies are already in the
statement dependency modules. The current source of
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`, absent in the old
local source checkout, was read successfully through `scompile.py --source`.
The docstring carries all five proof steps and their DAG citations, including
shrinking, restriction of the hypotheses, fibre dimensions, the local-ring
dimension formula and its suprema, and return to the original neighbourhoods.

Edge cases checked before writing:

- Empty X: the universal fibre condition is vacuous, and the conclusion requires
  a point x, so the theorem imposes no unintended nonempty-fibre requirement.
- Empty Y: a morphism into it has empty source; again no x is supplied.
- d = 0: the formula reduces to equality with the base dimension. This includes
  identity morphisms and open immersions of locally Noetherian schemes.
- The affine n-space projection over a field has fibre dimension n; at every
  point its local topological dimension is n, including generic points. This
  distinguishes the chosen dimension from the dimension of a local ring.
- Infinite local dimension of Y is retained because the conclusion is in
  `WithBot ℕ∞`; no finiteness assumption on either local dimension is imposed.
- Nonsurjective flat maps are allowed; the condition quantifies over source
  points, so fibres over points outside the image cause no obligation.
- The universe u is explicitly declared and arbitrary. Both schemes use the
  common universe of Mathlib's scheme category; there are no test-object size
  restrictions, auto-bound variables, or file-local notation in the signature.

Searches for an existing statement:

- `msearch.py ... leanfinder`, query: “For a flat locally finite type morphism of
  locally Noetherian schemes of constant fibre dimension d the local topological
  dimension at x equals the local dimension at f(x) plus d”. Eight hits:
  `IsSmoothOfRelativeDimension`, `Flat`, `Flat.generalizingMap`,
  `Algebra.IsStandardSmooth.relativeDimension`, `Flat.instIsMultiplicativeScheme`,
  `Flat.stalkMap`, `UniversallyOpen.of_flat`, and
  `Algebra.IsStandardSmoothOfRelativeDimension.out`. No dimension formula.
- `msearch.py ... loogle`, query `topologicalKrullDimAt, Flat`: no hits;
  `topologicalKrullDimAt` is unknown to that Mathlib-only index.
- `msearch.py ... leansearch`, query “Dimension formula for flat morphisms of
  schemes of constant relative dimension”. Eight hits on smooth relative
  dimension and the flat morphism API, with no matching formula.
- `msearch.py ... grep`, query
  `(Flat|flat).*topologicalKrullDimAt|topologicalKrullDimAt.*(Flat|flat)`:
  zero Mathlib hits.
- `rg` in the upstream `WeilConjectures/AlgebraicGeometry` and project
  `lean/Sheaf/AlgebraicGeometry` for local dimension and flat dimension phrases:
  related results include smooth local dimension and fibre dimension charts;
  none state the flat constant-relative-dimension formula. In particular,
  `SmoothLocalDimension.lean` assumes smoothness and cites this very node in
  its proof plan, so cannot replace this theorem.
- `grep -rn 'lem-per-flat-constant-relative-dimension'` in upstream
  `WeilConjectures`: no hits.
- `rg` for `topologicalKrullDimAt_eq_add_of_flat`, `constantRelativeDimension`,
  `constant_relative_dimension`, and `rel-dimension-dimension` across upstream
  `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration or name collision.

Validation: prescribed `scompile.py Q13 lem-per-flat-constant-relative-dimension`
compiled both the sandbox and library-path form cleanly (2.3 s and 2.5 s).
Every source line is at most 100 characters. The node record contains the exact
multiline theorem signature and UTC date 2026-10-18.

## Second reading by Q13

Author's second reading, with the node and Lean file reopened; independent
review is performed by the maintainer, as required by this direct-delivery brief.
No other agent was started.

I checked both locally Noetherian binders, flatness, local finite type and the
natural-number d separately. The hypothesis ranges over every source point,
and `f.asFiber a` belongs to precisely the scheme-theoretic fibre over f(a).
It is its local topological dimension that is set to d. The arbitrary x binder
then states exactly the single requested equality at x and its image f(x), with
finite d added to the base dimension. Both occurrences use the recorded
open-neighbourhood definition, rather than stalk dimensions or global dimensions.
There is no added smoothness, surjectivity, finite type, separatedness, or
finiteness assumption. The source Tag 0AFE and its relative-dimension definition
agree with these choices. No statement mismatch was found; no corrections,
new nodes, dependency modules, or disputed statements are needed.
