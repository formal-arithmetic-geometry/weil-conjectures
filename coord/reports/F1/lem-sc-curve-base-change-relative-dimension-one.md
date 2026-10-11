## Worker report

The module `lean/Sheaf/AlgebraicGeometry/CurveBaseChangeRelativeDimensionOne.lean`
states `AlgebraicGeometry.curve_baseChange_smooth_fiber_dimension_one`, with only
`sorry` as its proof. It gives the two explicit clauses in the node's definition of
smooth relative dimension one. No definition is introduced; no statement correction,
new node, or dependency replacement is needed. Only the item's `lean` record changes.

Hypothesis and clause correspondence:

| Node text | Lean |
| --- | --- |
| `k` is a field | `{k : Type u} [Field k]` |
| `C` is a scheme over `k` with its structure morphism | `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))` |
| `C` is integral | `[f.IsCurveOverField]`, whose inherited `IsVariety.isIntegral` is `IsIntegral C` |
| `f` is separated | The same class inherits `IsVariety` and hence `IsSeparated f` |
| `f` is of finite type | The same class inherits `LocallyOfFiniteType f` and `QuasiCompact f` |
| `C` has dimension exactly one | The same class has `dim_eq_one : C.dim = 1` |
| The structure morphism is smooth | `[Smooth f]` |
| Any scheme `T` and morphism to `Spec k` | `{T : Scheme.{u}} (g : T ⟶ Spec (.of k))` |
| `C_T = C ×_Spec k T` | `pullback f g : Scheme.{u}` |
| `f_T` is the second projection | `pullback.snd f g` |
| `f_T` is smooth | The first conjunct, `Smooth (pullback.snd f g)` |
| Every point `x` of `C_T` | `∀ x : (pullback f g : Scheme.{u}), ...` |
| `t = f_T(x)` and `x` as a point of `(C_T)_t` | `(pullback.snd f g).asFiber x`, of type `(pullback.snd f g).fiber ((pullback.snd f g) x)` |
| The fibre is `C_T ×_T Spec κ(t)` | `Scheme.Hom.fiber` is defined as that pullback along `T.fromSpecResidueField t` |
| Dimension of the fibre at `x` equals one | `topologicalKrullDimAt ((pullback.snd f g).asFiber x) = 1` |

The phrase "smooth of relative dimension one" is expanded using the node's own
"is smooth, and for every point ..." description. This retains its local topological
dimension clause explicitly, without replacing it by a local-ring dimension or by
a global-dimension bound. The numeral has type `WithBot ℕ∞`. `asFiber` uses the
canonical homeomorphism from the scheme-theoretic fibre to the set-theoretic fibre;
`fiberι_asFiber` says its image is precisely the original point `x`.

Dependency declarations read and used:

- `def-pc-curve`: `Sheaf.AlgebraicGeometry.Variety`,
  `AlgebraicGeometry.Scheme.Hom.IsCurveOverField`, including the full signatures
  and docstrings of its inherited `Scheme.Hom.IsVariety`. The curve class gives
  all of integral, separated, finite type, and dimension exactly one.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`. Read the chart definition, its docstring and the
  `SmoothOfRelativeDimension` signature. The conclusion uses the node's expanded
  smoothness-plus-fibre-dimension description; it introduces no replacement notion.
- `def-pc-base-change`: `Sheaf.AlgebraicGeometry.BaseChangeConventions`, whose
  recorded note explicitly prescribes `Limits.pullback f T.hom` with second
  projection `pullback.snd`. The same chosen pullback is used with the unbundled
  structure map `g`. Read the whole conventions module, including
  `AlgebraicGeometry.baseChange_fiber`, which records the fibre identification
  used in proof step 2. No module-pullback functor is used because this node has
  no module-sheaf clause.
- `def-kun-dimension`: `WeilConjectures.Mathlib.Topology.KrullDimension`,
  `topologicalKrullDimAt (x : X) : WithBot ℕ∞` for a topological space `X`.
  Read its full definition as the infimum of dimensions of open neighbourhoods,
  and its docstring. This is the recorded dimension at a point, not the stalk dimension.
- The underlying fibre and fibre-point constructions are Mathlib's
  `AlgebraicGeometry.Scheme.Hom.fiber`, `fiberHomeo`, and `asFiber`, from
  `Mathlib.AlgebraicGeometry.Fiber` (imported by the conventions module).

Sources read online, because this clone has no `literature/stacks-project` checkout:
[02NK](https://stacks.math.columbia.edu/tag/02NK),
[02FY (1)](https://stacks.math.columbia.edu/tag/02FY),
[01VB](https://stacks.math.columbia.edu/tag/01VB), and
[0A21 (3)](https://stacks.math.columbia.edu/tag/0A21).
These support, respectively, relative-dimension stability, equality of local fibre
dimensions, smoothness stability, and equality of local and global dimensions
on an irreducible scheme locally of finite type over a field. The docstring gives
all four original proof steps and names their DAG dependencies.

Edge cases checked before writing:

- Empty `T` is allowed. Its pullback is empty; the pointwise equality is vacuous,
  and the smooth projection has empty source. There is no nonemptiness assumption
  on `T` or on the pullback.
- `T` need not be reduced, connected, Noetherian, affine, smooth, or of finite
  type over `k`; no such assumption occurs in the signature.
- An empty or zero-dimensional `C` is excluded by the original curve hypothesis,
  including integrality and `C.dim = 1`. No additional exclusion was added.
- No properness, projectivity, algebraic closure, geometric integrality, rational
  point, or characteristic restriction on `k` is assumed. A curve may split into
  several components after a field extension; every fibre point still has local
  topological dimension one.
- At a generic point of a smooth curve, stalk dimension can be zero while the
  local topological dimension in this statement is one. `topologicalKrullDimAt`
  preserves this essential distinction.
- The universe `u` is explicit and arbitrary; `k`, `C`, and `T` live in the same
  scheme category, as required for the chosen pullback. Any finite collection of
  these objects can be placed in a common universe. All variables are bound.

Searches for an existing statement (actual calls recorded in `searches.jsonl`):

- LeanFinder, query `base change of a smooth integral curve over a field has relative
  dimension one`: eight hits, including standard-smooth base-change stability and
  unrelated Weierstrass-curve scalar-extension lemmas. No matching curve theorem.
- Loogle, query `AlgebraicGeometry.SmoothOfRelativeDimension,
  CategoryTheory.Limits.pullback.snd`: one hit,
  `AlgebraicGeometry.instSmoothOfRelativeDimensionSndScheme`, which assumes
  `SmoothOfRelativeDimension n f` and does not deduce it from the curve hypothesis
  or state the displayed local fibre dimensions.
- Mathlib grep via `msearch.py`, query `smoothOfRelativeDimension|fiber.*dim` in
  `AlgebraicGeometry`: ten returned hits, all chart-based relative smoothness or
  etale equivalences; no theorem with the item's hypotheses and conclusion.
- LeanSearch, query `base change of a smooth curve over a field has fibre dimension
  one at every point`: unavailable, HTTP Internal Server Error; recorded as unavailable.
- `rg` in the source project's `WeilConjectures/AlgebraicGeometry` and
  `WeilConjectures/Mathlib/AlgebraicGeometry`, query
  `smoothOfRelativeDimension|topologicalKrullDimAt.*asFiber|asFiber.*topologicalKrullDimAt|IsCurveOverField`:
  found generic smooth base-change instances, relative-dimension/global-dimension
  comparison over a field, and local constancy of fibre dimension; none states this
  curve theorem. Read signatures and docstrings of
  `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` and
  `topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`; both need additional
  derivations to obtain this statement, rather than being an existing match.
- `rg` for the exact item id in `WeilConjectures` and `dag/lean_names_upstream.json`:
  no hit.
- `rg` in `lean/Sheaf` for the same concept pattern and for
  `smoothOfRelativeDimension|fiber.*dim|base.change.*curve`: no matching statement.
  `DimensionBaseChange.dim_base_change` gives global dimension after a field
  extension, not arbitrary base change with pointwise fibre dimension.
- `rg` for the proposed full declaration's final name
  `curve_baseChange_smooth_fiber_dimension_one` in Mathlib, WeilConjectures,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no collision.

No statement dispute or mathematical node fault was found.

Validation: server single-file compilation via `scompile.py`; delivery preflight
via `deliver2.py --no-push`. The independent second reader supplies the second-reading
section and delivers the packet.

## Second reading by F1

I independently opened the item JSON, its Lean file, all four statement-dependency
nodes, and their recorded declarations and docstrings. No hypothesis, object, or
conclusion mismatch was found; the Lean and the node record are retained unchanged.
The following is my object/hypothesis/conclusion inventory and correspondence.

| Node item | Lean rendering and verdict |
| --- | --- |
| An arbitrary field k | `{k : Type u} [Field k]`: exact, no characteristic or closure assumption. |
| A scheme C over k with structure map | `{C : Scheme.{u}} (f : C ⟶ Spec (.of k))`: exact; the explicitly named map is needed for base change. |
| C integral | `[f.IsCurveOverField]` extends `f.IsVariety`, whose `isIntegral : IsIntegral C` field supplies precisely this property. Exact; being a field extension or geometrically integral is not required. |
| f separated | The inherited `IsSeparated f` field of `IsVariety`: exact. |
| f finite type | The inherited `LocallyOfFiniteType f` and `QuasiCompact f`: exact conjunction used by this dependency, no stronger finite-presentation assumption added. |
| C has dimension exactly 1 | `IsCurveOverField.dim_eq_one : C.dim = 1`: exact; opened `Sheaf.AlgebraicGeometry.Dimension` and checked that `Scheme.dim` is the supremum of stalk Krull dimensions, as def-pc-curve requires. |
| f smooth | `[Smooth f]`: exact existing dependency predicate, defined by smooth ring maps on affine charts. |
| Any scheme T and any map to Spec k | `{T : Scheme.{u}} (g : T ⟶ Spec (.of k))`: exact; no geometric or finiteness instance on T. |
| C_T is the specified base change | `pullback f g`: exactly the chosen fibre product prescribed by def-pc-base-change, not an unrelated scheme with an asserted isomorphism. |
| f_T is the second projection | `pullback.snd f g`: exact, with target T. |
| f_T is smooth | First conjunct `Smooth (pullback.snd f g)`: exact. |
| For every x in C_T, set t = f_T(x) | `∀ x : (pullback f g : Scheme.{u})`: exact quantification; the dependent type of `asFiber x` fixes t to this image. |
| The fibre is C_T ×_T Spec κ(t), and x is its corresponding point | Mathlib `Scheme.Hom.fiber` is that pullback; `Scheme.Hom.asFiber` has type `f_T.fiber (f_T x)` and is defined using `fiberHomeo`. Opened `fiberι_asFiber`, which identifies its image with x. Exact. |
| Dimension at this fibre point is 1 | `topologicalKrullDimAt ((pullback.snd f g).asFiber x) = 1`: exact, using def-kun-dimension, not stalk dimension. |
| Smooth of relative dimension 1 | The two preceding conclusion clauses are joined by `∧`, exactly as the item's explicit expansion and def-sbc-smooth-morphisms specify. No new predicate is defined. |

Source reading: this machine has no Stacks .tex checkout, so I fetched upstream
`morphisms.tex` and `varieties.tex` into this item's `scratchpad/` and opened the
labels named in the node. I also read the corresponding official tag pages:
[02NK](https://stacks.math.columbia.edu/tag/02NK),
[02FY](https://stacks.math.columbia.edu/tag/02FY),
[01VB](https://stacks.math.columbia.edu/tag/01VB), and
[0A21](https://stacks.math.columbia.edu/tag/0A21).
The hypotheses of 02NK and 02FY (1) include local finite type, already supplied
by `IsCurveOverField`; 01VB has no additional base-change hypothesis. In 0A21 (3),
the field, locally algebraic scheme, and irreducibility hypotheses follow from
the curve data. Nothing in these source places assumes T Noetherian or finite type.
The theorem docstring reproduces the node's four proof steps, including the
scheme-fibre identification, comparison of scheme and topological dimensions,
and the use of irreducibility in passing to dimension at every point.

Dependency audit: `Variety.lean` gives the correct integral curve convention,
not upstream's possibly reducible `IsCurve`; `BaseChangeConventions.lean` explicitly
prescribes the pullback and second projection used here. I read the signatures
and definitions of `Smooth` and `SmoothOfRelativeDimension` in Mathlib, and the
definition of `topologicalKrullDimAt` in the recorded upstream module (the infimum
over open neighbourhoods). These are the node's notions. This delivery has no
new nodes or replacement dependency modules, and no statement correction.

Edge cases: empty T is allowed and the pointwise clause is vacuous; no nonempty
pullback instance occurs. Empty or dimension-zero C is excluded only by the
original curve data. No restriction on characteristic, properness, rational
points, or algebraic closure is added. Nonreduced, disconnected, non-Noetherian,
and arbitrarily large T are allowed. Fibres can be reducible after field extension;
the claim still concerns dimension at each point, not integrality of the fibre.
At a generic point the stalk may have dimension zero while this neighbourhood
dimension is one, confirming the importance of the recorded dimension notion.
There is no index family or variable n in the statement; the dimension is fixed
at one. The explicit arbitrary universe u places the finite diagram in one common
scheme category; no size bound is imposed. Every type and term variable is bound.

Independent duplicate searches, recorded by `msearch.py` in `searches.jsonl`:

- LeanFinder: `A smooth one dimensional integral variety remains of fibre dimension
  one after arbitrary scalar base extension`: eight hits, principally standard
  smooth algebra presentations and their base-change stability; no matching theorem.
- Loogle: `topologicalKrullDimAt`: unknown identifier in its Mathlib index, so no
  hit. Also searched `AlgebraicGeometry.SmoothOfRelativeDimension,
  CategoryTheory.Limits.pullback.snd` to inspect the generic pullback instance.
- LeanSearch: `The pullback projection of a smooth integral dimension one scheme
  over a field has fibres of local dimension one`: unavailable (Internal Server
  Error); no mathematical absence verdict is inferred from this service failure.
- `rg` over all `WeilConjectures`, Mathlib algebraic geometry, and `lean/Sheaf`,
  using `IsCurveOverField`, curve/baseChange in both orders, fibre-dimension-one,
  and `topologicalKrullDimAt.*asFiber`: only Weierstrass scalar extension,
  the curve definitions, generic fibre-dimension comparison/local constancy,
  and `DimensionBaseChange.dim_base_change`. The last only gives global dimension
  under field extension, not this pointwise statement for arbitrary T.
- Opened upstream `smoothOfRelativeDimension_iff_topologicalKrullDim_eq` and
  `topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`: their signatures require
  comparison or base-change arguments to produce this item; neither is an exact
  existing match. Exact item-id search in upstream and `dag/lean_names_upstream.json`
  returned no declaration.

H5/H6/H8/H9 check: no definitions are introduced, the sole proof is `by sorry`,
module and theorem docstrings cite the source and blueprint id, and all lines are
within 100 characters. The recorded `lean.statement` is verbatim the file's
signature, with no implicit unbound variables. No mathematical or code change was
needed; this reading adds this independent audit and its search records only.
