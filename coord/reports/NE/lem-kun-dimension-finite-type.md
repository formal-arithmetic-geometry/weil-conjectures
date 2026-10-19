## Worker report

The node is already stated by `AlgebraicGeometry.exists_topologicalKrullDim_le`
in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 212–215
of slopmaster2. Its full signature and docstring were read. Record it with
`existing: true`; no Lean module, new node, or dependency module is needed.

Hypothesis and conclusion correspondence:

- “K a field”: `{K : Type u} [Field K]`.
- “X a scheme”: `{X : Scheme.{u}}`.
- “over K”: `(f : X ⟶ Spec (.of K))`, the structure morphism. Quantifying over
  this map is the explicit form of a scheme over the field; its choice is not
  constrained beyond the node's hypotheses.
- “of finite type”: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the
  conjunction specified by def-weil-finite-type-morphism.
- “kundim X < infinity”: `∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)`.
  Every natural bound is strictly below top. Conversely any element below top
  in WithBot ℕ∞ is either bottom (bounded by 0) or a natural number (bounded
  by itself). Thus this is equivalent, neither stronger nor weaker.

The dimension is precisely the dependency's `topologicalKrullDim`, not the
local-ring dimension or a separate scheme dimension. Its definition is
`krullDim (IrreducibleCloseds X)`, the supremum of strict chain lengths.
The point dimension announced by def-kun-dimension is not needed here.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs, line 180;
  a commutative division ring with nontriviality.
- def-pc-scheme: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`,
  Mathlib.AlgebraicGeometry.Scheme, lines 42 and 74.
- def-weil-finite-type-morphism: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType, line 43, and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact,
  line 43. Their complete signatures and docstrings were read.
- def-kun-dimension: `topologicalKrullDim`, Mathlib.Topology.KrullDimension,
  lines 35–40, and `topologicalKrullDimAt`,
  WeilConjectures.Mathlib.Topology.KrullDimension, lines 339–344.
  These are the recorded definitions on the scheme's underlying space.

Edge cases: the empty scheme has dimension bottom and admits bound 0; the
existing proof explicitly handles bottom. Zero-dimensional schemes admit
bound 0. No integrality, nonemptiness, reducedness, separatedness, perfection,
or characteristic restriction is imposed. The single universe u is arbitrary;
field and scheme universes may be enlarged to a common universe, as in the
project's scheme-over-field convention. The upstream proof uses a finite
subcover of affine opens and finite dimensions of finite-type algebras; reuse
of this existing theorem is required by the one-statement rule, without a
new proof or changes to the node's recorded proof plan.

Searches (2026-10-15):

- msearch LeanFinder: “A scheme of finite type over a field has finite Krull
  dimension”: eight hits, including FiniteRingKrullDim and ring dimension
  finiteness, but no exact scheme theorem in Mathlib.
- msearch Loogle: “AlgebraicGeometry.topologicalKrullDim_ne_top_of_compactSpace,
  topologicalKrullDim”: zero hits; first name unknown to the Mathlib service.
- msearch grep: `topologicalKrullDim.*(ne_top|lt_top)|exists_topologicalKrullDim_le`
  in Mathlib/AlgebraicGeometry: zero hits.
- msearch LeanSearch: same plain-language query: service unavailable,
  Internal Server Error; no result available.
- rg of upstream WeilConjectures for `exists_topologicalKrullDim_le` and
  `topologicalKrullDim_ne_top_of_compactSpace`: exact existing declarations
  in Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean, plus applications
  in HilbertPolynomial and the six-functor modules. Read both signatures
  and docstrings and the whole proofs. The existential-bound version has
  precisely the node's finite-type hypotheses.
- rg of upstream WeilConjectures for `lem-kun-dimension-finite-type`: no tag hit.
- rg of lean/Sheaf for those declaration names: applications and a reference
  to the upstream theorem, no duplicate declaration. rg for topologicalKrullDim
  also confirms existing modules consistently use the same dimension.

No statement correction or disputed statement. The source blueprint statement
was read and agrees with the existing declaration via the equivalence above.
The upstream proof route differs from the blueprint's recorded proof route;
this does not change its statement.

## Second reading by NE

I read the blueprint node statement and the recorded declaration independently. The objects and hypotheses are rendered as follows:

- A field (K) is `{K : Type u} [Field K]`; no extra characteristic, algebraic-closed, or nontriviality hypothesis is added beyond `Field`.
- A scheme (X) is `{X : Scheme.{u}`}; the common universe is the declaration's universe and does not exclude the cases in the node.
- “of finite type over (K)” is the structure morphism `(f : X ⟶ Spec (.of K))` with `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the project's finite-type-morphism convention.
- The conclusion `\kundim X < \infty` is represented by `∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)`. Here `topologicalKrullDim` is the recorded `def-kun-dimension` notion, and the existential bound is equivalent to being strictly below top in `WithBot ℕ∞`, including bottom (the empty scheme) and every finite natural value.

The existing declaration is `AlgebraicGeometry.exists_topologicalKrullDim_le` in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, with exactly those binders and conclusion. It therefore states the node's claim; no Lean file, definition, or dependency module is needed. The source proof uses compactness of a quasi-compact scheme and the finite-type-over-a-field dimension result, while the blueprint proof route is documentary and does not alter the statement.

Edge cases checked: the empty scheme has dimension `⊥` and is bounded by `0`; a zero-dimensional scheme is bounded by `0`; no integrality, reducedness, separatedness, nonemptiness, or characteristic condition is present; `K` and `X` use the same arbitrary universe `u`; and no index set, integer `n`, or zero object occurs. Searches in Mathlib, `WeilConjectures`, and `lean/Sheaf`, plus LeanFinder/Loogle/grep searches recorded above, found no competing declaration or duplicate statement. No mismatch was found and nothing was changed in the worker's node copy.
