## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds` states
`AlgebraicGeometry.Scheme.Hom.finiteType_fibre_image_dimension_bounds` with one `sorry`.
It introduces no definitions. The node is unchanged except for its `lean` record.
No statement correction, new node, dependency repair, or statement dispute is needed.

Read the node and all four statement dependencies, including their recorded Lean interfaces
and full signatures/docstrings. Read the source in `literature/stacks-project/varieties.tex`,
lines 3952–4011, Tag 0B2L, `lemma-dimension-fibres-locally-algebraic`: for an irreducible source,
the dimension difference equals the generic-fibre transcendence degree, local fibre dimensions
are at least that difference, and equality holds on a dense open. The node's componentwise
consequences have exactly the hypotheses used here. The theorem docstring carries all four
node proof steps, including the empty-source case and the comparison of component fibres
with ambient scheme-theoretic fibres.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| `k` is a field | `{k : Type u} [Field k]` |
| `X` and `Y` are schemes | `{X Y : Scheme.{u}}` |
| Both schemes are over `k` | `[X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]` |
| `X` is finite type over `k` | Both `LocallyOfFiniteType` and `QuasiCompact` for `X ↘ Spec (.of k)` |
| `Y` is finite type over `k` | Both `LocallyOfFiniteType` and `QuasiCompact` for `Y ↘ Spec (.of k)` |
| `f : X → Y` is a `k`-morphism | `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]` |
| All dimensions are topological Krull dimensions, empty dimension negative infinity | `topologicalKrullDim`, valued in `WithBot ℕ∞`, whose bottom is the empty-space dimension |
| The closure is the topological closure in `Y` of `f(X)` | `closure (Set.range f)` as a subset of the underlying space of `Y` |
| First bound: dimension of the image closure at most dimension of `X` | First conjunct `topologicalKrullDim (closure (Set.range f)) ≤ topologicalKrullDim X` |
| Moreover, for nonnegative integers `d,n` | Second conjunct begins `∀ (d n : ℕ)`; natural numbers represent exactly the nonnegative integers, including zero |
| Dimension of `Y` is at most `d` | Antecedent `topologicalKrullDim Y ≤ (d : WithBot ℕ∞)` |
| Every scheme-theoretic fibre has dimension at most `n` | Antecedent `∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (n : WithBot ℕ∞)` |
| Conclusion: dimension of `X` at most `d+n` | `topologicalKrullDim X ≤ ((d + n : ℕ) : WithBot ℕ∞)` |
| No dominance, properness, flatness, irreducibility, or algebraic closedness | No corresponding assumptions occur in the signature |

The bounds are a conjunction, so the first inequality has no dimension-bound premises;
the second is universally quantified in `d,n` and conditional on precisely its two premises.
Every universe and variable is explicitly bound; `set_option autoImplicit false` is present.
The common scheme/field universe is the standard Mathlib scheme convention and can be enlarged
as needed; there is no independently smaller test-object universe or size restriction.

Dependency declarations used:

- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, lines 38–46, and
  `AlgebraicGeometry.QuasiCompact` in `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  lines 37–46. The finite-type module's introduction explicitly defines finite type as
  locally of finite type and quasi-compact, as does the node.
- `def-weil-scheme-over-base`: its Mathlib match `AlgebraicGeometry.Scheme.Over` and
  `AlgebraicGeometry.Scheme.Hom.IsOver` in `Mathlib.AlgebraicGeometry.Over`, lines 32–50.
  `Over` supplies the structure morphism; `IsOver` asserts its commutation with `f`.
  This dependency is a Mathlib leaf and needs no repaired `lean` field.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`, lines 35–40. It is the Krull dimension of the poset
  of nonempty irreducible closed subsets; a subset argument uses its subspace topology.
- `def-pc-scheme-fibre`: `AlgebraicGeometry.Scheme.Hom.fiber` in
  `Mathlib.AlgebraicGeometry.Fiber`, line 38, defined as the pullback along
  `Y.fromSpecResidueField y`. Read its projections at lines 41 and 46, its residue-field
  scheme structure at lines 57–59, and `fiberHomeo` at lines 102–104.

Proof-only imports include the recorded finite-dimensionality and local-dimension modules
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and
`WeilConjectures.Mathlib.Topology.KrullDimension`; the recorded source module
`WeilConjectures.AlgebraicGeometry.Modules.VeryAmple` for
`lem-pc-closed-imm-base-change`; and Mathlib modules for closed subschemes, closed immersions,
immersions, and Noetherianity. These are ordinary imports, not public statement dependencies.
The child `lem-zl-irreducible-fibre-dimension-lower-bound` has neither a Lean record nor a
Mathlib match at the inspected base, so no proof-only import can yet be given for it.
It is only mentioned in the proof plan; no missing notion is needed for this signature.

Edge cases checked against the mathematical statement and its encoding:

- Empty `X`: its image and closure are empty, both dimensions in the first inequality are
  bottom, and the second conclusion is bottom at most a natural number. No `Nonempty` binder.
- Empty `Y`: a morphism to it forces `X` empty; the fibre premise is vacuous and both bounds
  are valid. No point of `Y` is selected.
- Empty individual fibres: their dimension is bottom, so the premise permits them.
- `d = 0` and `n = 0` are allowed, including simultaneously; arithmetic occurs in `ℕ`
  before its explicit coercion to the extended dimension type, with no truncated subtraction.
- Disconnected or reducible sources, nonreduced schemes, non-dominant maps, and all field
  characteristics remain included. No separatedness or algebraic closedness was introduced.

Searches actually run (all through the prescribed tools or read-only source searches):

1. `msearch.py` LeanFinder: "For finite type schemes over a field the dimension of the closure
   of a morphism image is bounded by the source dimension and source dimension is bounded by
   base dimension plus fibre dimension". Eight hits, including `finite_appTop_of_universallyClosed`,
   `IsFinite`, `IsDominant`, `IsStandardSmoothOfRelativeDimension.out`, and fibre finiteness /
   Jacobson-space declarations. These do not state either pair of bounds.
2. `msearch.py` Loogle: `"topologicalKrullDim", "fiber"`. Successful, zero hits.
3. `msearch.py` grep: `topologicalKrullDim.*(range|fiber)|dimension.*fibres` in
   `AlgebraicGeometry`. Successful, zero hits.
4. `msearch.py` LeanSearch: "The dimension of a finite type scheme over a field is at most
   the dimension of the target plus an upper bound on dimensions of all fibres of a morphism".
   Eight hits: relative smooth dimension/composition, proper locally-finite-type, fibre,
   finite morphisms and finite fibres. None is the desired general theorem.
5. `rg -n` for `topologicalKrullDim.*(range|fiber)|dimension.*(fibres|fibers)|` followed by
   the exact item id, in the upstream `WeilConjectures` and project `lean/Sheaf` trees.
   Read the candidate upstream finite-dimensionality, generic-fibre, and topology-range
   declarations: none states this theorem. Project hits include component lower bounds and
   special fibre bounds, not this conjunction. In particular,
   `FiniteTypeFibreComponentLowerBound` is the rational-maximal-ideal algebraic component
   inequality for a domain target, not this scheme-level statement.
6. `rg -n` for `finiteType_fibre_image_dimension_bounds|finiteTypeFibreImageDimensionBounds|`
   `topologicalKrullDim.*range|dim.*image.*le` in Mathlib's algebraic geometry, upstream
   `WeilConjectures`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`.
   The range-dimension hits concern embeddings and closed subschemes, not arbitrary morphisms
   of finite-type schemes. Neither proposed theorem name occurs.
7. `grep -rn` for the exact item id in upstream `WeilConjectures`: no hits. Also inspected
   the upstream name index for fibre/image names; no exact existing declaration was found.

Validation: `scompile.py Q54 lem-zl-finite-type-fibre-image-dimension-bounds` on the delivered
module passed both the sandbox and library-mode single-file compilations (2.2 s and 3.0 s),
with no errors or warnings. Only one postponed theorem is introduced; its proof is `sorry`.

## Second reading by Q54

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
