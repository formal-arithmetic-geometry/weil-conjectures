## Worker report

The module `Sheaf.TraceFormula.OpenChartFibreBoundSynchronization` states
`AlgebraicGeometry.openChart_fibreBound_synchronization`, with one `sorry` proof.
It introduces no definitions or further nodes and changes only the item's `lean` field.
The statement and proof plan are unchanged. No statement dispute or node fault was found.

The source was read in `literature/stacks-project/morphisms.tex`,
`lemma-dimension-fibre-after-base-change` (Tag 02FY, part (1)), and
`literature/stacks-project/topology.tex`, `definition-Krull` (Tag 0055) and
`lemma-dimension-supremum-local-dimensions` (Tag 0B7I). The six proof steps in the
node are reproduced in the theorem docstring, including closed-immersion base change
(Tag 01QR) and the elementary finite directed upper-bound argument. The latest
blueprint ancestor `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality`
was also read; as the node's blueprint record explains, the retained auxiliary
finite-stage dimension branch is not the ancestor's current normal-cone proof.

Hypothesis-by-hypothesis correspondence:

| Node | Lean rendering |
| --- | --- |
| Small nonempty directed partially ordered set `I` | `{I : Type u} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]` |
| Inverse system `f_i : X_i → S_i` | `X S : Iᵒᵖ ⥤ Scheme.{u}` and `f : X ⟶ S`; `f.app (op i)` is `f_i`, and naturality is the commutative transition square |
| Finite set of chart indices | `{A : Type v} [Finite A]`, with no nonemptiness condition |
| Open subschemes `W_{i,a}` and `V_{i,a}` | The schemes `(W a).obj (op i)`, `(V a).obj (op i)`, with inclusions `(ιW a).app (op i)`, `(ιV a).app (op i)`; `hW`, `hV` assert that these are open immersions |
| The source charts cover `X_i` | `hcover : ∀ i x, ∃ a, x ∈ Set.range ((ιW a).app (op i))` |
| `f_i(W_{i,a}) ⊆ V_{i,a}` and restricted morphism `g_{i,a}` | `g a : W a ⟶ V a` and `hrestrict : ∀ a, g a ≫ ιV a = ιW a ≫ f` |
| Transitions carry corresponding source and base charts into one another | Functor maps `(W a).map (homOfLE h).op` and `(V a).map (homOfLE h).op`, together with naturality of `ιW` and `ιV` |
| Integer `d ≥ 0` | `d : ℕ`, the equivalent parametrization of nonnegative integers |
| Scheme-theoretic fibres and topological dimension | `Scheme.Hom.fiber` and `topologicalKrullDim`, compared with `(d : WithBot ℕ∞)` |

Representing an open subscheme by an open immersion retains exactly the same object
up to its canonical identification with the open image. In particular, `g` is not
an arbitrary replacement map: its composite with the open immersion `ιV` is prescribed
by `hrestrict`, so it is uniquely the restriction of `f`. Conversely the original
image-inclusion condition gives precisely such a restriction. Given compatible opens,
the transition restrictions exist uniquely; their identity/composition laws, naturality
of the inclusions, and naturality of `g` follow from the corresponding laws for `X`,
`S`, and `f`, by cancellation of open immersions. Thus the functor encoding adds no
coherence or geometric hypotheses beyond the node's inverse system and compatibility.
The index universe follows the project's small-diagram convention, and the finite
chart index has an independent universe. Every variable and universe is explicitly bound.

Clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| (1), at every fixed stage, all fibres of `f_i` satisfy the bound iff every chart fibre does | The first conjunct `∀ i, (∀ s, topologicalKrullDim ((f.app (op i)).fiber s) ≤ ...) ↔ ∀ a t, topologicalKrullDim (((g a).app (op i)).fiber t) ≤ ...` |
| (2) assumes each restricted map locally of finite type | The first antecedent of the second conjunct: `∀ a i, LocallyOfFiniteType ((g a).app (op i))` |
| Closed immersion of the induced comparison `W_{j,a} → W_{i,a} ×_{V_{i,a}} V_{j,a}` | The second antecedent: for `a`, `i`, `j` and `h : i ≤ j`, `IsClosedImmersion (pullback.lift ((W a).map (homOfLE h).op) ((g a).app (op j)) ((g a).naturality (homOfLE h).op))` |
| Bounds on a fixed chart at `i` persist at each `j ≥ i` | The first conjunct after the two antecedents, universally quantified over `a`, `i`, `j`, the order relation, and the fibre bound at `i`, concluding the bound for every point of `V_{j,a}` |
| One bounding index for each chart | Antecedent `∀ a, ∃ i, ∀ t, topologicalKrullDim (((g a).app (op i)).fiber t) ≤ ...` |
| A common `j` bounds every fibre of each `f_k` for all `k ≥ j` | Conclusion `∃ j, ∀ k, j ≤ k → ∀ s, topologicalKrullDim ((f.app (op k)).fiber s) ≤ ...` |

In the comparison map, `pullback.lift`'s two legs are exactly the source transition
and `g_{j,a}`. Its equality witness is the existing naturality equality for `g`.
Its inferred target is the pullback of `g_{i,a}` and the base-chart transition.
There is no chosen arbitrary comparison and no new helper construction.
The additional finite-type and closed-comparison assumptions are inside the second
conjunct's implication, so they do not restrict part (1).

Dependency declarations used, with their recorded modules read directly:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `AlgebraicGeometry.Scheme.Hom.fiber` (the pullback along `fromSpecResidueField`).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and `pullback.lift`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim : WithBot ℕ∞`.

The statement dependencies are public imports. The proof dependencies are imported
without `public` where not already statement imports: `fibre_dimension_after_base_change`
from `Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange`;
`topologicalKrullDimAt` and `topologicalKrullDim_le_of_iSup_eq_top` from
`WeilConjectures.Mathlib.Topology.KrullDimension`;
`topologicalKrullDim_eq_iSup_topologicalKrullDimAt` from
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`; scheme sobriety instances
from `Mathlib.AlgebraicGeometry.Properties`. The other recorded Mathlib proof matches,
`Topology.IsInducing.topologicalKrullDim_le` and
`AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`, are in the public
statement imports already. No dependency record needed repair.

Edge cases were checked before writing and again on the final signature:

- `A` can be empty. Then `hcover` forces every `X_i` empty; all source-chart conditions
  are vacuous and all global fibre bounds hold. `[Nonempty I]` still supplies `j`.
- Empty source/base schemes and empty charts are allowed; no nonempty or inhabited
  scheme/point binders were added. Universally quantified fibre claims on an empty
  base are vacuous, as they should be.
- Empty fibres have dimension `⊥` in `WithBot ℕ∞`, which is bounded by every natural `d`.
- `d = 0` includes empty and zero-dimensional fibres; there is no positivity hypothesis.
- `i = j` is allowed. Functor identity laws identify its comparison with the canonical
  identity comparison, so no strict-transition condition has been introduced.
- No reducedness, Noetherianity, quasi-compactness, affineness, or limit-existence
  assumption is present. Only the second assertion requires locally finite type.

Searches for an existing statement (all `msearch.py` calls used group Q40 and this item):

- LeanFinder: `Fibre dimension bounds are local on finite compatible open charts and
  persist under closed immersions into base changes, eventually at a common directed
  index`. Eight hits, including `IsLocalAtSource`, local-at-target immersion properties,
  and preimmersion base-change stability; none states the two assertions.
- LeanSearch: `Fibre dimension bounded by d iff it is bounded on each of finitely many
  compatible open charts, with bounds propagating under closed comparison maps in a
  directed inverse system`. Eight hits about directed inverse-system limits, vector
  bundle frames, finite morphism fibres, and simplicial dimension; no match.
- Loogle: `"topologicalKrullDim", "fiber"`. Zero hits.
- Mathlib grep via msearch, under `AlgebraicGeometry`:
  `(topologicalKrullDim|krullDim).*(fiber|baseChange|Cover)|(fiber|baseChange|Cover).*(topologicalKrullDim|krullDim)`.
  Zero hits.
- Project/source `rg`: `(fibre.*(synchron|chart)|fiber.*(synchron|chart)|open_chart_fibre|topologicalKrullDim.*fiber)`
  under `lean/WeilConjectures` and `lean/Sheaf`. Related field-extension and fibre-dimension
  results, curve charts and particular dimension bounds were found, including
  `topologicalKrullDim_fiber_of_isPullback`; none supplies the full chart-locality,
  closed-comparison persistence and finite synchronization statement.
- Node-id search in `lean/WeilConjectures` found no occurrence. Exact proposed-name
  search in `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf`
  found no existing declaration.

Validation: `scompile.py Q40 lem-trf-open-chart-fibre-bound-synchronization <module>`
compiled both the sandbox and library-path versions cleanly (7.0 s and 2.9 s),
with no errors or warnings. The only proof is the intended stage-2 `sorry`.

## Second reading by Q40

This is the dispatcher's required worker self-check; the maintainer performs the
independent review. I reread the node, the complete final signature and the six-step
proof docstring together. The first conjunct has no extra finite-type assumptions.
The second retains both persistence at every ordered pair of indices and the eventual
uniform bound at every later stage, rather than only at the common stage itself.
Naturality has the correct inverse-system direction (`op j → op i`). The closed map
is the canonical pullback lift with those two specified legs. The restricted morphisms
are determined by `hrestrict`, and the cover uses only source charts, with no added
requirement that the base charts cover `S_i`. Empty charts, an empty finite index type,
and zero dimension remain allowed. No mismatch or correction was found, and no
additional nodes, dependency modules, or statement changes were needed.
