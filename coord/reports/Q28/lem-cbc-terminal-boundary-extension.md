## Worker report

The module `lean/Sheaf/CategoryTheory/TerminalBoundaryExtension.lean` states
`SSet.Enhanced.terminal_iff_boundary_extension`, with one `sorry` and no other
declarations. The node is unchanged except for its `lean` record. No repair note
exists for this item. No new notions, dependency repairs, statement corrections,
or disputed statements are needed.

Sources read: the whole node and its six proof steps; the statement and Lean record
of `def-cbc-enhanced-diagrams-cones`; its complete source module; the recorded
sources of the stated proof dependencies; Mathlib's boundary and vertex APIs;
Kerodon [06R1](https://kerodon.net/tag/06R1),
[05ET](https://kerodon.net/tag/05ET), and
[01KX](https://kerodon.net/tag/01KX). Proposition 06R1 states exactly the desired
positive-dimensional boundary criterion. The source's finality is rendered using
the dependency's incoming right-pinched mapping spaces and weak contractibility.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| A quasicategory Q | `{Q : SSet.{u}} [Quasicategory Q]` |
| A specified vertex t | `(t : Q _⦋0⦌)` |
| For every vertex x | `∀ x : Q _⦋0⦌` |
| Map_Q(x,t), with the recorded right-pinched convention | `mappingSpace Q x t` |
| Contractible, meaning weakly contractible | `IsContractible (mappingSpace Q x t)` |
| If and only if | `↔` |
| Every integer m ≥ 1 | `∀ (n : ℕ)`, with dimension `n + 1` |
| A simplicial boundary map σ | `(σ : (∂Δ[n + 1] : SSet.{u}) ⟶ Q)` |
| The last vertex of σ equals t | `(boundary.ι (0 : Fin (n + 2)) ≫ σ).app _ (stdSimplex.obj₀Equiv.symm (Fin.last n)) = t` |
| An extension over the whole simplex | `∃ σbar : (Δ[n + 1] : SSet.{u}) ⟶ Q` |
| Restriction recovers σ | `(boundary (n + 1)).ι ≫ σbar = σ` |
| Boundary is the union of faces, with empty zero-boundary | Mathlib `SSet.boundary`, `boundary_eq_iSup`, and `boundary_zero` |

The last-vertex expression uses only existing maps: `boundary.ι 0` includes the
zeroth face, whose vertices are 1,...,n+1. Consequently its last vertex, indexed
by `Fin.last n` before inclusion, is exactly vertex n+1 of the full simplex.
This follows directly from `boundary.ι` being the factorization of
`stdSimplex.map (SimplexCategory.δ 0)`, where δ uses `Fin.succAboveOrderEmb 0`.
It imposes no condition on the other vertices or on any higher face of σ.

Dependencies used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: `SSet.Enhanced.mappingSpace`,
  `SSet.Enhanced.IsContractible`, whose full definitions were read. The former
  imposes a constant entire initial face and a specified last vertex; the latter
  tests the map to the standard point using realization weak equivalence.
- Mathlib `AlgebraicTopology.Quasicategory.Basic`: `SSet.Quasicategory` (available
  through that dependency), imposing exactly inner-horn extension.
- Mathlib `AlgebraicTopology.SimplicialSet.Boundary`: `SSet.boundary`,
  `SSet.boundary.ι`, and `SSet.Subcomplex.ι`; Mathlib
  `AlgebraicTopology.SimplicialSet.StdSimplex`: `SSet.stdSimplex.obj₀Equiv`.
- Proof-only import `Sheaf.CategoryTheory.RightFibrationFibers`:
  `SSet.Enhanced.rightFibration_fibers`, specifically its Kan-fiber clause.
- Proof-only import `Sheaf.CategoryTheory.RightFibrationContractibleFibers`:
  `SSet.rightFibration_of_contractible_fibers`.
- Proof-only import Mathlib `AlgebraicTopology.SimplicialSet.CategoryWithFibrations`:
  `SSet.modelCategoryQuillen.I`, with boundary lifting given by
  `CategoryTheory.MorphismProperty.rlp`.
- `lem-cbc-kan-fibration-fiber-criterion` has neither a Lean record nor a Mathlib
  match; its proof-only import is therefore omitted. It is not a statement
  prerequisite, and no other DAG theorem is restated here. Its intended use is
  recorded in step 6 of the theorem docstring.

The theorem docstring carries all six node proof steps: the explicit vertex slice,
right-horn filling by an inner horn one dimension higher, identification of the
Kan fibers, correspondence of boundary lifting problems including dimension zero,
the forward contractible-fiber implication, and the converse fiber criterion.

Edge cases checked before writing:

- `m = 1` is `n = 0`; the chosen boundary vertex is vertex 1, and an extension
  is exactly an edge from the other specified vertex to t. This essential
  nonemptiness condition is retained.
- A one-point quasicategory satisfies both sides. The empty quasicategory has no
  possible t, so there is no spurious nonemptiness assumption on Q.
- For two discrete points and t one of them, both sides fail: the other incoming
  mapping space is empty and its two-vertex boundary has no connecting edge.
- For the nerve of 0 → 1, t=1 satisfies both sides; t=0 fails already in m=1.
- For the one-object nerve BG with nontrivial G, incoming mapping space is not
  weakly contractible; two distinct parallel arrows give a two-boundary that
  cannot fill when the remaining edge is the identity. Higher dimensions are
  genuinely required and have not been discarded.
- The single explicit universe u is that of the supplied simplicial sets and
  dependency constructions; there is no site/coefficient universe restriction.

Searches actually run (the wrapper log is `searches.jsonl`):

- LeanFinder: "A final vertex in a quasicategory has contractible right mapping
  spaces if and only if every simplex boundary ending at that vertex extends".
  Eight hits, including `Quasicategory.hornFilling`, `Quasicategory`, `KanComplex`,
  `StrictSegal.quasicategory`, and `horn₃₂.exists_desc`; none is this criterion.
- Loogle: `"SSet", "boundary", "terminal"`: zero hits.
- Mathlib grep wrapper, AlgebraicTopology:
  `terminal.*boundary|final.*boundary|boundary.*terminal|boundary.*final`: zero hits.
- LeanSearch: "A final vertex of a quasicategory is characterized by extension of
  every simplex boundary whose last vertex is that vertex". Eight hits, primarily
  the quasicategory API and `modelCategoryQuillen.I`; no exact match.
- Direct rg of upstream `WeilConjectures/` and project `lean/Sheaf/` for the same
  boundary/final patterns and the item id: only unrelated prose hits in project
  files, and no upstream result. The separately requested node-id search likewise
  has no upstream occurrence.
- Direct rg of Mathlib, upstream `WeilConjectures/`, project `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for `terminal_iff_boundary_extension`: no collision.
- Direct rg for right-pinched mapping-space terms located the existing enhanced
  framework and right-pinch comparison module. The recorded enhanced framework
  supplies exactly the needed definitions, so no private copy was introduced.

Validation: `scompile.py Q28 lem-cbc-terminal-boundary-extension` compiled the
module as sandbox and library, each within the default 60-second limit, without
errors or warnings. All universes and variables are explicitly bound and
`autoImplicit` is disabled. Lines are at most 100 characters. Only the node's
`lean` field differs from the repository copy. The second reader will write the
independent reading and perform the actual delivery.

## Second reading by Q28

I independently opened the node statement, its source place, the Lean module, and the
recorded dependency declarations. The item-by-item reading is:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| A quasicategory `Q` | `{Q : SSet.{u}} [Quasicategory Q]` | Same simplicial-set object and inner-horn hypothesis. |
| A specified vertex `t` | `(t : Q _⦋0⦌)` | Same chosen vertex. |
| Every vertex `x` | `∀ x : Q _⦋0⦌` | Same quantifier, with no nonemptiness assumption. |
| Incoming right-pinched mapping space | `mappingSpace Q x t` | Exactly the dependency's right-pinched construction: the initial face is constant at `x` and the last vertex is `t`. |
| Contractibility | `IsContractible (mappingSpace Q x t)` | Same weak contractibility convention from the dependency. |
| Equivalence | `↔` | Same two directions. |
| Every integer `m ≥ 1` | `∀ (n : ℕ)` with `m = n + 1` | Bijection with all positive dimensions, with none omitted. |
| Boundary map | `(σ : (∂Δ[n + 1] : SSet.{u}) ⟶ Q)` | Same simplicial-set morphism. |
| Last vertex is `t` | `(boundary.ι (0 : Fin (n + 2)) ≫ σ).app _ (stdSimplex.obj₀Equiv.symm (Fin.last n)) = t` | The zeroth face is `Δ[n] → ∂Δ[n+1]`; its last vertex maps to vertex `n+1`, so this is exactly `σ(n+1)=t`. |
| Extension | `∃ σbar : (Δ[n + 1] : SSet.{u}) ⟶ Q` | Same existential simplex. |
| Restriction | `(boundary (n + 1)).ι ≫ σbar = σ` | Equality is precisely restriction to the boundary. |
| Boundary convention | Mathlib `boundary`; the case used starts at `n+1`, hence positive dimensions | The source's `∂Δ^0 = ∅` convention is compatible and no `m=0` case is accidentally added. |

The source page is Kerodon Proposition the project server (06R1). It states that an object is
final exactly when every `m ≥ 1` boundary map ending at that object extends over
`Δ^m`; the node specializes finality to the dependency's incoming mapping spaces.
The Lean therefore has the same objects, hypotheses, dimension range, vertex
condition, and extension clause. No mismatch was found and no Lean or node statement
was changed. The theorem remains a statement with `sorry`; no result is proved.

Edge cases were checked independently: `m=1` is `n=0`, and the displayed condition
selects the second vertex, so it requires an edge to `t`; the empty simplicial set has
no possible `t`; a one-point simplicial set satisfies both sides; a discrete two-point
set fails for the other vertex; and the nerve of `0 → 1` satisfies the criterion for
`t=1` but fails for `t=0`. There is no characteristic, ring, scheme, or additional
universe restriction. Empty mapping spaces are permitted by the dependency's
contractibility predicate only when the criterion itself fails, as required.

I repeated the existing-definition searches. LeanFinder, Loogle, and LeanSearch
queries for a final/terminal quasicategory vertex characterized by boundary extension
returned only primitive horn, simplex, or ordinary-category declarations. `rg` over
Mathlib, `WeilConjectures/`, project `lean/Sheaf/`, and `dag/lean_names_upstream.json`
found no declaration named `terminal_iff_boundary_extension` and no competing theorem
for this criterion. `rg` confirmed that `mappingSpace` and `IsContractible` are supplied
by `Sheaf.CategoryTheory.EnhancedDiagramsCones`; no private copy was introduced.
The dependency modules and their signatures were read: the enhanced-diagram node
supplies the exact mapping-space convention, while the right-fibration and Kan-fiber
nodes are used only by the documented proof. No dependency node was unusable and no
new definition or dependency module was needed.

The module compiled with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q28 lem-cbc-terminal-boundary-extension`
with no errors or warnings. All variables and universes are explicit under
`autoImplicit false`, and the node's `lean.statement` remains verbatim equal to the
Lean signature. The required `## Worker report` section remains above this section.
