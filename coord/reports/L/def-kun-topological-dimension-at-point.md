# def-kun-topological-dimension-at-point (L, stage 2)

## Worker report

Worker W-dim0510 for L, stage 2, item `def-kun-topological-dimension-at-point`. **Existing declaration; no module written.**

The source repository already defines the notion (brief §1, one definition per notion):
`WeilConjectures/Mathlib/Topology/KrullDimension.lean:333` (module `WeilConjectures.Mathlib.Topology.KrullDimension`,
compiled, root namespace, variables `{X : Type*} [TopologicalSpace X]`):

```lean
noncomputable def topologicalKrullDimAt (x : X) : WithBot ℕ∞ :=
  ⨅ (U : Opens X) (_ : x ∈ U), topologicalKrullDim U
```

Docstring: "the local dimension dim_x X ... the infimum of the topological Krull dimensions of the open
neighbourhoods of x [Stacks 04NA]". Body is not sorry. The repository also has
`topologicalKrullDimAt_eq_of_forall` and `IsOpen.topologicalKrullDimAt_eq`, and
`AlgebraicGeometry/Morphisms/Smooth.lean` uses it (smooth of relative dimension n gives dim_x = n).

Clause by clause:
- "X a topological space, x ∈ X": `{X : Type*} [TopologicalSpace X] (x : X)`; any universe.
- "open neighbourhoods U of x": `(U : Opens X) (_ : x ∈ U)`. A probe compile showed this is equal to
  `⨅ U : TopologicalSpace.OpenNhdsOf x, topologicalKrullDim U` (proved by `le_antisymm`, `le_iInf`,
  `iInf₂_le`, `le_iInf₂`, `iInf_le_of_le`), so it is the same as the form the node's searches suggested.
- "Krull dimension of U with the subspace topology": `topologicalKrullDim ↥U` (Mathlib,
  `Mathlib/Topology/KrullDimension.lean`; the subtype topology `instTopologicalSpaceSubtype`).
- "the minimum": the infimum in the complete lattice `WithBot ℕ∞`. The infimum is attained because `WithBot ℕ∞` is
  well-ordered and the family is nonempty (`⊤ : Opens X` contains x) (`ciInf_mem`,
  lem-kun-extended-naturals-minimum), so inf = min. The repository has no separate attainment theorem, and the node
  does not need one because its "minimum exists" is only the justification inside the definition.
- "an element of {0,1,…,∞}": the codomain is `WithBot ℕ∞`, as for Mathlib's `topologicalKrullDim`. The value is never
  ⊥ because every open neighbourhood contains x and so is nonempty, and a nonempty space has dimension ≥ 0. This is
  not a separate Lean statement, and none is needed for the definition. Keeping `WithBot ℕ∞` avoids a coercion and
  matches the downstream uses in the source repository.

Codomain choice: `WithBot ℕ∞` (the existing declaration's). It is the direct infimum and is the lead's preferred form.

Edge cases: the empty X has no points, so the case does not arise. A point with only X as a neighbourhood gives
dim X. ∞ is allowed (`⊤`).

Searches:
- grep of Mathlib: only `Topology/KrullDimension.lean` and `RingTheory/Spectrum/Prime/Topology.lean` mention
  `topologicalKrullDim`. Neither file uses `OpenNhdsOf` or nhds with it. No `topologicalKrullDimAt` or `krullDimAt`
  in Mathlib.
- grep of `~/weil-conjectures-slopmaster2/WeilConjectures` for `topologicalKrullDimAt`: the definition above
  (KrullDimension.lean:333) and its uses in `AlgebraicGeometry/Morphisms/Smooth.lean`.
- `dag/lean_names_upstream.json` has no entry naming this node, and the source repository has no blueprint tag for
  it. The match comes from the name and the docstring.

Record: `lean/.sandbox/L/def-kun-topological-dimension-at-point.lean-record.json` (`existing: true`,
`branch: slopmaster2`). Node faults: none. STATEMENT-DISPUTED: none.

## Second reading by L

L read WeilConjectures/Mathlib/Topology/KrullDimension.lean:331-334: the definition is the node's (existing: true).
