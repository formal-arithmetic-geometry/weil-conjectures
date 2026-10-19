## Worker report

The module `Sheaf.AlgebraicGeometry.ComplementaryPureSubcurveComponents` states
`AlgebraicGeometry.complementary_pure_subcurve_components`. Its only theorem has
proof `sorry`; no definitions or proofs are added. The node statement and
statement dependencies are unchanged.

The source was read in `literature/stacks-project/curves.tex`, Tag 0E38,
`lemma-closed-subscheme-nodal-curve`, first proof paragraph: reduced pure
one-dimensional closed subschemes are unions of components. The node expands the
complement and double-complement consequences without the unnecessary nodal or
field hypotheses. The node's six proof steps are all reproduced in the docstring.

Hypothesis and clause correspondence:

- The ambient scheme is `X : Scheme.{u}`. `[IsReduced X]` expresses reducedness.
  `[IsNoetherian X]` is Mathlib's class extending `IsLocallyNoetherian X` and
  `CompactSpace X`: locally Noetherian and quasi-compact, precisely the node's
  explicit meaning of Noetherian. No separation or base-field hypothesis is added.
- `hX : ∀ C ∈ irreducibleComponents X, topologicalKrullDim C = 1` is the dimension
  condition on every ambient component. Here a set coerces to its subtype with
  the subspace topology, and the numeral has type `WithBot ℕ∞`.
- `i : Y ⟶ X`, `[IsClosedImmersion i]`, and `[IsReduced Y]` give the reduced closed
  subscheme Y. `hY` repeats the dimension-one condition for its own components.
- `j : Z ⟶ X`, `[IsClosedImmersion j]`, `[IsReduced Z]`, and
  `hZ : Set.range j = closure ((Set.range i)ᶜ)` specify exactly the reduced induced
  closed subscheme on that closure. These are the defining properties of Z,
  not an added geometric restriction. The recorded dependency
  `reduced_induced_closed_subscheme` ensures both existence of such a model and
  uniqueness up to a unique isomorphism over X. Thus quantifying over its reduced
  closed-immersion models is equivalent to the node's instruction to take Z.
- `∃ I : Set (Set X), I ⊆ irreducibleComponents X` selects a subset of the
  component set. This ambient set is finite by the imported Mathlib theorem
  `finite_irreducibleComponents_of_isNoetherian`; it is not an extra assumption.
- `Set.range i = ⋃₀ I` identifies Y with the selected union. In conjunction with
  its reducedness and closed immersion this identifies its reduced closed scheme
  structure too, by uniqueness in the recorded reduced-induced dependency. A
  topological union is closed since I is finite and its members are components.
- `Set.range j = ⋃₀ (irreducibleComponents X \ I)` is the remaining-component
  union. Again Z is already a reduced closed immersion, so the same uniqueness
  theorem gives equality as reduced closed subschemes, not just supports.
- `∀ C ∈ irreducibleComponents Z, topologicalKrullDim C = 1` gives the component
  dimension assertion for Z itself, not for a different ambient subset.
- The final `∃ e : Y ≅ (vanishingIdeal (Closeds.closure ((Set.range j)ᶜ))).subscheme`
  with `e.hom ≫ ...subschemeι = i` identifies the double complementary reduced
  closure with Y **over X**. This expresses equality of closed subschemes rather
  than an abstract scheme isomorphism or a bare support identity. The existing
  canonical vanishing-ideal construction supplies the specified reduced scheme;
  no arbitrary map or choice of a new construction is used.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced`, the
  scheme `QuasiSober` and `T0Space` instances; the sobriety proof dependency uses
  `QuasiSober.sober` and `IsGenericPoint.eq` from `Mathlib.Topology.Sober`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  `AlgebraicGeometry.IsNoetherian`, and the proof input
  `AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`,
  `isClosed_of_mem_irreducibleComponents`,
  `exists_mem_irreducibleComponents_subset_of_isIrreducible`,
  `mem_irreducibleComponent`, and `irreducibleComponent_mem_irreducibleComponents`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`;
  its existing `vanishingIdeal`, `subscheme`, and `subschemeι` construction is
  used literally in the conclusion. The recorded side module is imported to
  avoid the known duplicate declaration in the upstream counterpart.
- The sole additional non-public proof import is
  `Sheaf.Topology.IrreducibleOpenComplementDimension`, declaration
  `irreducible_open_complement_dimension`. Other proof dependencies are in the
  public Mathlib imports or the reduced-induced module. No import cycle arises.

Edge cases checked before writing:

- Empty X forces Y and Z empty through their scheme maps. I is empty and all
  three component-dimension assertions are vacuous; there is no `Nonempty` or
  `IrreducibleSpace` hypothesis excluding this case.
- Empty Y gives I empty and Z the reduced ambient X. Its complementary closure
  is empty again. Empty Z gives I the entire component set and Y the reduced X.
- Components may intersect: `irreducibleComponents X \ I` is a complement in
  the **set of components**, not the pointwise complement of their union. The
  closures in hZ and the double-complement clause retain intersection points.
- An irreducible X permits only the empty or entire pure subcurve; a proper
  closed zero-dimensional subscheme fails hY as intended. Isolated ambient
  zero-dimensional components fail hX, as the node requires.
- All schemes are in the same arbitrary universe u, the standard scheme
  category of the recorded reduced-induced uniqueness declaration; there is no
  field, characteristic, finite-type, separation, or nonempty restriction.

Searches performed for an existing exact statement:

- `msearch.py leanfinder`: “A reduced pure one dimensional closed subscheme of a
  reduced Noetherian curve is a union of irreducible components and the
  complementary closure is the remaining union”. Eight hits: coproduct range
  complements, zero loci, scheme sobriety, coborderRange, component finiteness,
  and integral/irreducible equivalences. None states the theorem.
- `msearch.py loogle`: `irreducibleComponents, topologicalKrullDim`; zero hits.
- `msearch.py grep`: `subcurve|pure.*dimension|complementary.*component` in
  `AlgebraicGeometry`; zero hits.
- `msearch.py leansearch`: “A reduced pure one dimensional closed subscheme of a
  reduced Noetherian scheme is a union of irreducible components”. Eight hits
  give finite irreducible closed decompositions, `irreducibleComponents`,
  component finiteness and reduced/irreducible equivalences, not this statement.
- `rg` in the upstream `WeilConjectures` and side `lean/Sheaf` sources for the
  item id, `complementary.*component`, and `pure.*subcurve`: unrelated uses of
  complementary components only, no matching statement. Further searches for
  reduced complementary closures found uses in open-closed arguments, not this
  theorem. The final declaration name was also searched in Mathlib, upstream,
  side sources and `dag/lean_names_upstream.json`, without a hit.

No statement correction, missing notion, dependency repair, or disputed statement
was needed. Initial per-file `scompile.py` validation passed both local and
library checks with no errors or warnings. The final delivery dry run repeats
compilation after explicitly listing all statement-dependency module imports.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
