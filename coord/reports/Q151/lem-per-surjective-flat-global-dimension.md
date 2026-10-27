## Worker report

The module `Sheaf.AlgebraicGeometry.SurjectiveFlatGlobalDimension` states
`AlgebraicGeometry.topologicalKrullDim_eq_add_of_surjective_flat_constantRelativeDimension`.
Its only proof is `by sorry`; it introduces no definitions. The node changes only in `lean`.
No new nodes, dependency repairs, statement changes, or statement disputes are needed.

Read the complete node and its six statement dependencies, their recorded declarations,
and Stacks `morphisms.tex`, lemma-rel-dimension-dimension (Tag 0AFE), particularly
its second proof paragraph. The source's global formula is the intermediate assertion
following the shrinking to a surjective map. The item's stage-1 proof explicitly expands
its supremum argument and includes nonempty Y.

Hypothesis and clause correspondence:

- Schemes and their morphism: `{X Y : Scheme.{u}}` and `(f : X ⟶ Y)`.
  The universe `u` is explicit and arbitrary.
- Locally Noetherian source and target: `[IsLocallyNoetherian X]` and
  `[IsLocallyNoetherian Y]`; no global Noetherian or quasi-compact hypothesis.
- Flat morphism: `[Flat f]`, the recorded Mathlib notion, equivalent to flatness
  of all stalk maps by `Flat.iff_flat_stalkMap`.
- Locally of finite type: `[LocallyOfFiniteType f]`, retaining precisely the local
  condition, with no quasi-compactness or finite-presentation assumption added.
- Natural relative dimension: `(d : ℕ)`, allowing zero.
- Scheme-theoretic fibre over f(a): `f.fiber (f a)` is Mathlib's pullback of f
  along `Y.fromSpecResidueField (f a)`.
- The corresponding point of this fibre: `f.asFiber a`, constructed using the
  recorded fibre homeomorphism. Its projection to X is a by `fiberι_asFiber`.
- Local dimension equals d at every a: the single hypothesis
  `(hd : ∀ a : X, topologicalKrullDimAt (f.asFiber a) = (d : WithBot ℕ∞))`.
  This uses the infimum of dimensions of open neighbourhoods, not the dimension
  of the fibre local ring. It has exactly the same quantification as the node.
- Surjectivity on underlying points: `[Surjective f]`, the class in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, whose field is
  `Function.Surjective f`.
- Nonempty target: `[Nonempty Y]`, explicitly retained.
- Global formula: `topologicalKrullDim X = topologicalKrullDim Y + (d : WithBot ℕ∞)`.
  Both sides use the recorded global topological dimension, and addition in
  `WithBot ℕ∞` includes infinity plus a finite natural number equal to infinity.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
  The affine-cover equivalence is already recorded on pqf-def-locnoeth.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and its
  stalkwise equivalence `Flat.iff_flat_stalkMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`, `fiberHomeo`, and `asFiber`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`,
  exactly the infimum over open neighbourhoods specified by the node.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, defined by chains of
  irreducible closed subsets and valued in `WithBot ℕ∞`.

The proof plan's recorded modules are imported without `public`:
`Mathlib.AlgebraicGeometry.AffineScheme` (affine stalk localization),
`Mathlib.RingTheory.Localization.Submodule` (`IsLocalization.isNoetherianRing`),
`Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
(`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`),
`Mathlib.RingTheory.Ideal.GoingDown` (flat implies going down),
`Mathlib.RingTheory.KrullDimension.Basic` (`ringKrullDim`),
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`
(`Scheme.Hom.fiberStalkMap_surjective_ker_quotientEquiv`),
`WeilConjectures.Topology.DimensionSupremumLocalDimensions`
(`topologicalKrullDim_eq_iSup_topologicalKrullDimAt`), and
`WeilConjectures.AlgebraicGeometry.Dimension` (`Scheme.dim_eq_topologicalKrullDim`).
The docstring records all four proof steps, including finite supremum attainment
on each fibre and on the base. No imported consumer theorem is used as a dependency.

Edge cases checked mathematically before writing:

- d = 0: identity maps over any nonempty locally Noetherian base satisfy the
  hypotheses and give dimension X = dimension Y.
- Empty target: explicitly excluded, as in the node; no silent empty-supremum
  convention is used. Empty source over nonempty target cannot be surjective.
- Affine line over a field: d = 1 at every fibre point in the neighbourhood sense,
  including its generic point. The generic point's local ring instead has
  dimension zero, confirming why the stated hypothesis must use the topological
  local dimension rather than stalk dimension.
- Unbounded global dimension: a disjoint union of affine spaces of increasing
  dimensions is locally Noetherian; its identity has d = 0 and infinite global
  dimension. No finite-dimensionality assumption excludes this case.
- Surjectivity is substantive: an open and closed component of a disconnected
  base can have smaller dimension than another component. A nonsurjective open
  immersion with d = 0 would not suffice for the conclusion.
- No characteristic, irreducibility, separatedness, finiteness of components,
  or irreducible-component equidimensionality hypothesis has been imposed.

Searches actually run (2026-10-23):

1. `msearch.py ... leanfinder` query:
   "A surjective flat locally finite type morphism of locally Noetherian schemes
   with constant local fibre dimension d has source dimension equal to target
   dimension plus d". Eight hits: smooth relative dimension and standard smooth
   algebra interfaces, Flat, flat descent, flat mono, and flat epimorphism results.
   None states the global dimension formula.
2. `msearch.py ... loogle` query `"Flat", "topologicalKrullDim"`: zero hits.
3. `msearch.py ... grep` query
   `(flat|Flat).*(krullDim|KrullDim)|(krullDim|KrullDim).*(flat|Flat)` in
   `AlgebraicGeometry`: zero hits.
4. `msearch.py ... leansearch` query:
   "Surjective flat locally finite type morphism of locally Noetherian schemes
   with constant fibre dimension d has dimension of source equal to dimension
   of base plus d". Eight hits: flat mono, affine faithful flatness, proper implies
   locally finite type, smoothness, flat epimorphism, flat stalk maps, Surjective,
   flat quotient map. No exact dimension formula.
5. `rg` in both live `lean/WeilConjectures` and `lean/Sheaf` for
   `(flat|Flat|surjective).*(krullDim|KrullDim)|(krullDim|KrullDim).*(flat|Flat|surjective)`.
   Inspected `Sheaf.AlgebraicGeometry.FlatConstantRelativeDimension`: its result
   concerns local dimensions and is the parent, not this global statement.
   The upstream quasi-finite result requires universally closed and quasi-finite
   and gives equality, so also is not an exact match. Other hits are ring bounds
   or unrelated applications.
6. `grep -rn lem-per-surjective-flat-global-dimension lean/WeilConjectures`:
   no hits. Name search for the chosen theorem in Mathlib, upstream, Sheaf, and
   `dag/lean_names_upstream.json` found no existing declaration of that name.

## Second reading by Q151

Self-check after opening the node, module, recorded definitions, and source again:
the signature retains both Noetherian hypotheses, flatness, local finite type,
natural d, the universal local fibre-dimension hypothesis, surjectivity, and
nonempty Y. Its conclusion is the global dimension equality in the prescribed
extended dimension type. The point is `asFiber a`, whose source signature puts
it in the fibre over f(a). In particular it does not assert that every fibre
stalk has dimension d. The proof docstring explicitly distinguishes those notions.
No mismatch or further edit was found. This is a worker self-check, not an
independent reader's review; the dispatcher instruction prohibits other agents,
and the maintainer supplies the independent review of this delivery.
