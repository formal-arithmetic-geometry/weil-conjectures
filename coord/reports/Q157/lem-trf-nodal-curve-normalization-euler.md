## Worker report

The module `Sheaf.AlgebraicGeometry.NodalCurveNormalizationEuler` states
`AlgebraicGeometry.Scheme.nodal_curve_normalization_euler` with proof `sorry`. It gives the
Euler characteristic of the structure sheaf of a proper, reduced, connected, pure
one-dimensional nodal `k`-scheme as the number of irreducible components minus the finite
nonsmooth-point count minus the sum of the genera of the canonical normalizations of those
components.

The hypotheses and clauses are rendered as follows.

- The algebraically closed base field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The curve is `B : Scheme.{u}` with `[B.Over (Spec (.of k))]`, and properness of its
  structure morphism is `[IsProper (B ↘ Spec (.of k))]`.
- Reducedness and connectedness are `[IsReduced B]` and `[ConnectedSpace B]`.
- Pure dimension one is the exact componentwise condition
  `hpure : ∀ Z : Set B, Z ∈ irreducibleComponents B → topologicalKrullDim Z = 1`.
  This is the recorded pure-dimension formulation using the Krull-dimension dependency;
  it also leaves the empty-component convention of that definition intact.
- The nodal completed-local-ring hypothesis at every nonsmooth point is `hnodal`. Its
  completion is `AdicCompletion (IsLocalRing.maximalIdeal (B.presheaf.stalk x))
  (B.presheaf.stalk x)`, and the specified split node is
  `MvPowerSeries (Fin 2) k ⧸ Ideal.span {X 0 * X 1}`.
- `N : Set B` and `hN : N = {x : B | x ∉ (B ↘ Spec (.of k)).smoothLocus}` identify the
  finite set of internal nodes (all nonsmooth points are nodal by `hnodal`). Its size is
  rendered by `(N.ncard : ℤ)` in the conclusion.
- `v : ℕ` and `components : Fin v ≃ irreducibleComponents B` enumerate all irreducible
  components exactly once, including the possibility of an empty index type at the type
  level.
- `Z : Fin v → Scheme.{u}` with `[∀ a : Fin v, IsIntegral (Z a)]` supplies the reduced
  component schemes. The maps `j : ∀ a, Z a ⟶ B` with
  `[∀ a, IsClosedImmersion (j a)]` and
  `hcomponents : ∀ a, Set.range (j a) = (components a).1` identify their underlying
  components.
- For each component, `Z a).fromNormalization` is the recorded canonical normalization
  morphism. `hnormalizations` states that its composite to `Spec k` is proper and smooth
  and that `(Z a).normalization` is connected. Thus the genus term is exactly
  `(((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ)`, using the recorded
  `Scheme.Hom.genus` declaration.
- The conclusion is
  `Scheme.Modules.eulerChar k (Modules.unit B) = (v : ℤ) - (N.ncard : ℤ) -
  ∑ a : Fin v, (((Z a).fromNormalization ≫ j a ≫ B ↘ Spec (.of k)).genus : ℤ)`.
  `Modules.unit B` is the structure sheaf as an object of `B.Modules`, and
  `Modules.eulerChar` is the recorded Euler-characteristic definition.

Dependency declarations used:

- `AlgebraicGeometry.Scheme.nodal_normalization_quotient` from
  `Sheaf.AlgebraicGeometry.NodalNormalizationQuotient`. I read its full signature and
  docstring: it uses the same field, proper/reduced/connected/pure-dimension and split-node
  hypotheses, and supplies the normalization short exact sequence and the equality
  `Q.eulerChar k = (N.ncard : ℤ)`.
- `AlgebraicGeometry.Scheme.fromReducedNormalization` and
  `AlgebraicGeometry.Scheme.reducedNormalizationComponent` from
  `Sheaf.AlgebraicGeometry.ReducedNormalization`, used through the existing canonical
  normalization construction on each integral component. Their definitions and
  docstrings were read; no private normalization copy is introduced.
- `AlgebraicGeometry.Scheme.Hom.genus` from
  `WeilConjectures.AlgebraicGeometry.Curve`, whose full signature and docstring define the
  genus of a morphism as the finite-dimensional differential-form dimension.
- `AlgebraicGeometry.Scheme.Modules.eulerChar` and `Modules.unit` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, whose full signatures and docstrings
  define the alternating cohomological dimension sum and the structure-sheaf object.
- `AlgebraicGeometry.IsProper` from `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsReduced` from `Mathlib.AlgebraicGeometry.Properties`,
  `ConnectedSpace` from `Mathlib.Topology.Connected.Basic`, `topologicalKrullDim` and
  `irreducibleComponents` from `Mathlib.Topology.KrullDimension` and
  `Mathlib.Topology.Irreducible`, `AdicCompletion` from
  `Mathlib.RingTheory.AdicCompletion.Basic`, `MvPowerSeries` from
  `Mathlib.RingTheory.MvPowerSeries.Basic`, and `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`. These are used exactly in the displayed
  hypotheses and component conditions.

Edge cases checked before writing: `v = 0` remains syntactically allowed (and is ruled out
for a connected nonempty curve by the component equivalence); `N = ∅` gives the smooth-curve
formula; a self-node is one point of `N` and hence contributes once; a curve with one
component gives `1 - e - g`; genus zero gives the expected component-minus-node value; and
all universes are tied to the scheme and field universe `u`. No characteristic, finite-field,
projectivity, or extra connectedness hypothesis was added.

Searches made:

- `msearch.py Q157 lem-trf-nodal-curve-normalization-euler leanfinder "Euler characteristic
  structure sheaf proper connected nodal curve normalization components nodes genus"`: returned
  normalization-coproduct and generic normalization declarations, with no nodal Euler formula.
- `msearch.py Q157 lem-trf-nodal-curve-normalization-euler loogle "eulerChar, genus,
  irreducibleComponents"`: zero hits (unknown `eulerChar` identifier in Loogle).
- `msearch.py Q157 lem-trf-nodal-curve-normalization-euler grep
  "nodal.*Euler|Euler.*nodal|normalization.*Euler" Mathlib/AlgebraicGeometry`: zero hits.
- `rg` over `WeilConjectures/` and `lean/Sheaf/` for
  `nodal_curve_normalization_euler`, the node id, and nodal/normalization Euler patterns:
  no existing declaration of this statement; only the separate normalization quotient and
  contraction-defect statements were found.
- The dependency node records and their source declarations were opened in full. The
  recorded `mathlib_match` leaves were checked against their signatures before use.

No new definition node, dependency-interface repair, statement correction, or
`STATEMENT-DISPUTED` flag is needed.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
