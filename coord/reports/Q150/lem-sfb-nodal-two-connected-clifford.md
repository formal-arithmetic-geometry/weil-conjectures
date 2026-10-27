## Worker report

The module `Sheaf.AlgebraicGeometry.NodalTwoConnectedClifford` states
`AlgebraicGeometry.nodal_two_connected_clifford`, with its sole proof `by sorry`.
There are no definitions, auxiliary theorems, new nodes, dependency replacements,
or changes to the mathematical node. The node copy changes only `lean`.

Source read: the author-hosted primary PDF
https://pagine.dm.unipi.it/franciosi/lavori/franciosi-tenni2.pdf,
Section 2, Definition 2.2, Definition 2.6, Theorem 2.7 (printed pp.39--41).
Theorem 2.7's Cartier case gives the subcanonical cluster bound; converting the
specified generically nonzero map to its Cartier zero scheme and using
Riemann--Roch gives exactly the node's line-bundle inequality. The module docstring
carries all four accepted proof steps, including cancellation of the splitting
correction and the Euler-degree calculation.

Hypothesis and clause correspondence:

- Algebraically closed field: `(k : Type u) [Field k] [IsAlgClosed k]`.
  These binders impose no restriction on the characteristic.
- Projective k-scheme: `(X : Scheme.{u}) [X.Over (Spec (.of k))]` and
  `[IsHProjective (X ↘ Spec (.of k))]`, the recorded finite-projective-embedding
  convention. The structure map is used consistently for all scalar restrictions.
- Nonempty connected: `[ConnectedSpace X]`; its `toNonempty` field supplies
  nonemptiness, so there is no redundant extra hypothesis.
- Reduced: `[IsReduced X]`.
- Pure dimension one: `hpure : X.IsPureDimension 1`, which quantifies over
  every irreducible component with its subspace Krull dimension.
- Smooth except at ordinary nodes: `hnodal` quantifies over singular closed
  points, i.e. closed singletons outside the structure morphism's `smoothLocus`.
  It supplies the maximal-ideal-adic completion ring isomorphism with
  `MvPowerSeries (Fin 2) k ⧸ Ideal.span {X 0 * X 1}`. Its explicit equality
  for every `a : k` says that this is an isomorphism of completed local
  k-algebras, not merely an abstract ring isomorphism. On this reduced
  finite-type pure curve over the perfect field k, nonclosed points are
  the component generic points and are smooth. Thus the closed-point
  formulation covers precisely all possible singularities.
- Every decomposition into two reduced nonempty unions of distinct components:
  `htwo` quantifies over schemes A and B and their closed immersions a,b into X,
  requires `IsReduced A`, `IsReduced B`, and their nonemptiness. Its sets P,Q
  are subsets of `irreducibleComponents X`, disjoint and exhaustive. The range
  equalities with `⋃₀ P` and `⋃₀ Q` identify A,B with the reduced component
  unions. In a Noetherian scheme their reduced closed structures are unique;
  this quantification neither admits arbitrary thickenings nor omits a union.
- Scheme-theoretic finite intersection and length at least two:
  `pullback a b`, with the scalar map obtained from
  `pullback.fst a b ≫ a ≫ X ↘ Spec (.of k)`. The bound is literally
  `2 ≤ @Module.finrank k Γ(pullback a b, ⊤) _ _ (Module.compHom _ ...)`.
  Thus length is the dimension of global functions, including the scheme
  structure, not the number of intersection points. Finiteness follows from
  projectivity and the absence of any shared component, and is not imposed
  as an extra hypothesis.
- The specified omega: `(ω : X.Modules) [ω.IsInvertible]`, with `e` the
  k-linear coherent-module Serre-duality representing isomorphisms and `he`
  their naturality under every coherent morphism. This is exactly the
  specification supplied by `exists_nodal_line_serre_riemann_roch`, not an
  arbitrary invertible module. Coherence on the projective locally Noetherian
  curve is expressed by `IsQuasiCoherentFiniteType`, as in that dependency.
  Existence and uniqueness are provided by the dependency; the statement
  applies to every such representing choice and uses no arbitrary choice.
- Invertible M: `(M : X.Modules) [M.IsInvertible]`.
- A single section nonzero at every component generic point: `hs` is
  `∃ s : Γ(M, ⊤), ∀ C : irreducibleComponents X, germ ... s ≠ 0`.
  The existential is outside the universal: this is one common section.
  `genericPoints.ofComponent` chooses the unique generic point of each
  scheme component. No component is omitted, including self-nodal ones.
- A single map M to omega nonzero at all component generic points: `hφ`
  is `∃ φ : M ⟶ ω, ∀ C, (RingedSpace.moduleStalkFunctor ...).map φ ≠ 0`.
  This is nonzero as a linear map on the generic stalk, not just nonzero
  globally or nonzero on one chosen component.
- Zariski module-sheaf cohomology: `scalarCohomology (X ↘ Spec (.of k)) M 0`
  is the existing `RingedSpace.moduleCohomology` object with scalars restricted
  to k along the structure map. Its finrank is h0 as stipulated by the node.
- The conclusion is
  `2 * (Module.finrank k (scalarCohomology ... M 0) : ℤ) ≤ degree k M + 2`.
  Multiplying the displayed rational inequality by positive two gives exactly
  this integer inequality, including odd degrees. `Scheme.Modules.degree`
  is the recorded Euler-characteristic difference; no componentwise replacement
  degree or multidegree assumptions are introduced.

Dependency declarations read and used:

- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsHProjective` (finite-coordinate projective embedding).
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, through the recorded pure-dimension definition.
- `def-pc-degree-line-bundle`:
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`,
  `AlgebraicGeometry.Scheme.Modules.degree`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`,
  `AlgebraicGeometry.IsReduced`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth`, via the structure morphism's `smoothLocus`.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `def-sc-ringed-space-module-cohomology`:
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.moduleCohomology`, used through
  `Scheme.Modules.scalarCohomology` in
  `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
  The same module supplies `scalarMap` and `scalarCohomologyMap`.
- `def-weil-algebraic-closure`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed` (the algebraically-closed-field clause of its mathlib match).
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`,
  `ConnectedSpace` (its mathlib match).
- `def-weil-irreducible-components`: `Mathlib.Topology.Irreducible`,
  `irreducibleComponents` (its mathlib match).
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`
  and `.Algebra`, `AdicCompletion` and `AdicCompletion.of`.
- `def-weil-pbc-multivariate-power-series`:
  `Mathlib.RingTheory.MvPowerSeries.Basic`, `MvPowerSeries` and `MvPowerSeries.X`.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`,
  `AlgebraicGeometry.Scheme.IsPureDimension`.
- `lem-sfb-nodal-line-serre-riemann-roch`:
  `Sheaf.AlgebraicGeometry.NodalLineSerreRiemannRoch`,
  `AlgebraicGeometry.exists_nodal_line_serre_riemann_roch`. Its full signature
  and docstring were read: the omega, duality and naturality binders reproduce
  its representing specification. The explicit scalar compatibility in our
  nodal hypothesis implies the ring-isomorphism hypothesis it accepts.
- Generic germs use `genericPoints.ofComponent` (`Mathlib.Topology.Sober`),
  `TopCat.Presheaf.germ`, and the existing
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`
  (`WeilConjectures.Algebra.Homology.ModuleStalkFunctor`).

All recorded modules of already stated proof dependencies are imported privately:
`SubcanonicalSplittingIndex`, `Morphisms.ProjectiveImpliesProper`,
`EulerCharZeroDimSupport`, `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`,
and `ReducedCurveDualizingModule`. Degree is already public. The local nodes
`lem-sfb-nodal-linear-series-base-colength`,
`lem-sfb-subcanonical-splitting-clifford-bound`, and
`lem-trf-proper-field-invertible-coherent` had no Lean record when read;
their proof steps are retained in the docstring, without inventing declarations.

Edge cases checked before writing:

- Irreducible X: a partition into two nonempty unions cannot exist, so `htwo`
  is vacuous exactly as stated. Self-nodes do not produce component partitions.
- Empty scheme is excluded by connectedness; the universal quantifiers over
  component partitions do not silently make the whole theorem vacuous.
- Empty zero divisor (M = omega) is allowed; the inequality becomes the
  canonical equality 2g = (2g-2)+2.
- Genus one with M = O has h0 = 1, degree zero and equality, including a cycle
  of rational components and two rational components meeting at two nodes.
- A separating single node fails `htwo` since its intersection algebra has
  dimension one. Multiple intersection nodes and nontrivial scheme structure
  are measured by global functions rather than point counting.
- On P1 two-connectedness is vacuous, but an effective M cannot also map
  generically nontrivially to omega = O(-2); the theorem assumes no positive genus.
- Odd and negative integer degrees are interpreted in integers; no natural
  subtraction, floor division, characteristic-zero assumption, or fixed number
  of components is used.

Searches actually run:

- `msearch.py ... leanfinder "Clifford inequality for line bundle sections on a
  two connected nodal projective curve"`: eight hits on division polynomials,
  elliptic coordinate rings and unrelated Weierstrass bounds; no curve Clifford
  inequality.
- `msearch.py ... loogle '"Clifford"'`: twelve hits on Clifford algebras and
  their constructors/maps; no curve theorem.
- `msearch.py ... grep 'Clifford|subcanonical|TwoConnected' AlgebraicGeometry`:
  fifteen hits, concerning subcanonical sites and related topology, no match.
- `rg` in both `lean/WeilConjectures/AlgebraicGeometry` and
  `lean/Sheaf/AlgebraicGeometry` for two-connectedness, generic nonvanishing,
  nodal Clifford and Clifford: upstream hits are unrelated Clifford-algebra
  Koszul constructions. Project hits include `SubcanonicalResidualDuality`,
  `SubcanonicalSplittingIndex`, `NodalSpecialCliffordSubcurve` and generic-stalk
  lemmas. Those were inspected where relevant; none states this inequality for
  all M with the node's hypotheses. Residual duality's `hTwoConnected` provides
  the established partition encoding; here the node's length is written directly
  as global functions.
- `grep -rn 'lem-sfb-nodal-two-connected-clifford' lean/WeilConjectures`: no hit.
- Final `rg` over `lean/Sheaf` and `lean/WeilConjectures` for
  `nodal_two_connected_clifford|nodal-two-connected-clifford|two.connected.clifford`:
  no existing declaration.

No STATEMENT-DISPUTED flag or mathematical node fault was found. No repair note
exists for the item. Compilation and delivery validation use only scompile.py
and deliver2.py; no live file or direct Git mutation is performed.

## Second reading by Q150

The dispatcher forbids other agents and assigns independent review to the
maintainer. This section records my own rereading, not a claim of independent
agent review. I compared the complete node with the complete declaration again:
`ConnectedSpace` includes nonemptiness; the nodal condition preserves k-scalars;
P,Q partition all components and exclude a shared component; the intersection
length is Gamma of the actual fibre product; both nonvanishing existentials
quantify over one section/map before all components; omega has natural coherent
Serre duality; and the integer inequality is algebraically equivalent to the
node's displayed bound with the recorded degree. The initial compiler namespace
error (`open Scheme.Modules` outside AlgebraicGeometry) was corrected to the
fully qualified namespace; it did not alter any hypothesis. No mathematical
statement change was needed.
