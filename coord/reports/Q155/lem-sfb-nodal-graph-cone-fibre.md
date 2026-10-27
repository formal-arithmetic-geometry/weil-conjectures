## Worker report

The module `Sheaf.AlgebraicGeometry.NodalGraphConeFibre` states
`AlgebraicGeometry.GraphCone.Nodal.exists_nodalGraphCone_comparison` with `sorry`.
All auxiliary definitions have real data; the result structures describe the clauses
of this node rather than postulate any new input hypothesis.

Hypothesis and conclusion correspondence:

- A field and locally finite type curve are `k`, `[Field k]`, `C`, `f`, and
  `[LocallyOfFiniteType f]`. No separatedness, properness, connectedness, or global
  quasi-compactness hypothesis is imposed.
- The geometric-fibre hypothesis quantifies over all algebraically closed fields
  `Ω : Type u` and all maps `g : Spec Ω ⟶ Spec k`. The implication from `Nonempty`
  preserves empty fibres. `IsPureDimension 1` uses the recorded componentwise
  dimension definition. Nonsmooth points are outside `(pullback.snd f g).smoothLocus`.
  `IsGeometricOrdinaryDoublePoint` is the existing maximal-ideal completion isomorphism
  with `MvPowerSeries (Fin 2) Ω / (X 0 * X 1)`.
- `singularDiagram f` is exactly the first-Fitting closed singular subscheme and
  its inclusion. `F : GraphCone.Construction` is the simultaneous canonical construction
  of the recorded gluing dependency; the assertion holds for every such construction.
- `PointBase.openPoint`, `singleton`, `scalarIso`, `scalarIso_apply`, and `residueIso`
  specify the open scheme `Spec κ(x)` with its canonical evaluation, not an abstract
  one-point topological space. `finite` and `separable` use the structural residue-field
  map. The singleton open subschemes cover D because the pointwise data are indexed by every
  point of D. This is precisely the disjoint open-point decomposition; no finite
  index or enumeration is assumed.
- `tensorRing`, `tensorAugmentation`, `graphPrime`, and `graphRing` explicitly construct
  `A ⊗[k] κ`, its multiplication-to-residue augmentation, its kernel prime, and the
  localization at that prime. `pointAmbient`, `pointGraph`, and `graphPoint` construct the
  actual graph point in the scheme fibre product.
- `LocalComparison.localStalk` identifies this localization with the actual graph stalk.
  Its two projection equations specify the map on both tensor factors. `graphIdeal` is
  the extended graph prime. `quotient`, `quotient_scalars`, and `quotient_original`
  identify H/J with κ and its actual residue map. `ideal_comap` is J intersect A = m.
- `LocalComparison.graphGraded` is gr_m A ≃ gr_J H. `graphGraded_apply` sends every
  homogeneous representative a to its actual image under A → H; consequently it
  preserves degrees and the degree-zero residue action.
- `PointGraded.toTangent`, `bijective`, `homogeneous`, and `scalar` express the graded
  algebra isomorphism from the restriction of G to the singleton. `fibreRing` is the
  actual tensor product with κ using its evaluation map. `fibreIso`, `fibreIso_include`,
  and `fibreIso_scalar` give G tensor κ ≃ gr_m A and fix its algebra structure.
- `PointChart` specifies the affine graph chart and its restriction map on ideal
  representatives. Its two projection equations fix the chart-to-local-ring map.
  `chart_class` connects the preceding equivalences with G's recorded gluing charts;
  these are not arbitrarily chosen graded equivalences.
- `PointBranches.normalization` is the existing normalized tangent comparison. It
  contains Proj gr_m A ≅ Spec(A^ν/m A^ν), its equation over Spec κ, and its fibre
  isomorphism to `pullback C.fromReducedNormalization (C.fromSpecResidueField x)`.
  Its normalization is the actual integral closure of the reduction in total fractions.
- `Comparison.iso` and `over_centre` give the global D-scheme isomorphism. `pointwise`
  requires that its restriction be the projectivization of `toTangent` followed by
  precisely the normalized tangent comparison and its normalization-fibre isomorphism.
- `PointBranches.geometricSplit` is the actual scalar-extended normalization residue
  algebra Ω × Ω, preserving diagonal Ω scalars. `branches` uses the existing
  `GeometricBranches` predicate, which gives the completed normalization branch square,
  both projections and cardinality two, without an ordering.
- The second conjunct of the theorem quantifies over every isomorphism of k-curves.
  It supplies its induced singular-diagram and normalization isomorphisms, requires
  that they lie over the given curve map, and gives the commuting global comparison
  square using the canonical pullback map. Local naturality is additionally recorded
  by the existing normalized tangent comparison's `IsNatural` predicate.

Recorded dependencies used directly: `GraphConeGluing` (`GraphCone.Construction`,
`singularDiagram`, `Chart`, `Gluing`); `PureDimension` (`Scheme.IsPureDimension`);
`FirstFittingSingularSubscheme` (`Scheme.firstFittingIdealSheaf` and its inclusion);
`NodalLocalTangentData` (`NodalLocal.Comparison`, `Normalization`, `ResidueAlgebra`,
`tangentGrading`, `initialForm`, `stalkScalarMap`, and `GeometricBranches`);
`ProjectiveNodalTower` (`IsGeometricOrdinaryDoublePoint`); `ReducedNormalization`
(`Scheme.reducedNormalization`, `fromReducedNormalization`);
`WeilConjectures.RingTheory.AssociatedGradedRing` (`Ideal.associatedGraded`, its pieces,
ring structure, quotient scalar inclusion); relative Proj's `GradedAlgebraData.relProj`,
`relProjHom`, and `relProjι`. Mathlib supplies Field, LocallyOfFiniteType, Smooth,
AdicCompletion, MvPowerSeries, Algebra.IsSeparable, scheme residue fields, tensor
products, Localization.AtPrime, Proj.map, fibre products and coproduct universal properties.
The proof-only imports retain all recorded proof dependencies with usable modules.
Three proof dependencies currently have no Lean module: geometric-pure-fibre-point-dimension,
separable-point-flat-completion-map, and power-quotient-graded-comparison. They are not
needed to type this statement and are named in its complete nine-step proof docstring.

The added statement dependencies are two already landed nodes:
`def-sfb-nodal-tangent-comparison-data` owns the existing intrinsic comparison data;
`def-trf-projective-nodal-tower` owns the existing geometric completed-node predicate.
No new DAG nodes or dependency repairs are needed. The mathematical statement is unchanged.

Edge cases read against the source: empty C and empty D (vacuous point clauses and empty
coproduct), infinitely many singular points (index is all of D), nonsplit nodes (quadratic
field alternative retained), non-rational finite separable residue fields (no κ = k),
characteristic two (uv model and separability, no division by two), and nonseparated
curves (all graph comparisons are local). The model xy = 0 gives two branches; a nonsplit
real quadratic node gives conjugate branches which split only geometrically.

Searches actually executed with msearch.py:

- LeanFinder: “The graph conormal algebra of a nodal curve at a singular point has
  projectivization equal to its normalization fibre”. Eight hits: Weierstrass nonsingularity
  and generic Proj chart identities; no matching comparison.
- Loogle: “Ideal.associatedGraded, AlgebraicGeometry.Scheme.reducedNormalization”.
  Zero hits; upstream-only `Ideal.associatedGraded` is unknown to the service.
- Mathlib grep: `nodal|[Gg]raph[Cc]one|normalization.*conormal` in AlgebraicGeometry:
  zero hits.
- LeanSearch: “Nodal curve graph conormal algebra normalization fibre canonical graded
  algebra comparison”. Eight relative normalization declarations; none compares graph
  cones and normalization fibres.
- rg over WeilConjectures and Sheaf for the node id, graphCone, BranchNormalization,
  nodal graph and normalization/conormal: the existing graph-cone gluing and local
  tangent-normalization modules are usable dependencies, not this global theorem.
  The recorded GraphConeGluing source was also checked with scompile.py --source.

Source read: `literature/stacks-project/curves.tex`, remark-quadratic-extension,
remark-trivial-quadratic-extension and lemma-split-node, especially the equality
between construction (3) and the scheme-normalization fibre. The exact tensor-local
comparison and arbitrary disjoint open gluing follow the node's nine-step proof.

## Second reading by Q155

Author's second reading (dispatcher forbids starting another agent): re-read the node
and the full Lean file. The correspondence above checks every hypothesis and clause.
In particular the global result must restrict to the same canonical local comparison,
not merely be an unrelated isomorphism; the explicit `PointComparison.intoGraph`/`intoNormalization` restriction equation and `PointChart.chart_class`
supply this. The ordinary-double-point predicate is reused, not replaced by the stronger
connected nodal-fibre predicate. Residue scalars are taken through the actual augmentation,
not a chosen coefficient field. The geometric splitting and completed branch square are
both retained. The naturality clause includes existence of induced diagram maps, rather
than assuming the missing singular or normalization functorial maps as extra input.
No statement correction or disputed clause was found. Compilation and preflight results
are recorded below after validation.

Validation: every compile used scompile.py at the unchanged 60-second limit.
The final module disables generated injectivity and size specification lemmas for its
result structures; they are unused auxiliary derivations. The bundled graph ring retains
the standard localization algebra instance.

The clean scompile.py run passed sandbox mode in 27.2 seconds and library mode in
30.4 seconds. The first complete deliver2.py --no-push run printed OK, with preflight
and compilation passing (temporary dry-run commit ce2cd98edcf). The final documentation
cleanup is checked again by the required final dry run before pushing.
