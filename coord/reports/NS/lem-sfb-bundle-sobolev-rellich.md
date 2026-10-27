## Worker report

Repair of returned immutable head `e8af0cd471ab`, addressing both H4 and H9.
The statement module is `Sheaf.Analysis.BundleSobolevRellich`, declaration
`BundleSobolev.bundle_sobolev_rellich`. Its single postponed theorem has `sorry`
and the original six-step proof plan. The helper module is
`Sheaf.Analysis.MetricBundleSobolevData`. Every definition has actual data.
The item's natural-language statement, source, proof and proof dependencies are
unchanged. Both item and helper now cite `def-sfb-bundle-sobolev-space`.

H4 repair: read the whole landed `Sheaf.Geometry.Manifold.BundleSobolevSpace`
and its DAG node against current main. It supplies the single `BundleSobolev.L2`,
`l2Norm`, `MetricVolume`, `chartGram`, `Localization`, `multiPartial`,
`IsWeakDerivative`, `HasWeakDerivatives`, `MemSobolev`, `H`, and
`localizedCoefficient`. Both delivered modules publicly import that module.
Removed the helper's Chart, Localization, coefficients, multiPartial, indices,
localized, IsL2, l2Setoid, MeasurableL2, HasWeakDerivatives, volumeDensity,
IsMetricVolume, IsOriented and classHasWeakDerivatives declarations. The helper
retains only three pairings, Tests/testPairing/testDensity/IsDistribution, and
HilbertCompletion. Tests use subtypes of actual atlas charts and actual bundle
trivializations, on their open overlap; there is no new localization structure.
The image and choice-independence clauses use the shared weak predicates.

H9 repair: deleted `HilbertCompletion.scalar` and its instance attribute.
`InnerProductSpace` extends `NormedSpace`, so that sole structure supplies the
real module and normed-space instances, including the scalar action in `smooth`.
The consumer probe synthesizes both instances and checks by reflexivity that
their module projections agree.

Source retained from the first delivery: Demailly VI §1 (1.4) on printed p.288
specifies measurable L² sections and the integrated pairing. VI §2, printed
p.289, defines weak Sobolev spaces and states Rellich (2.2). The PDF and extracted
pp.288–290 are in the sandbox. This is a nested prerequisite of the current
blueprint direct-images proof (3), not that unit's own statement. The maintainer
accepted the earlier clause reading; this repair changes the common interfaces,
not the mathematics. No statement correction or dispute is needed.

Hypothesis and clause correspondence:

- Scalars: all inner products, integrals, coordinate derivatives and linear maps
  are over `ℝ`, using the instance of Mathlib `Field` (`def-weil-field`).
- Compact oriented smooth m-manifold without boundary: `m : ℕ`, `hm : 1 ≤ m`,
  `N : Type u`, `TopologicalSpace`, `T2Space`, `SecondCountableTopology`,
  `CompactSpace`, `ChartedSpace (EuclideanSpace ℝ (Fin m))` and
  `IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N`. The identity model has no
  boundary. The inline `h_oriented` states that a smooth maximal-atlas subset
  covers N and has strictly positive coordinate-transition determinants. Its
  previous helper abbreviation was removed rather than redefining orientation.
- Smooth base metric and its positive volume: `g : ContMDiffRiemannianMetric`
  on `TangentSpace`, `MeasurableSpace N`, `BorelSpace N`, and
  `V : BundleSobolev.MetricVolume g`. Use `V.measure` everywhere. Its shared
  `chart_density` fixes volume by the square root of `chartGram`'s determinant;
  this is not an arbitrary measure or an assumed realization property.
- Smooth finite-rank real bundle with smooth positive definite fibre metric:
  `B : N → Type v`, arbitrary `r : ℕ`, Euclidean rank-r fibre model,
  `FiberBundle`, `VectorBundle ℝ`, `ContMDiffVectorBundle ∞`, pointwise
  `NormedAddCommGroup`, `InnerProductSpace ℝ`, and
  `IsContMDiffRiemannianBundle ∞`. No global triviality or equality m = r.
- Smooth sections: precisely Mathlib `ContMDiffSection ... ∞ B`, with its
  existing pointwise additive and real module structures.
- L² completion and integrated norm: existential `L : HilbertCompletion` of
  `fun u v ↦ l2Pairing V.measure u v`; the pairing is the actual fibre integral.
  HilbertCompletion gives a complete real inner product space, dense linear
  `smooth` map and `inner_smooth`. `Function.Injective L.smooth` is a conclusion.
  These characterize the completion up to its unique isometric linear map
  fixing smooth sections; no analytic conclusions are input hypotheses.
- Order: `s : ℕ`, `hs : 1 ≤ s`.
- Finite charts, frames and subordinate compact partition: `∀ P :` the shared
  `Localization (m := m) (q := r) B`. Its `size`, `chart`, `chart_smooth`,
  `frame`, `frame_smooth`, `chart_in_frame`, `covers`, `positive_transition`,
  `partition` and `subordinate` supply the finite oriented trivializing cover.
  `SmoothPartitionOfUnity.IsSubordinate` puts each closed support inside the
  chart; compactness of N makes that support compact. This reuses the landed
  structure without adding a compactness axiom to it.
- Sobolev norm: `sobolevPairing P s u u` sums over `i : Fin P.size`, scalar
  component `k : Fin r`, and `α : Fin m → Fin (s+1)` with `∑ a, α a ≤ s`.
  For each coefficient the formula is the same partition-times-frame formula
  as shared `localizedCoefficient`, applied to an actual smooth section rather
  than an a.e. representative. Outside the chart target it is zero. It uses
  the shared scalar `multiPartial`. The componentwise sum of products is the
  Euclidean inner product, so its square root is precisely the stated norm.
- H^s completion, Hilbert structure and smooth density: existential
  `H : HilbertCompletion` of this exact pairing; `Function.Injective H.smooth`.
  Its `dense`, `inner_smooth`, `hilbert` and `complete` fields give these clauses.
- Canonical measurable realization: `e : L.Space ≃ BundleSobolev.L2 B V.measure`.
  The target is the landed dependent almost-everywhere quotient, restricted to
  classes having an a.e. measurable representative and finite squared integral.
  `(e (L.smooth u)).val = ((u : ∀ x, B x) : Filter.Product (ae V.measure) B)`
  pins the realization on every smooth section. `inner ℝ u v = classPairing ...`
  gives the integrated inner product, while `‖u‖ = l2Norm B V.measure (e u)`
  explicitly pins the norm to the shared numerical norm. Representative choices
  here are only representatives of existing a.e. classes, not analytic data
  chosen from an undetermined existence theorem.
- Identity extension: `j : H.Space →L[ℝ] L.Space`, with
  `∀ u, j (H.smooth u) = L.smooth u` and `Function.Injective j`.
  The continuous linear map is bounded; smooth density determines the extension.
- Exact image: `(∃ v : H.Space, j v = u) ↔ MemSobolev B V.measure s (e u)`.
  This is the shared predicate defining `BundleSobolev.H`, so the completion
  realizes the very same H^s subset as the embedding theorem.
- Localized weak characterization and independence: for every shared `Q`, the
  theorem supplies positive `c,C` with both smooth norm inequalities, and for
  every shared L² class `u` gives
  `MemSobolev ... s u ↔ ∀ i k, HasWeakDerivatives s ⊤ (localizedCoefficient ... u i k)`.
  Thus all atlas/frame/partition choices have this same image. The shared
  `HasWeakDerivatives` calls `IsWeakDerivative`, whose test identity has exactly
  `(-1 : ℝ) ^ (∑ i, α i)`. It includes α = 0. Its local square-integrability on
  all of R^m gives global square-integrability here: these localized functions
  have fixed compact support, and their distributional derivatives have support
  there too. This recovers precisely the item's localized L²-derivative clause.
- Local distributions: `Tests c e` is Mathlib `TestFunction` on
  `c.target ∩ c.symm ⁻¹' e.baseSet`, valued in `EuclideanSpace ℝ (Fin r)`, at ⊤,
  with its existing LF topology. The chart and frame are actual atlas subtypes.
  `testPairing` integrates coefficients of the shared L² representative against
  each test. `testDensity` uses `chartGram` for the inverse metric density,
  extending by zero outside the chart/frame intersection. `IsDistribution`
  requires a continuous real-linear local functional and all finite relations
  between intrinsic densities. This is the usual Jacobian/change-of-frame rule.
  Every shared L² class gives such a distribution and
  `Function.Injective (fun u ↦ testPairing ... u)` states test separation.
  The same shared image therefore also means the same distributional subspace.
- Rellich: `IsCompactOperator j`, plus explicitly every sequence with any real
  norm bound has a strictly increasing subsequence whose images tend to some
  `v : L.Space` in the norm topology. No unit-bound or nonempty-case restriction.

Dependency declarations read and used:

- `Sheaf.Geometry.Manifold.BundleSobolevSpace`: the complete signatures and
  docstrings of Model, MetricVolume/chartGram, Localization, L2/l2Norm,
  multiPartial, IsWeakDerivative/HasWeakDerivatives, MemSobolev/H and
  localizedCoefficient were read. This is the new direct dependency of both nodes.
- `Mathlib.Algebra.Field.Defs`: Field.
- `Mathlib.Geometry.Manifold.IsManifold.Basic`: IsManifold/maximalAtlas;
  `Mathlib.Geometry.Manifold.ChartedSpace`: ChartedSpace.
- `Mathlib.Geometry.Manifold.VectorBundle.Basic`: ContMDiffVectorBundle,
  with the imported FiberBundle/VectorBundle/trivializationAtlas API.
- `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`: ContMDiffSection.
- `Mathlib.Geometry.Manifold.VectorBundle.Riemannian`:
  ContMDiffRiemannianMetric and IsContMDiffRiemannianBundle.
- `Mathlib.Geometry.Manifold.PartitionOfUnity`: SmoothPartitionOfUnity and
  IsSubordinate, through the shared Localization.
- `Mathlib.Analysis.Distribution.TestFunction`: TestFunction and its LF topology.
- `Mathlib.Analysis.InnerProductSpace.Defs`: InnerProductSpace, whose full
  extends clause was reread to verify the single inherited NormedSpace structure.
- `Sheaf.Analysis.EuclideanFixedSupportRellich`:
  MeasureTheory.euclidean_fixed_support_rellich, the proof-only import.
  The graph-mollification and chart-overlap proof nodes still have no published
  Lean record; no proof import for an absent statement was invented.

Edge cases reread: empty N, size-zero localization on empty N, rank r = 0,
zero section/sequence, arbitrary real bound, m = s = 1, and α = 0. No Nonempty,
connectedness, positive total volume or r ≥ 1 assumption appears. Shared finite
component sums are zero in rank zero. Universes u and v remain independent;
completion spaces have the same max universe as their smooth sections and the
shared L² classes. `autoImplicit` is false. There are no local instances or
private notation, and definitions contain no sorry.

Searches retained from the first pass: msearch LeanFinder for “Sobolev norm
completion smooth sections compact manifold Rellich compact embedding into L2”,
Loogle “Sobolev”, grep “Sobolev|Rellich|volumeForm|riemannianMeasure” in Geometry,
and LeanSearch for measurable square-integrable bundle sections. They found
Euclidean weak Sobolev spaces, supported-function seminorms and smooth bundle
sections, but no exact realization/Rellich theorem.
Repair searches: msearch LeanFinder “Hilbert completion of smooth vector bundle
sections with integrated pairings and compatible local coefficient distribution
tests” gives smooth metric pairings, not this completion/test-family interface;
Loogle `"HilbertCompletion", "testPairing", "BundleSobolev"` and Mathlib grep
`HilbertCompletion|testPairing|testDensity|IsDistribution|classPairing` give zero
hits. LeanSearch “Hilbert completion of a real pairing and distributions of vector
bundle sections via local coefficient tests” gives HilbertSpace, ordinary uniform
completion and local-frame coefficients. Neither is the dense map paired to the
specified smooth-section integral with the compatible local test-family data.
Project rg in both Lean roots for the retained helper names found no declarations;
DAG rg found the closed-range consumer, not another definition of this interface.
`blueprint_refs.py search 'metric bundle Sobolev'` gives zero blueprint-unit hits.
The actual parallel-landed shared Sobolev node was found, read, and reused.
Raw repair msearch results are in the helper's mathlib_searches.

Both modules and a module-mode consumer importing both this Rellich theorem and
`Sheaf.Geometry.Manifold.BundleSobolevEmbedding` passed scompile.py with no errors
or warnings. The consumer checks the shared L2/H/Localization/MetricVolume and
weak-derivative declarations, the two theorem signatures, and the inherited scalar
instance coherence. The consumer is a sandbox probe, not a delivered module.

## New nodes

`def-sfb-metric-bundle-sobolev-data` is narrowed to integrated and scalar-component
Sobolev pairings, local coefficient testing with intrinsic-density compatibility,
and dense-isometric Hilbert completion data. It now cites and imports
`def-sfb-bundle-sobolev-space` for every underlying Sobolev notion. Its statement
and declaration list were rewritten to match the repaired helper; all duplicate
notions were removed. Demailly VI §1–2 is the source; the searches above and their
raw records distinguish the remaining interface from the shared Sobolev-space
node. Its source, chapter, item ancestry, empty proof fields and import_flags are
retained. This helper was new in the returned packet and is not on current main.

## Dependency modules

No extra dependency modules. The four retained dependency records bind existing
Mathlib declarations under §1(B), with notes, changing only lean fields against
current main: def-sfb-smooth-real-manifold to IsManifold, def-sfb-smooth-real-vector-bundle
to ContMDiffVectorBundle, def-sfb-smooth-bundle-sections to ContMDiffSection, and
def-sfb-local-coefficient-tests to TestFunction. Their full specializations are
listed in the clause reading above. These are exact existing bindings, not copies.
The new shared Sobolev dependency uses NO's landed record unchanged.

## Second reading by NS

Worker's explicit second pass for this repair; no other agent was started, as
instructed. The maintainer performs the independent delivery review. Reopened
both delivered files, both owned node records, and the landed Sobolev and embedding
modules. Matched each clause as above, checked support compactness follows from
CompactSpace and subordination, and checked scalar-coordinate sums equal the old
Euclidean vector pairing. Confirmed no duplicate Localization, multiPartial or
HasWeakDerivatives survives. The realization and embedding now literally use the
same dependent a.e. quotient and MemSobolev/H predicate. The forall-Q clause gives
both norm equivalence and equality with every localized weak condition. The
orientation assumption is unchanged inline, the volume is the shared MetricVolume,
and the testing domains include all smooth chart/frame overlaps. Removed the
extra scalar field; consumer compilation verified the inherited module agrees
with that used by the linear smooth map. Empty and rank-zero cases still apply,
and the six-step proof with sole sorry is retained.
