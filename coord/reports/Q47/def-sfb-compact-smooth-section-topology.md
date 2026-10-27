## Worker report

The module `Sheaf.Geometry.Manifold.CompactSmoothSectionTopology` constructs the topology and
compactly supported subspace in the node, with real data throughout and no theorems or sorries.
The item node changes only in `lean`. All seven owning declarations are in `lean.declarations`.
The chart/frame indices, coordinate functions and derivatives are helpers belonging to this
very definition, not separate independent notions needing new DAG nodes.

Clause-by-clause correspondence:

- A nonnegative dimension and rank are `m q : ℕ`. The base is `N : Type u` with
  `TopologicalSpace N`, `ChartedSpace (EuclideanSpace ℝ (Fin m)) N` and, on the topology,
  `IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m))) ∞ N`.
  The self model is the boundary-free real Euclidean model. `CompactSpace N`, `T2Space N`
  and `SecondCountableTopology N` are exactly the three additional base hypotheses.
- The bundle is `B : N → Type v`, with its fibre real vector spaces, topologies, total-space
  topology, `FiberBundle`, `VectorBundle ℝ` and `ContMDiffVectorBundle ∞`, modelled on
  `EuclideanSpace ℝ (Fin q)`. These are the dependency's Mathlib notions, with independent
  base and fibre universes. No norm on an individual fibre is required.
- Smooth sections are the dependency's `ContMDiffSection` with this base model, fibre model,
  bundle and differentiability parameter `∞`; addition in translates is its pointwise addition.
- `CompactSmoothSectionTest.chart` is an `OpenPartialHomeomorph`, so its source `U` and target
  `V` are open and it is a homeomorphism between them. `smooth_chart` and `smooth_inverse`
  require smoothness on those open sets. This indexes ALL compatible smooth charts, including
  restrictions, rather than only `chartAt` or members of a chosen atlas.
- `frame : Fin q → (x : N) → B x` and `isFrame : IsLocalFrameOn ... ∞ frame chart.source`
  supply exactly a smooth fibrewise basis over `U`. Values outside `U` are junk values;
  every local frame can be extended there by zero and no global smoothness is requested.
- `compactSet`, `isCompact`, `subset_target` and `order` supply compact `K ⊆ V` and `k ≥ 0`.
- `CompactSmoothSectionTest.coefficients` pulls the section back by `chart.symm` and uses
  `isFrame.coeff` for each component. `IsLocalFrameOn.coeff_sum_eq` gives precisely
  `s(x⁻¹(z)) = ∑ j, coefficient_j(z) • frame_j(x⁻¹(z))` on `V`.
  `WithLp.toLp 2` packages these coefficients in the Euclidean, not sup, norm.
- A multi-index is explicitly `α : Fin m → ℕ`, its order `∑ j, α j`. The list
  `(List.finRange m).flatMap (fun j => List.replicate (α j) j)` contains each coordinate
  with exactly this multiplicity. `sectionCoordinateDerivative` recursively applies `fderiv ℝ`
  to the standard Euclidean coordinate vector. Its empty-list branch is the original function.
  Smoothness implies the usual equivalence with repeated partial differentiation; the total
  extension off `V` is irrelevant to derivatives on its open domain.
- `seminormValue` is the supremum in `ℝ≥0` of all these derivative norms for `|α| ≤ k` and
  `z ∈ K`, coerced to `ℝ`. This is exactly the maximum of the finitely many compact suprema:
  there are finitely many such multi-indices, each smooth derivative is continuous and bounded
  on compact `K`, and the nonnegative supremum of their union equals their finite maximum.
  No claim of a bundled `Seminorm` instance or its proofs is needed to construct these values.
- `compactSmoothSectionTopology` uses `TopologicalSpace.generateFrom` on sets explicitly
  written as the image by `fun t => s₀ + t` of the finite intersection
  `{t | ∀ i : Fin n, (a i).seminormValue B t < ε i}`, with `∀ i, 0 < ε i`.
  `Fin n` ranges over every finite family, with independent indices and radii in each family.
  `generateFrom` is exactly the smallest topology in which all these sets are open.
- `CompactlySupportedSmoothSection` is the subtype with
  `IsCompact (closure {x : N | s x ≠ 0})`, using exactly the support formula of the node.
  `compactlySupportedSmoothSectionTopology` is `TopologicalSpace.induced Subtype.val` from the
  constructed ambient topology. No alternative ambient topology is inferred implicitly.

Dependency declarations read and used:

- `def-sfb-smooth-real-manifold`: `ChartedSpace` in `Mathlib.Geometry.Manifold.ChartedSpace`
  (atlas, chosen charts, covering condition), and `IsManifold` in
  `Mathlib.Geometry.Manifold.IsManifold.Basic` (smooth groupoid with the self model).
- `def-sfb-smooth-real-vector-bundle`: `ContMDiffVectorBundle` in
  `Mathlib.Geometry.Manifold.VectorBundle.Basic` (smooth coordinate-change operators), with
  `FiberBundle` and `VectorBundle` as its prescribed underlying structures.
- `def-sfb-smooth-bundle-sections`: `ContMDiffSection`, `instAddCommGroup`, `instModule` in
  `Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection`. Read the full structure and the
  pointwise operations. All three nodes are Mathlib matches and need no `lean` repair.
- The `LocalFrame` import publicly imports the above bundle and section APIs. Its
  `IsLocalFrameOn`, `coeff`, `toBasisAt` and `coeff_sum_eq` implement the node's stated frames
  and coefficients, without a private copy. `PiL2` supplies the Euclidean fibre and basis;
  `Topology.Order` supplies the generated and induced topology constructions.

Edge cases checked before writing, then checked against the constructed definitions:

- `K = ∅`: the nonnegative set of derivative norms is empty, whose `sSup` is zero.
- `q = 0`: `EuclideanSpace ℝ (Fin 0)` has only the zero vector, hence all norms are zero;
  the empty frame is a basis of each rank-zero fibre.
- `m = 0`: there is one function `Fin 0 → ℕ`, its sum is zero, and the coordinate list is
  empty, so the derivative is exactly the original coefficient function, for every `k`.
- `k = 0`: only the zero multi-index contributes, again with the original coefficient function.
- `N = ∅`: the smooth section type is a singleton, compact coordinate sets are empty, and the
  construction gives its unique topology and compact support.
- `n = 0`: the intersection is the full section space, its translate is full as required.
- Empty chart sources/targets are allowed, yield only empty compact tests, and impose no
  constraint. Disconnected bases are allowed. Compact support is automatic on compact `N`,
  but the required subtype and its induced topology are still constructed explicitly.

Searches actually performed with the prescribed `msearch.py` wrapper:

1. `leanfinder`: "Topology of smooth sections of a vector bundle defined by suprema of
   coordinate derivatives on compact subsets in smooth charts and frames". Eight hits:
   smooth bundle instances, smooth sections, their coercions and smooth sheaf sections;
   no section topology.
2. `loogle`: "ContMDiffSection, TopologicalSpace". Twelve hits: the section structure,
   constructors, coercions and pointwise algebra; no topology on that type.
3. `leansearch`: "smooth bundle section topology on compact manifold coordinate derivatives
   seminorms". Eight hits: `ContDiffMapSupportedIn.seminorm`, `ContMDiffSection` and local
   smoothness criteria. The first concerns maps on one normed space with one fixed compact
   support; it is not this bundle section topology.
4. `grep`: `ContMDiffSection.*[Tt]opolog|[Tt]opolog.*ContMDiffSection|section.*[Ss]eminorm`.
   Twenty-five reported hits were unrelated sections titled Seminormed, generic seminorms
   or Schwartz function seminorms. Direct `rg` with the same pattern on both project source
   roots returned no match. A direct node-id search in `lean/WeilConjectures` returned no
   match. Searches for the chosen declaration names in both project roots, Mathlib Geometry
   and Calculus, and `dag/lean_names_upstream.json` returned no match.

The source attribution is preserved honestly: the node explicitly describes an agent-stated
convention with an unavailable Demailly PDF, and the PDF is absent locally. No claim is made to
have checked its inherited page numbers. The accepted stage-1 mathematical statement is retained
verbatim. No statement dispute or dependency fault was found.

Validation: `scompile.py` compiled both the sandbox and named library module cleanly. The first
pass identified the missing `NNReal` notation scope and the reducibility annotations expected
on topology-valued definitions; these were repaired. Final dry-run and delivery results follow
from the prescribed delivery wrapper.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
