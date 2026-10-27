## Worker report

The delivery states `BundleSobolev.sobolev_chart_overlap_bound` and supplies concrete
notation for its transformation and chain-rule coefficients. Its only postponed theorem
is this named theorem, with the seven-step DAG proof in its docstring. All definitions
have real data. No statement correction or statement dispute is needed.

Hypothesis and clause correspondence:

- Real scalars: `ℝ`, with Mathlib's `Field ℝ`; the recorded `def-weil-field` match is
  `Field` in `Mathlib.Algebra.Field.Defs`, whose signature and docstring were read.
- Smooth Hausdorff boundaryless m-manifold, m≥1: arbitrary `M : Type u`,
  `[T2Space M]`, `[ChartedSpace (Model m) M]`,
  `[IsManifold 𝓘(ℝ, Model m) ∞ M]`, and `hm : 1 ≤ m`. The self model excludes
  boundary and corners. No compactness, orientation or second countability is assumed.
- Smooth real rank-r bundle: arbitrary `E : M → Type v`, fibre vector-space and
  topology instances, `FiberBundle`, `VectorBundle` and `ContMDiffVectorBundle` with
  fibre `Model r = EuclideanSpace ℝ (Fin r)`. `r : ℕ` includes rank zero.
- Two smooth coordinate charts: `cU cV : OpenPartialHomeomorph M (Model m)` and
  `hcU`, `hcV` membership in the maximal smooth atlas. Sources are U,V; targets O_U,O_V.
- Smooth frames on the chart domains: trivializations `eU eV`, linearity instances,
  smooth trivialization-atlas membership `heU heV`, and `hU hV` saying the chart
  sources lie in the frame domains. This is the same frame encoding as the existing
  bundle Sobolev definitions. Atlas frames give smooth coordinate maps and inverses
  by `Bundle.Trivialization.contMDiffOn` and `contMDiffOn_symm`.
- Compact K⊆U: `K : Set M`, `hK : IsCompact K`, `hKU : K ⊆ cU.source`.
- Smooth scalar η with compact support in V: `hη : ContMDiff ... ∞ η`,
  `hηc : HasCompactSupport η`, `hηV : tsupport η ⊆ cV.source`.
- Integer s≥0: `s : ℕ`.
- Inputs in L² and W^{s,2}: `EuclideanMem s f` includes `MemLp f 2 volume` and
  the L² weak derivatives of every component and every multi-index |α|≤s. This
  quantifies over all a.e. measurable L² representatives, equivalent to quantifying
  over their a.e. classes. No particular measurable representative is assumed.
- Vanishing a.e. outside κ_U(K): `∀ᵐ x ∂volume, x ∉ cU '' K → f x = 0`.
- v_f is implicit in the exact formula: `overlapTransform` uses the U-to-V matrix
  `eU.coordChangeL ℝ eV` at `cV.symm y` on `(cV.symm ≫ₕ cU).source`, and is zero
  elsewhere. Thus it is exactly η times the U-frame section (zero outside U),
  expressed in V coordinates and zero outside O_V. `overlapMultiplier` includes η.
- One fixed C>0 for all inputs: `∃ C : ℝ, 0 < C ∧ ∀ f ...`. C precedes f and
  depends only on the bound fixed data.
- Sobolev preservation and bound: `EuclideanMem s (overlapTransform ... f)` and
  `euclideanNorm s (overlapTransform ... f) ≤ C * euclideanNorm s f`.
  `euclideanNorm` is the square root of the finite sum over all |α|≤s and all
  Euclidean components of the L² weak-derivative squared integrals. Every multi-index
  appears once, without multinomial coefficients, including α=0 and s=0.
- Weak Leibniz and chain rules: `IsWeakDerivative ⊤ α ... (overlapWeakDerivative ...)`
  for every |α|≤s and component. The helper is an explicit finite sum of input weak
  derivatives composed with F, multiplied by `overlapChainCoefficient`. Its recursion
  starts at A for β=0, differentiates each coefficient, and adds C_{β-e_j}∂_i F_j.
  It follows exactly the node's recursion; the word order agrees with `multiPartial`.
  The expression is zero off the overlap. A is smooth on that overlap, which is the
  only domain sampled by the formula. No auxiliary support hypothesis was added.
- A.e. representative independence: the fourth conjunct states f=ᵐg implies Tf=ᵐTg.
  It makes the displayed pointwise formula a well-defined map on L² classes.
- Distributional-section agreement: the last conjunct pairs Tf against every smooth
  compactly supported vector test ψ. The right side integrates over
  `(cU.symm ≫ₕ cV).source`, with f, transposed frame action (the k,l sum), cutoff,
  ψ composed with the inverse transition, and
  `|LinearMap.det (fderiv ℝ (fun z ↦ cV (cU.symm z)) x).toLinearMap|`.
  This is exactly duality with the absolute inverse Jacobian, without an orientation
  assumption. The preceding weak-derivative identity also handles differentiated tests.
  This equality states agreement for the associated distributions directly through
  their values on all tests; no arbitrary distribution map is supplied as a premise.

Dependency declarations used:

- `Sheaf.Geometry.Manifold.BundleSobolevSpace`: `BundleSobolev.Model`, `multiPartial`,
  `IsWeakDerivative`, `weakDerivative`. The source, full signatures and docstrings were
  read; scalar tests are `TestFunction ⊤ ℝ ⊤`, with the exact (-1)^|α| identity.
- New `Sheaf.Analysis.EuclideanWeakSobolev`: `BundleSobolev.EuclideanMem`, `euclideanNorm`.
- Mathlib: `ChartedSpace`, `IsManifold`, `ContMDiffVectorBundle`,
  `Bundle.Trivialization`, `Bundle.Trivialization.coordChangeL`, `MemLp`, Lebesgue
  `volume`, `ContDiff`, `ContMDiff`, `HasCompactSupport`, and Fréchet derivatives.
- Proof imports cover the recorded Mathlib matches: `ContDiffBump` (InnerProduct),
  real smooth differentiation (ContDiff.Comp), the two Jacobian nonnegative/integrability
  statements and integral formula (MeasureTheory.Function.Jacobian), continuous compact
  support integrability (already publicly imported by BundleSobolevSpace), and
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (LineDeriv.IntegrationByParts).
  The proof dependency `lem-sfb-euclidean-sobolev-graph-mollification` currently has no
  Lean or Mathlib record, so no import exists to add. It is used only by the proof plan;
  its statement is not needed to type the present theorem. No duplicate was introduced.

Edge cases checked before writing: rank r=0 gives empty component sums and the zero
map; empty K forces f=0 a.e.; empty overlap, η=0, and an empty manifold give zero
output; s=0 includes exactly the zero multi-index and gives the L² norm; m=1 is
included; reversed coordinate orientation is handled by absolute determinant. Noncompact
and non-second-countable manifolds are included because all bounds concern fixed compact
local supports. Arbitrary null-set modifications of f are explicitly covered. Independent
universes u,v are explicit and `set_option autoImplicit false` is enabled in both modules.

Searches made: msearch LeanFinder for smooth coordinate/frame changes bounded on integer
weak Sobolev norms returned supported smooth sup-seminorms, not this statement; Loogle
`ContMDiff, TestFunction, MemSobolev` had no hit (unknown unqualified MemSobolev);
msearch LeanSearch for weak localization returned smooth coordinate-change APIs. Direct
Mathlib grep `weakDerivative|IsWeakDerivative|MemSobolev` found only the Fourier/Bessel
potential Sobolev definition in `Analysis/Distribution/Sobolev.lean`, whose signature was
read and whose norm is not this exact unweighted integer norm. Additional LeanSearch and
LeanFinder queries for the Euclidean integer weak definition returned classical Sobolev
inequalities. Direct rg in lean/WeilConjectures found no overlap-bound declaration (nor
the item tag); rg in lean/Sheaf found BundleSobolevSpace and Fourier prerequisites.
DAG searches and `tools/blueprint_refs.py search 'weak Sobolev'` found no separate Euclidean
integer definition. Existing BundleSobolev scalar weak derivatives are reused.

Source checked online: Demailly, Differential and pseudodifferential operators on manifolds,
§2 pp.3–4: integer-order description after (2.1), localization (2.2), (2.2 prime),
independence of covering/partition/trivialization, and Lemma 2.3.
https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf

Validation: both delivered modules compiled individually, in dependency order, through
scompile.py against the live published library, clean of errors and unexpected warnings.

## New nodes

`def-sfb-euclidean-weak-sobolev` defines global Euclidean integer W^{s,2} membership and
its exact derivative-sum norm. Source: Demailly supplemental §2 p.3 after (2.1), and
VI §2 weak-derivative setup. It reuses `def-sfb-bundle-sobolev-space` scalar weak derivatives
rather than defining a second scalar weak-derivative notion. The bundle norm requires a
finite oriented chart cover, metric and partition, so it is not the Euclidean norm needed
here. Mathlib's Fourier/Bessel-potential membership has a different interface and norm.
The new definition's LeanSearch, LeanFinder and Mathlib grep results are copied verbatim
from real msearch records; direct DAG/upstream/Sheaf and blueprint searches found no
existing definition of these two global Euclidean notions. There are no postponed proofs
or existence-based arbitrary data choices in the new module.

## Second reading by Q03

The dispatcher requires this worker to work alone and assigns the independent review to
the maintainer. This section records a final worker consistency pass, not a fabricated
independent worker reading. Reopened the node and both source files: all fixed hypotheses
are explicit, C precedes f, the support is an a.e. condition, all multi-indices occur once,
and both final clauses are present as explicit formulas. The initial compiler issues
(matrix elaboration and classical set-membership decisions) were repaired without changing
these mathematical clauses. No remaining mismatch or statement dispute was found.
