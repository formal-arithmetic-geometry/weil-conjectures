## Worker report

Q139, stage 2, 2026-10-24. The delivery states
`Real.integrable_fourier_moments_of_weak_derivatives` in
`Sheaf.Analysis.WeakSobolevFourierMoments`. Its sole proof is `sorry`.
No definitions, new DAG nodes, dependency repairs, or statement corrections are needed.
Only the item's `lean` field changes. The accepted Q57 stage-1 split is preserved.
The inherited BLOCKED ending concerned stage-1 duplicate splitting; the current queue gives
this item stage 2, and brief-stage2 section 0 explicitly authorizes this handoff.

Hypothesis and conclusion correspondence:

- The real dimension is `{m : ℕ}` with `hm : 1 ≤ m`, exactly `m ≥ 1`.
  `EuclideanSpace ℝ (Fin m)` has the Euclidean norm, not the supremum norm of a bare function
  space; its `volume` is Lebesgue measure.
- `u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m)))` is a complex square-integrable
  function modulo almost-everywhere equality. Integrals use the canonical measurable
  representative of that class; replacing it almost everywhere leaves the test pairings equal.
- `t r : ℕ` encode the two nonnegative integers. The hypothesis
  `htr : (r : ℝ) + (m : ℝ) / 2 < (t : ℝ)` is precisely the strict threshold.
  The dimension is cast before division, so there is no natural-number truncation.
- `hweak` quantifies over every `α : Fin m → ℕ` with `(∑ i, α i) ≤ t` and supplies an
  existential `v` in the same L2 space. It does not require a chosen family of derivatives
  or any classical differentiability of `u`.
- Every test is an arbitrary `φ : EuclideanSpace ℝ (Fin m) → ℂ` with
  `ContDiff ℝ ∞ φ` and `HasCompactSupport φ`. The integrals are the complex bilinear
  products `v x * φ x` and `u x * (...) x`, with sign `(-1 : ℂ) ^ (∑ i, α i)`.
  There is no conjugation or positivity condition on the tests.
- The inline fold over `List.finRange m` composes, for each coordinate `i`, `α i`
  iterations of `fun g y ↦ fderiv ℝ g y (EuclideanSpace.single i 1)`.
  This is exactly the product of the coordinate derivatives in the node; smoothness of the
  tests ensures that different coordinate orders agree. This uses the existing Fréchet
  derivative definition directly, rather than defining another derivative or Sobolev notion.
- `𝓕 u` is the L2 Fourier transform from `MeasureTheory.Lp.instFourierTransform`, defined by
  `MeasureTheory.Lp.fourierTransformₗᵢ`. Reading LpSpace.lean:47–65 and its Schwartz comparison
  at 100–110 confirms that this is the continuous isometric extension of the usual
  negative-exponent Fourier transform, rather than the pointwise Bochner Fourier transform
  of a function which need not be L1.
- The conclusion quantifies over every `h` with `Measurable h` and
  `h =ᵐ[volume] (𝓕 u : Lp ...)`. Thus it includes every measurable representative and explicitly
  renders representative independence, without choosing one arbitrarily.
- For every `j : ℕ` with `j ≤ r`, the conclusion is
  `Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖h ξ‖) volume`. This is the finite nonnegative integral
  in the node: the integrand is measurable and nonnegative, and `Integrable` says its
  absolute-value integral is finite. The norm on ℂ is the stated absolute value.

Dependency declarations read and used:

- The only statement dependency is the Mathlib leaf `def-weil-field`, whose match is `Field`.
  Its full class signature and docstring were read at Mathlib/Algebra/Field/Defs.lean:170–180.
  The standard ℝ and ℂ fields are used through the public Mathlib imports; no new field
  definition is made.
- Public imports are Mathlib.Analysis.Fourier.LpSpace (`Lp`, its Fourier transform and
  measure/integral interfaces), Mathlib.Analysis.InnerProductSpace.PiL2 (`EuclideanSpace`,
  `EuclideanSpace.single`), Mathlib.Analysis.Calculus.ContDiff.Basic (`ContDiff`, `fderiv`),
  and Mathlib.Data.List.FinRange (`List.finRange`).
- Proof-only imports are Mathlib.Analysis.SpecialFunctions.JapaneseBracket for the matched
  `integrable_rpow_neg_one_add_norm_sq` of `lem-sfb-euclidean-bracket-integrable`, and
  Mathlib.MeasureTheory.Function.L1Space.Integrable for `MeasureTheory.MemLp.integrable_mul`
  of `lem-sfb-l2-product-integrable`. Both matches' full signatures were read.
  The third proof dependency, `lem-sfb-l2-weak-derivative-fourier-identity`, is currently
  unsplit and has no Lean record, so it has no module to import; the proof docstring names
  this exact pending mathematical input. It is a proof prerequisite, not an unstated notion
  required to type the present statement.

Edge cases checked before writing:

- Zero `u` and zero derivatives satisfy the hypothesis and give zero moments.
- For `α = 0`, all iterates are identities, the fold returns `φ`, and the sign is 1;
  this is the required weak identity with `v = u`.
- In dimension 1 the fold is the ordinary repeated real-direction derivative on complex tests.
- `r = 0` retains the unweighted Fourier L1 assertion, and `j = 0` evaluates `‖ξ‖ ^ 0` to 1
  even at `ξ = 0`. All natural `j` up to `r` are included.
- `t = 0` cannot meet the stated strict threshold when `m ≥ 1`; no additional case is removed.
  The strict borderline `t = r + m/2` is correctly excluded.
- Changing `h` on a measurable null set preserves its relation to `𝓕 u` and the weighted
  integrand almost everywhere. The arbitrary-representative conclusion handles this directly.
- Nonzero constant functions on the whole Euclidean space are not L2 and hence are not
  counterexamples. No compact support of `u`, finite measure, or smoothness of `u` is added.

Searches made (all 2026-10-24):

- `msearch.py ... leanfinder "L2 weak partial derivatives imply integrability of polynomial
  Fourier moments Sobolev embedding"`: 8 related results, headed by
  `Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le` and its VectorFourier versions.
  They assume classical differentiability/integrability and do not match the weak hypothesis.
- `msearch.py ... loogle "iteratedFDeriv, ContDiff, HasCompactSupport"`: one result,
  `HasCompactSupport.exists_bound_iteratedFDeriv`; it is a uniform test-function derivative
  bound, not the required Fourier-moment theorem.
- `msearch.py ... grep "weak.*deriv|fourier_memL1|partialDeriv" Analysis`: 6 hits, including
  `TemperedDistribution.MemSobolev.fourier_memL1`. I read Sobolev.lean:212–278. That theorem
  assumes Bessel-potential Sobolev membership and only gives the unweighted conclusion;
  identifying that hypothesis with all the weak derivative identities is a separate theorem.
- `msearch.py ... leansearch "L2 weak derivatives through integer order t imply integrable
  polynomial moments of the Plancherel Fourier transform for t > r + dimension / 2"`:
  8 related hits, including Schwartz Plancherel, Lp inner-product preservation and smooth
  Fourier-derivative formulas. None has the node's hypotheses and conclusion.
- `rg` on Mathlib/Analysis/Calculus and Mathlib/Analysis/Distribution for
  `partialDeriv|partial.*[Dd]eriv|multiindex|multiIndex` found no coordinate multi-index
  weak-derivative definition; the directional Schwartz and distribution derivatives are
  different bundled objects. Directly composing the existing `fderiv` suffices here.
- `rg` on the entire project `lean/WeilConjectures` and `lean/Sheaf` for
  `weak.*[Dd]eriv|[Ww]eak[Pp]artial|multiIndex|multiindex` returned unrelated weakly étale,
  weak Serre and category-theory uses, with no matching analytic notion or statement.
  Exact-id search in WeilConjectures found no attachment. The proposed module and declaration
  names have no existing hit in Mathlib or either project root.

Source reading: I read the current latest blueprint unit and its direct-images proof (3).
The original Demailly PDF remains absent locally, as the source record already says. I opened
https://totomityann.github.io/pdf/lua_agbook.pdf, PDF page 152 (index 151), VI §2 (2.1):
the preceding text defines the derivative-based Sobolev space and gives the strict Sobolev
threshold. The weighted Euclidean Fourier input is explicitly agent-stated, as in the node;
it is not presented as a numbered Demailly assertion or as a proof contained in that excerpt.
No statement fault or disputed statement was found.

Validation: the prescribed scompile.py compiled the module both as a sandbox and under its
library module name, with no errors or warnings. An initial missing `ContDiff` notation scope
was corrected by `open scoped FourierTransform ContDiff`; no mathematical statement changed.

## Second reading by Q139

This is the dispatcher's direct-delivery workflow; no independent worker was started, as the
brief forbids starting agents. The maintainer supplies the independent delivery review.
For this recorded second pass I reopened the node and the complete Lean module and compared
every binder and the entire conclusion, including the folded derivative.

The dimension restriction, real strict threshold, all multi-indices including zero, one L2
weak derivative for each multi-index, all smooth compactly supported complex tests, bilinear
integrals and sign all agree exactly with the node. The derivative fold has no choice of
ordering as a hypothesis: it computes the ordered coordinate product, which agrees with the
node's multi-index derivative on smooth tests. The Fourier transform acts on Lp itself,
not on its representative as a potentially nonintegrable function. Arbitrary measurable
representatives are quantified in the conclusion, and the natural `j` range is exactly
`0 ≤ j ≤ r`. The real `Integrable` assertion is the required finite absolute moment, with
no hidden cancellation. All variables are explicitly bound, and there are no universe
parameters needed for these concrete finite-dimensional spaces.

No mathematical mismatch was found or repaired in this pass. I checked the five proof steps
against the docstring: coordinate weak-derivative Fourier identity; finite-coordinate
weight estimate; inverse bracket at `s = t - j`; L2 product integrability; and almost-everywhere
representative independence. Each is present, including the strict exponent check and the
`j = 0` case. No auxiliary theorem with an unmatched sorry or hollow definition was introduced.
