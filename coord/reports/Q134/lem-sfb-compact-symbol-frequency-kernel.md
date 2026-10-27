## Worker report

The module `Sheaf.Analysis.CompactSymbolFrequencyKernel` states
`Analysis.compactSymbol_frequencyKernel`, with its only theorem proof `sorry`.
Three concrete helpers belong to this node: `compactSymbolPartial` evaluates mixed
coordinate derivatives, `compactSymbolOperator` is the displayed Fourier integral,
and `compactSymbolCutoffOperator` is the actual regularized product integral.
These introduce no arbitrary maps, choices, axioms, or postponed data. Each has a
source/blueprint docstring. The theorem docstring reproduces all six proof steps,
including their prerequisite node ids. No node statement or dependency changes.

Hypotheses, matched individually:

- R and C are Mathlib `ℝ` and `ℂ`; their existing field instances implement
  `def-weil-field` (`Field`, Mathlib.Algebra.Field.Defs, full class signature and
  docstring read). No replacement field notion is introduced.
- Dimensions are `{m p q : ℕ}` and `hm : 1 ≤ m`. Thus p and q may be zero.
  Symbol order is the unrestricted integer `r : ℤ`.
- Spatial and frequency spaces are `EuclideanSpace ℝ (Fin m)`; the input and
  output are `EuclideanSpace ℂ (Fin p)` and `EuclideanSpace ℂ (Fin q)`.
  Matrices are `→L[ℂ]`, with the operator norm, not the norm on coordinate arrays.
  Every linear map between these finite-dimensional spaces is continuous.
- `b` is the stated curried matrix function; `hb : ContDiff ℝ ∞
  (Function.uncurry b)` asserts joint real smoothness.
- `K` and `hK : IsCompact K` give the single common compact set;
  `hsupp : ∀ x, x ∉ K → ∀ ζ, b x ζ = 0` is uniform in frequency.
- `hest` quantifies over both derivative orders and every coordinate word
  `i : Fin a → Fin m`, `j : Fin d → Fin m`. The concrete helper takes the
  d-th frequency derivative in the j coordinate directions, then the a-th
  spatial derivative in the i directions. For a jointly smooth function these
  are precisely the mixed partials for the associated multi-indices. All words
  representing a fixed multi-index give the same derivative by symmetry;
  conversely each multi-index has such a word. Thus this encoding adds no
  derivative condition. Constants are finite real numbers, existential after
  the coordinate words and before x and ζ. The exponent is integer `r - (d : ℤ)`.

Conclusions, matched individually:

- The partial Fourier transform is the existing `𝓕 (fun x ↦ b x ζ) θ`.
  `Real.fourier_eq'` gives exactly its negative `2πi` phase. The first conjunct
  quantifies `L : ℕ`, then `C : ℝ`, then θ and ζ, with weight
  `(1 + ‖θ‖) ^ (-(L : ℤ)) * (1 + ‖ζ‖) ^ r`. Constants are uniform in both variables.
- Inputs are arbitrary `SchwartzMap` into the p-dimensional complex Euclidean
  space. Its actual Mathlib definition is smoothness plus all weighted
  iterated-derivative bounds; it is not replaced by an integrability hypothesis.
- `compactSymbolOperator` is the integral with positive `2πi` phase,
  `b x ((2 * Real.pi) • ξ)` and the existing Schwartz Fourier transform `𝓕 f ξ`.
  The first input-dependent conjunct is `Integrable` of exactly this integrand
  for every x, expressing absolute convergence of the Bochner integral.
- `ContDiff ℝ ∞ (compactSymbolOperator b f)` is smoothness of the actual integral.
  `tsupport (compactSymbolOperator b f) ⊆ K` is its closed support containment.
- For each η, the next conjunct is precisely the Fourier-kernel formula:
  `𝓕 (compactSymbolOperator b f) η` equals the integral of
  `(𝓕 (fun x ↦ b x ((2 * Real.pi) • ξ)) (η - ξ)) (𝓕 f ξ)`.
- The last conjunct quantifies every complex smooth compactly supported χ
  equal to one in a neighbourhood of zero (`∀ᶠ ζ in 𝓝 0, χ ζ = 1`). For every
  smooth compactly supported complex test φ, the vector-valued pairing
  `∫ x, φ x • compactSymbolCutoffOperator b f χ R x` converges along real
  `R → +∞` to `∫ x, φ x • compactSymbolOperator b f x`.
  The cutoff helper is the product integral in `(y, ζ)` of
  `exp (i inner (x-y) ζ) * χ (R⁻¹ • ζ)` acting on `b x ζ (f y)`, multiplied by
  the real scalar `((2 * Real.pi) ^ m)⁻¹`. This is the original regularized
  double integral, not merely a cutoff of the conclusion's Fourier formula.
  The vector-valued pairing with every scalar test is equivalent to all
  componentwise dual tests, since q is finite. No conjugation is needed for
  the complex-linear distribution pairing. `atTop` eventually has R positive;
  the definition remains total at zero by Mathlib's inverse convention.

Dependency declarations used and source signatures read:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- The Fourier convention and integrals: `Real.instFourierTransform`,
  `Real.fourier_eq`, `Real.fourier_eq'`, Mathlib.Analysis.Fourier.FourierTransform.
- Schwartz input and its Fourier transform: `SchwartzMap` and
  `HasCompactSupport.toSchwartzMap`, `SchwartzMap.integrable`,
  Mathlib.Analysis.Distribution.SchwartzSpace.Basic;
  `SchwartzMap.fourierTransformCLM`, `SchwartzMap.instFourierTransform`,
  `SchwartzMap.instFourierTransformInv`, `SchwartzMap.instFourierPair`,
  `SchwartzMap.instFourierInvPair`, `SchwartzMap.lineDerivOp_fourier_eq`,
  `SchwartzMap.fourier_lineDerivOp_eq`, `SchwartzMap.integral_norm_sq_fourier`,
  Mathlib.Analysis.Distribution.SchwartzSpace.Fourier.
- Proof dependencies have Mathlib matches: `hasFDerivAt_integral_of_dominated_of_fderiv_le`
  (Mathlib.Analysis.Calculus.ParametricIntegral), `integrable_rpow_neg_one_add_norm_sq`
  (Mathlib.Analysis.SpecialFunctions.JapaneseBracket),
  `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`
  (Mathlib.MeasureTheory.Function.Jacobian), `MeasureTheory.Integrable.mono'`
  and `MeasureTheory.norm_integral_le_of_norm_le` (L1Space.Integrable and
  Integral.Bochner.Basic), `MeasureTheory.tendsto_integral_filter_of_dominated_convergence`
  (Mathlib.MeasureTheory.Integral.DominatedConvergence),
  `MeasureTheory.integrable_prod_iff`, `MeasureTheory.integral_integral_swap`
  (Mathlib.MeasureTheory.Integral.Prod). All recorded signatures and available
  docstrings were read. The proof-only modules are plain imports; the statement
  interfaces are public imports. The Schwartz module covers the final three
  proof dependency nodes and already exposes its underlying Basic module.

Edge cases: p=0 or q=0 gives zero operators and zero vector integrals, and the
bound permits C=0. Empty K forces b=0. L=0 is included. Integer powers on the
strictly positive weights permit negative r and r-d without truncation. Zero
coordinate derivative orders evaluate the actual original symbol. Arbitrarily
complex cutoffs are permitted, with no positivity or fixed-cutoff restriction.
The limit is over real radii, not only an integer subsequence. Non-minimal K
is permitted. All variables are explicitly bound; there are no auto-implicits,
local notations, private helpers, let-bindings in the statement, or extra
hypotheses supplying any conclusion.

Searches (all through the prescribed wrapper unless labelled rg):

- LeanFinder: "Fourier frequency kernel of a compactly supported smooth matrix
  symbol with polynomial symbol estimates and oscillatory cutoff quantization".
  Eight hits: Fourier evaluation, Schwartz transforms, and general Fourier
  derivative estimates. None states the parameter-uniform combined theorem.
- Loogle: `"iteratedLineDeriv", "fourierIntegral"`: zero hits.
- Mathlib grep: `symbol|oscillatory|iteratedLineDeriv`, Analysis/: returned
  iterated line derivatives, Sobolev Bessel potentials and unrelated uses of
  "symbol". No variable matrix-symbol quantization or combined statement.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `compact.symbol|symbolOperator|oscillatory|partialFourier|iteratedLineDeriv`:
  no matches. The item id also has no matches in WeilConjectures. All four
  proposed declaration names were searched in Mathlib and both project roots:
  no matches. The DAG's neighbouring `def-sfb-symbol-pseudodifferential-operators`
  gives the same normalization but has no usable recorded Lean declaration;
  its bundle/distribution framework is unnecessary for this Euclidean statement.
  The three integral/derivative helpers are concrete expressions belonging to
  this node's own formula, rather than copies of an existing definition.

The accepted DAG explicitly records an agent-supplied analytic prerequisite,
with Demailly hodge-ams.pdf WANTED locally. It is still absent locally. A fresh
attempt to open the stated official PDF URL timed out. This is not a new claim
of having read that PDF. I read the current blueprint unit and direct-images
proof under literature/blueprint/latest; the analytic route and unit statement
are unchanged. No false edge case or statement correction was found.

Validation: scompile.py compiled both sandbox and named library module cleanly
(3.4 s and 4.1 s). The first attempt diagnosed missing scoped `ContDiff` infinity
notation; adding `open scoped ContDiff` resolved it, with no mathematical change.

## Second reading by Q134

Self-check after compilation, not an independent worker review: the dispatcher
brief prohibits starting another agent and assigns independent review to the
maintainer. I reopened the node and file and matched all hypotheses and clauses
as listed above. In particular I checked operator norms instead of entrywise
matrix norms, joint rather than separate smoothness, the uniform compact set,
integer subtraction in the derivative weight, the negative transform phase,
`η - ξ` rather than its opposite, frequency rescaling by `2π`, the double-integral
prefactor, arbitrary admissible cutoffs, every compact smooth test, and a real
atTop limit. No mismatch found in this self-check. No independence is claimed.
