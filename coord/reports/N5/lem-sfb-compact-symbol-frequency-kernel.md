## Worker report

The module `Sheaf.Analysis.CompactSymbolFrequencyKernel` states
`EuclideanSpace.compactSymbol_frequencyKernel`, with its sole theorem proof `sorry`.
Three concrete helpers expand the notation already introduced by this node:
`symbolMultiIndexDeriv`, `compactSymbolOperator`, and `cutoffSymbolOperator`.
They contain actual derivatives or Bochner integrals, no postponed data or proofs.
There are no new DAG nodes, dependency repairs, or statement corrections. The node
copy changes only `lean`; its natural-language statement and dependency lists are unchanged.

Hypothesis-by-hypothesis correspondence:

- Real and complex fields [def-weil-field] are Mathlib `ℝ`, `ℂ`, with their existing
  `Field` instances. The dependency match `Field` was read in
  `Mathlib.Algebra.Field.Defs` (including its docstring and full class signature).
- Integers m ≥ 1, p,q ≥ 0 are `m p q : ℕ` and `hm : 1 ≤ m`. Both ranks may be zero.
  The order is `r : ℤ`, with no sign restriction.
- Real Euclidean space is `EuclideanSpace ℝ (Fin m)`; complex Euclidean spaces
  are `EuclideanSpace ℂ (Fin p)` and `EuclideanSpace ℂ (Fin q)`.
  Matrices are `→L[ℂ]` between those spaces. Their norm is precisely the operator
  norm for the Euclidean norms, rather than a matrix-entry or supremum norm.
- The symbol `b` is a function from the product of two real Euclidean spaces into
  those operators. `hb : ContDiff ℝ ∞ b` gives joint smoothness.
- A fixed compact spatial set is the explicit `K` with `hK : IsCompact K`.
  `hsupp` says for every x and ζ, x outside K implies b(x,ζ)=0; K is independent of ζ.
- Multi-indices are `α β : Fin m → ℕ`. `symbolMultiIndexDeriv α β b` applies
  frequency coordinate derivatives with multiplicities β and spatial coordinate
  derivatives with multiplicities α. Finite lists are ordered by coordinate and
  folded with `fderiv ℝ` evaluated on the standard Euclidean coordinate vectors.
  Smoothness makes the coordinate orders commute. `hest` quantifies a finite real
  constant for every pair and bounds the operator norm by
  `c * (1 + ‖ζ‖) ^ (r - (∑ j, β j : ℕ))`; the exponent is an integer and the natural
  derivative order is coerced to that integer. The constant is uniform in x and ζ.

Conclusion-by-conclusion correspondence:

- Mathlib `𝓕 (fun x ↦ b (x,ζ)) θ` is exactly the displayed spatial Fourier integral.
  `Real.fourier_eq'` has phase `exp ((-2π ⟪x,θ⟫) i)` and Lebesgue `volume`.
  The first conjunct quantifies `L : ℕ`, then a finite real C, then all θ and ζ,
  and bounds its operator norm by `C*(1+‖θ‖)^(-L)*(1+‖ζ‖)^r`.
- `f : SchwartzMap ... ...` is an arbitrary vector-valued Schwartz function;
  Mathlib's `𝓕 f` is its Schwartz Fourier transform with the same normalization.
  Its construction and defining integral were read in
  `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier`.
- `compactSymbolOperator b f x` is the exact positive-phase integral in the node:
  `exp (2πi ⟪x,ξ⟫)` multiplying `b(x,2πξ)` applied to `𝓕 f ξ`.
  The first f-dependent conjunct is `Integrable` of exactly that integrand at every x,
  expressing absolute convergence in the finite-dimensional Banach output.
- `ContDiff ℝ ∞ (compactSymbolOperator b f)` gives smoothness and
  `tsupport (compactSymbolOperator b f) ⊆ K` gives the asserted support, including
  the closure convention. No unspecified output representative is used.
- The next conjunct is the exact kernel identity for all η: the Fourier transform
  of this same operator equals the integral of the spatial Fourier transform of b
  at `(η-ξ,2πξ)` applied to `𝓕 f ξ`. It retains the minus sign and 2π rescaling.
- `cutoffSymbolOperator` is the actual product Bochner integral over `(y,ζ)` with
  prefactor `(2 * (Real.pi : ℂ)) ^ (-(m : ℤ))`, phase
  `exp (i ⟪x-y,ζ⟫)`, and factor `χ (R⁻¹ • ζ)`.
- The final conjunct quantifies every complex-valued smooth compactly supported χ,
  with `∀ᶠ ζ in 𝓝 0, χ ζ = 1` expressing equality to one near zero.
  It quantifies every complex-valued smooth compactly supported test φ and asserts
  convergence of its vector-valued pairing with the actual cutoff operator to its
  pairing with `compactSymbolOperator`, as `R : ℝ` tends to `atTop`.
  The atTop filter is eventually positive; no condition at R=0 is asserted.
  Scalar tests and vector integrals test every output coordinate. Conversely,
  finite sums of these pairings include every dual-vector test, so this is precisely
  distributional equality, with bilinear testing convention and no conjugation.

Dependency declarations and imports:

- Statement dependency def-weil-field: `Field`,
  `Mathlib.Algebra.Field.Defs`, available through public Mathlib imports.
- Public statement imports:
  `Mathlib.Analysis.Distribution.SchwartzSpace.Fourier` (`SchwartzMap`, its Fourier
  transform and function Fourier transform) and
  `Mathlib.Analysis.InnerProductSpace.PiL2` (`EuclideanSpace`, coordinate vectors).
- Proof dependencies are all Mathlib leaves. Their full signatures were inspected;
  plain proof imports record the plan without making them statement dependencies:
  `Mathlib.Analysis.Calculus.ParametricIntegral`
  (`hasFDerivAt_integral_of_dominated_of_fderiv_le`),
  `Mathlib.Analysis.SpecialFunctions.JapaneseBracket`
  (`integrable_rpow_neg_one_add_norm_sq`),
  `Mathlib.MeasureTheory.Function.Jacobian`
  (`MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`),
  `Mathlib.MeasureTheory.Integral.DominatedConvergence`
  (`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`), and
  `Mathlib.MeasureTheory.Integral.Prod` (`integrable_prod_iff`, `integral_integral_swap`).
  The integral majorant declarations `Integrable.mono'` and
  `norm_integral_le_of_norm_le` are in Mathlib's L1/Bochner infrastructure.
  The Schwartz Fourier import supplies `SchwartzMap.fourier_lineDerivOp_eq`,
  `SchwartzMap.integral_norm_sq_fourier`, `SchwartzMap.lineDerivOp_fourier_eq`,
  `SchwartzMap.fourierTransformCLM`, its inverse and Fourier-pair instances.
  Its public Basic dependency supplies `HasCompactSupport.toSchwartzMap` and
  `SchwartzMap.integrable`.

Edge cases checked before writing and again against the final signature:
p=0 or q=0 gives the zero operator/output without a positive-rank assumption;
empty K forces b and its operator to zero; L=0 gives the undifferentiated bound;
zero multi-indices give b itself (empty folds); m=1 is included; both signs of r
are retained through integer powers of strictly positive bases. No positivity,
real-valuedness or normalization beyond one near zero is imposed on χ. Tests
include zero tests. The real limit permits every positive dilation to infinity.
The prefactor and frequency substitution cancel by the Jacobian `(2π)^m`.

Searches (2026-10-24):

- msearch LeanFinder, query "Compactly supported smooth matrix symbol Fourier frequency
  kernel rapid decay and oscillatory quantization": eight hits, including
  `SchwartzMap.fourier_evalCLM_eq`, `Real.pow_mul_norm_iteratedFDeriv_fourier_le`,
  Schwartz Fourier bilinear identities and `fourierTransformCLM`. These are proof
  ingredients, not the combined parameter-uniform statement and oscillatory comparison.
- msearch Loogle, query `"fourierIntegral", "iteratedFDeriv"`: five hits on
  `VectorFourier` derivative/weighted Fourier-integral results, not this assertion.
- msearch LeanSearch, query "Fourier kernel of compactly supported matrix symbol rapid
  decay equals oscillatory integral operator": eight hits on basic Fourier integrals,
  inverse transforms and Schwartz transform instances; no statement match.
- msearch grep, regex `symbol|oscillatory|fourierIntegral`, `Analysis/Fourier/`:
  basic Fourier integrals, Poisson summation and Fourier derivative results; no symbol
  operator or frequency-kernel theorem.
- Repository `rg` on `lean/WeilConjectures` and `lean/Sheaf` for
  `symbol|oscillatory|frequencyKernel|frequency_kernel`: algebraic symbols and unrelated
  category-theoretic uses, no analytic symbol operator or theorem. The prescribed
  upstream grep for the node id found no occurrence.
- Inspected the existing scalar `EuclideanSpace.multiIndexPartialDeriv` in
  `Sheaf.Analysis.L2WeakDerivativeFourierIdentity`. It accepts only a scalar-valued
  function on one Euclidean space. It cannot provide the matrix-valued two-variable
  mixed derivative here. The local helper expands this node's derivative notation,
  without introducing a competing scalar derivative notion or a generic symbol class.
- Exact-name searches for all four new names in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf` found no occurrence.

Source context: read the latest blueprint unit sk-thm-sf-ctf-stability and its
current direct-images proof (3). This item is the existing agent-written analytic
prerequisite deep below that route, not the unit's own statement. The Demailly Hodge
AMS PDF remains WANTED as already recorded by stage 1; the module and proof docstring
honestly retain that status. The six-step DAG proof is fully transcribed into the
main theorem docstring with its named supporting nodes.

Validation: scompile.py compiled the file in both sandbox and library module modes
on the server, with no errors or warnings (about 3.6 and 3.5 seconds respectively).
All variables are explicitly bound, autoImplicit is disabled, and every line is
at most 100 characters. There are no disputed statements or detected node faults.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
