## Worker report

The delivery states `SchwartzMap.exists_compactlySupported_multiIndex_l2_approximation`
in `Sheaf.Analysis.SchwartzCutoffL2Approximation`. Its only theorem proof is `sorry`.
No definitions, dependency modules, new nodes, or statement corrections are needed.
The node's natural-language statement and all dependency lists are unchanged.

Clause-by-clause correspondence:

- The real and complex fields are Mathlib `ℝ` and `ℂ`. The sole statement dependency,
  `def-weil-field`, has `mathlib_match = ["Field"]`; `Field` is the class in
  `Mathlib.Algebra.Field.Defs`. Its `Real.instField` and `Complex.instField` instances
  supply the two fields. There is no project-specific field definition to import.
- Euclidean `ℝ^m` is `EuclideanSpace ℝ (Fin m)`. The explicit binders `(m : ℕ)` and
  `(hm : 1 ≤ m)` retain precisely the stated positive dimensions, with no extra restriction.
  `volume` is its canonical Euclidean Lebesgue measure, supplied through
  `Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace`. In that module,
  `PiLp.volume_preserving_toLp` identifies it with the product Lebesgue measure.
- `ψ : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ` is exactly the specified Schwartz class.
  Mathlib `SchwartzMap.smooth'` requires real `ContDiff ℝ ∞`, and `decay'` gives a finite
  uniform bound on `‖x‖ ^ k * ‖iteratedFDeriv ℝ n ψ x‖` for every natural `k,n`.
  These are the node's smoothness and bounded-derivative conditions, not additional assumptions.
- `(s : ℕ)` ranges over all nonnegative integers, including zero.
- `∃ φ : ℕ → EuclideanSpace ℝ (Fin m) → ℂ` chooses one sequence before any multi-index.
  `∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n)` says that every term is smooth
  in real coordinates and that the closure of its nonzero locus is compact.
- `β : Fin m → ℕ` is exactly the multi-index. `(∑ j, β j) ≤ s` is its total-order bound.
  Write L for the explicit expression
  `(List.ofFn (fun j : Fin m ↦ List.replicate (β j) j)).flatten` in the signature.
  L lists j exactly β j times, in increasing coordinate order; its length is ∑ j, β j.
  The expression `iteratedFDeriv ℝ L.length f x (fun i ↦ EuclideanSpace.single (L.get i) 1)`
  evaluates the derivative on exactly that list of standard coordinate vectors.
  For smooth f, `DifferentiableAt.iteratedFDeriv_succ_apply_left'` identifies this with
  successive directional differentiation, hence precisely ∂^β f. Smoothness gives
  commutation if another ordering of the product notation is used.
- The first `MemLp ... 2 volume` asserts square integrability of ∂^β ψ; the next
  `∀ n, MemLp ... 2 volume` asserts it for every ∂^β (φ n). Their differences are therefore
  square integrable as well, by subtraction. None of these is silently assumed.
- `Tendsto (fun n ↦ Real.sqrt (∫ x, ‖... - ...‖ ^ 2 ∂volume)) atTop (𝓝 0)` is the
  displayed L² convergence with exactly the node's square-root-of-integral norm.
  The complex norm is complex absolute value. Both derivative terms use the same β.

Dependency interfaces read and retained for the proof plan:

- `lem-sfb-euclidean-smooth-ball-bump`: `ContDiffBump` in
  `Mathlib.Analysis.Calculus.BumpFunction.Basic`, with the inner-product-space instance in
  `Mathlib.Analysis.Calculus.BumpFunction.InnerProduct`. Read its data, `contDiff`,
  `nonneg`, `le_one`, `one_of_mem_closedBall`, `tsupport_eq`, and `hasCompactSupport`.
- `lem-sfb-schwartz-test-inclusion-integrability`: `HasCompactSupport.toSchwartzMap`
  and `SchwartzMap.integrable` in `Mathlib.Analysis.Distribution.SchwartzSpace.Basic`.
  Read both signatures and the construction, which retains the original function.
- `lem-sfb-schwartz-l2-coordinate-calculus`: `SchwartzMap.memLp` and
  `SchwartzMap.smulLeftCLM_apply` in the same Basic module; the `LineDeriv` instance and
  `SchwartzMap.lineDerivOp_apply_eq_fderiv` in
  `Mathlib.Analysis.Distribution.SchwartzSpace.Deriv`. The latter module is imported
  non-publicly for the proof plan.
- `lem-sfb-real-dominated-integral-convergence`:
  `MeasureTheory.tendsto_integral_of_dominated_convergence` in
  `Mathlib.MeasureTheory.Integral.DominatedConvergence`, imported non-publicly.
  Its real norm bound and almost-everywhere limit match the proposed squared-error proof.

The theorem docstring contains all six proof steps: choose the bounded smooth bump;
scale and multiply it with ψ; derive chain/product formulas by induction;
prove eventual pointwise vanishing of the error; exhibit the explicit integrable
finite-sum dominating function; apply dominated convergence and take square roots.
The source PDF is absent locally, as the node explicitly records. The current blueprint
unit `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
was read. This is an agent-stated analytic prerequisite, not a claimed numbered source theorem;
the delivery preserves that attribution and does not change the blueprint unit.

Edge cases checked before writing:

- s = 0 and β = 0: L is empty, and `iteratedFDeriv_zero_apply` is f itself.
  The conclusion is ordinary function approximation in L², not a vacuous derivative condition.
- m = 1: L repeats the single coordinate β 0 times; this is the ordinary repeated derivative.
- Mixed multi-indices, such as (2,1): L is (0,0,1), of length three, so neither mixed
  differentiation nor multiplicity is lost. Zero coordinates contribute empty sublists.
- ψ = 0 is allowed, and the zero sequence satisfies all clauses mathematically.
- Every sequence index includes n = 0; the proof plan uses R_n = n+1, avoiding zero dilation.
- A single φ is chosen outside `∀ β`; there is no separate approximation sequence for each β.

Searches for existing statements and notions:

- `msearch.py leansearch`, query "Smooth compactly supported approximations of all derivatives
  of a Schwartz function in L2": hits include `Lp.dense_hasCompactSupport_contDiff`,
  `HasCompactSupport.exist_eLpNorm_sub_le_of_continuous`, and `SchwartzMap.smooth`.
  These provide function approximation or regularity, not simultaneous derivative approximation.
- `msearch.py leanfinder`, query "Schwartz function approximated by smooth compactly supported
  functions with each multi-index derivative converging in L2": eight hits, including
  `SchwartzMap.denseRange_toLpCLM`, `HasCompactSupport.toSchwartzMap`, and
  `MemLp.exist_eLpNorm_sub_le`. None states the derivative approximation assertion.
- `msearch.py loogle`, query `"SchwartzMap", "tendsto"`: only `SchwartzMap.tendsto_cocompact`,
  which concerns spatial decay of one Schwartz function, not convergence of approximants.
- `msearch.py grep`, pattern `multiIndex|multi_index|iteratedFDeriv|dense|cutoff`, restricted
  to `Analysis/Distribution/SchwartzSpace`: derivative descriptions and operators, but no
  simultaneous compact-cutoff approximation statement.
- Direct `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for
  `schwartz.*(approx|cutoff)|multiIndexPartialDeriv` found the downstream theorem
  `MeasureTheory.Lp.fourier_weak_multiIndex_derivative`, whose proof cites this node,
  and its concrete coordinate-derivative helper. No equivalent approximation statement exists.
  Importing that downstream helper would obstruct the proof-dependency import, so the present
  statement uses Mathlib's general iterated derivative directly, without defining another helper.
  The downstream folded derivative and the present multilinear evaluation agree on smooth
  functions by iterated Fréchet differentiation. Also searched the exact node id in
  `lean/WeilConjectures`: no occurrence.
- Read `Mathlib.Analysis.Normed.Lp.SmoothApprox` and the relevant Basic Schwartz declarations;
  ordinary Lp density does not control derivatives simultaneously.

No statement dispute or mathematical node fault was found.

Validation: server compilation uses the required `scompile.py` wrapper with the standard
60-second limit. Initial checks identified a missing import for the canonical Euclidean
volume instance; the statement was unchanged while the import was repaired. The final
compile and delivery-preflight outcomes are recorded below.

Final single-file server compile: PASS, sandbox 19.2 s and library module 2.7 s; no errors
or non-sorry warnings.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
