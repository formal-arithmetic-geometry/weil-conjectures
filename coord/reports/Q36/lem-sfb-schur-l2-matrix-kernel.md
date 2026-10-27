## Worker report

The module `Sheaf.MeasureTheory.SchurL2MatrixKernel` states
`MeasureTheory.exists_schurL2MatrixKernel`, with one `sorry` and no new definitions.
The item statement is unchanged. No missing dependency, new node, or statement dispute was found.

Hypothesis and conclusion correspondence:

- Real and complex fields: Mathlib `ℝ` and `ℂ`, with their existing `Field` instances.
- Integers m ≥ 1 and p,q ≥ 0: `(m p q : ℕ) (hm : 1 ≤ m)`. There is no positivity
  hypothesis on p or q.
- The domain ℝ^m: `EuclideanSpace ℝ (Fin m)`, with its canonical `volume` (Lebesgue
  measure normalized by an orthonormal basis).
- The fibres ℂ^p and ℂ^q: `EuclideanSpace ℂ (Fin p)` and `EuclideanSpace ℂ (Fin q)`.
  The kernel values are `→L[ℂ]` between them. In finite dimensions every complex-linear map
  is continuous, so this represents exactly Hom_ℂ and carries its Euclidean operator norm,
  rather than the maximum-entry or maximum-row-sum matrix norm.
- Joint Lebesgue measurability: `hG` is `NullMeasurable G (volume.prod volume)` with the
  matrix-space measurable structure explicitly supplied as `borel (...)` (no local instance).
  `NullMeasurable` means every Borel preimage is measurable for the completion of product
  volume, exactly Lebesgue measurability. This allows completion-measurable kernels and
  does not strengthen the node to Borel measurability.
- Finite real constants: `(a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)`.
- Row bound: `hrow` says `∀ᵐ x ∂volume, ∫⁻ y, ‖G (x,y)‖ₑ ≤ ENNReal.ofReal a`.
- Column bound: `hcol` says `∀ᵐ y ∂volume, ∫⁻ x, ‖G (x,y)‖ₑ ≤ ENNReal.ofReal b`.
  These are nonnegative extended integrals, so their finite upper bounds include finiteness.
  In particular, a divergent norm integral cannot accidentally satisfy the assumption
  through the zero convention for the real Bochner integral.
- L²: `Lp (EuclideanSpace ℂ (Fin p)) 2 volume` and the analogous output space. Mathlib
  defines these using finite `eLpNorm` in `AEEqFun`, the quotient by almost-everywhere equality.
  For these separable finite-dimensional targets this is exactly completed-Lebesgue-measurable
  finite squared-norm-integral functions modulo almost-everywhere equality.
- Bounded complex-linearity: the existential witness `T` has type `→L[ℂ]` between those
  two L² spaces, including linearity and continuity.
- The estimate is the first conjunct for every `h`:
  `‖T h‖ ≤ Real.sqrt (a * b) * ‖h‖`.
- An arbitrary representative is `f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℂ (Fin p)`
  with `f =ᵐ[volume] h`. This equality already implies the same L² membership, so no extra
  representative regularity hypothesis is necessary.
- Almost-everywhere absolute convergence is
  `∀ᵐ x ∂volume, Integrable (fun y ↦ G (x,y) (f y)) volume`. Mathlib `Integrable` means
  almost-everywhere strong measurability plus finite integral of the norm.
- The integral determines the output class: `(T h : ... → ...) =ᵐ[volume]
  (fun x ↦ ∫ y, G (x,y) (f y))`.
  Since this holds for every representative f of h and the output is a single L² element,
  the statement includes independence of representatives. Values on exceptional null sets
  are immaterial. The Bochner integral is zero on nonintegrable sections, consistent with
  this almost-everywhere formula.

Dependency declarations read and used:

- `def-weil-field` is a Mathlib node with match `Field` in
  `Mathlib.Algebra.Field.Defs`; read the full class and docstring. `ℝ` and `ℂ` use their
  canonical instances; no replacement field definition or module is needed.
- Existing Mathlib notions: `EuclideanSpace` (`Mathlib.Analysis.InnerProductSpace.PiL2`),
  `ContinuousLinearMap`, `MeasureTheory.Lp` (`Mathlib.MeasureTheory.Function.LpSpace.Basic`),
  `MeasureTheory.NullMeasurable` (`Mathlib.MeasureTheory.Measure.NullMeasurable`),
  `volume` for real inner product spaces, `Integrable`, and Bochner/extended integration.
- All four proof dependencies are Mathlib leaves, not missing Lean modules. Their recorded
  APIs are retained through imports: `AEStronglyMeasurable.integral_prod_right'`,
  `prodMk_left`, `comp_snd` and `NullMeasurable.aemeasurable`; `lintegral_prod`,
  `lintegral_prod_symm`, `AEMeasurable.lintegral_prod_right`, `ae_lt_top'`,
  `lintegral_mono_ae`, `lintegral_const_mul''`; `L2.innerProductSpace`, `L2.inner_def`,
  `L2.integrable_inner`, `Lp.instCompleteSpace`, `norm_inner_le_norm`; `Integrable.mono'`,
  `norm_integral_le_of_norm_le`, `integral_add`, `integral_smul`, `integral_congr_ae`.
  L² and Haar imports expose the required basic norm/integral APIs; `Integral.Prod` and
  `Integral.Lebesgue.Markov` are plain imports for the additional proof-dependency APIs.
  The six-step natural-language proof in the declaration follows the node verbatim in substance.

Edge cases checked before writing: p = 0 or q = 0 makes the integrand zero; no `Nonempty (Fin p)`
or `Nonempty (Fin q)` is imposed. If a = 0 or b = 0, the norm estimate forces the zero output
class; the proof uses Cauchy–Schwarz without division. m = 1 is included. A zero input class,
the zero kernel, and arbitrary changes of representatives on a null set satisfy the same
formula. As a nonzero check, a scalar kernel supported on a unit cube in each variable has
a = b = 1 and induces the expected rank-one averaging operator. No global integrability of
the kernel or finite measure of ℝ^m is assumed.

Searches (2026-10-24):

- `msearch.py ... leanfinder "Schur test measurable matrix integral kernel row column
  integral bounds bounded operator L2"`: 8 hits, including `Real.integrable_prod_sub`,
  `ContinuousLinearMap.integrable_of_bilin_of_bdd_left/right`,
  `MeasureTheory.Integrable.op_fst_snd`, and continuous-linear-map product integrability.
  These concern bilinear integrability, convolution, or integrable maps, not the Schur test.
- `msearch.py ... loogle '"Schur", "Lp"'`: 0 hits.
- `msearch.py ... leansearch "Schur integral operator measurable matrix kernel bounded
  row column integrals gives bounded L2 map"`: 8 hits, including `SchwartzMap.integralCLM`,
  `MeasureTheory.setToFun`, and measurable parameter integrals. None states this criterion.
- `msearch.py ... grep "Schur|schur|integral.*kernel.*norm" MeasureTheory`: 0 hits.
- `rg -n "schur|Schur|schur_l2_matrix|schurL2" lean/WeilConjectures lean/Sheaf`:
  only unrelated representation-theoretic Schur lemmas and block-matrix Schur complements.
- `rg -n "lem-sfb-schur-l2-matrix-kernel" lean/WeilConjectures`: no hits.
- Full-name search for `exists_schurL2MatrixKernel` in Mathlib, WeilConjectures, Sheaf,
  and `dag/lean_names_upstream.json`: no hits.
- Read the source node and all its statement/proof dependency records. The source PDF
  remains absent from the named local literature checkout. Web search located Demailly's
  `https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/hodge-ams.pdf`, but opening
  it timed out. I do not claim to have read it; this is the agent-supplied prerequisite and
  detailed proof already recorded in the accepted node, with its source availability caveat.

Validation: `scompile.py Q36 lem-sfb-schur-l2-matrix-kernel <module>` compiled the sandbox
and actual module cleanly (8.5 s and 2.8 s). The initial probe found no default measurable
space on continuous linear maps; the delivered statement explicitly supplies their Borel
structure and then compiles without warnings. No hypothesis or mathematical statement changed.

## Second reading by Q36

Author's second reading, with the node and final file open; no independent worker was started,
as required by the dispatcher. The maintainer supplies the independent review.

Rechecked each clause against the correspondence above: the finite nonnegative constants,
Lebesgue completion, Euclidean operator norm, both marginal bounds, arbitrary L² input,
almost-everywhere absolute convergence, output membership, representative independence,
complex-linearity and the exact √(ab) bound are all present. The two subtle points were checked
explicitly: finite marginal integrals use `lintegral`, and the integral formula quantifies over
all representatives rather than only Mathlib's chosen one. No missing or additional mathematical
hypothesis was found. The Borel structure on the matrix target is explicit because the first
compiler run found that Mathlib does not install one by default. The declaration has only a
`sorry` proof, and introduces no chosen data, private notation, or local instances.
