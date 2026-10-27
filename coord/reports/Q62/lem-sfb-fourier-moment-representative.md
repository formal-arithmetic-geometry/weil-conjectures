## Worker report

This stage-2 delivery states `MeasureTheory.Lp.fourier_moments_inverse_representative`
in `Sheaf.Analysis.FourierMomentRepresentative`. Its only proof is `sorry`.
The item has a reviewed stage-1 split but no Lean record, and appears in
`coord/queue.tsv` at stage 2. The inherited stage-1 unchanged-item rejection does
not prevent the present stage-2 statement delivery (brief-stage2 §0).
The sandbox initially contained only dispatch marker files, with no interrupted
Lean file, report, or delivery result. No dependency repair or statement change
is needed. The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- Real and complex fields are Mathlib `ℝ` and `ℂ`, with their standard `Field`
  instances. These implement the sole statement dependency `def-weil-field`
  (`Field`, Mathlib.Algebra.Field.Defs).
- Euclidean `ℝ^m` with Lebesgue measure is `EuclideanSpace ℝ (Fin m)` and `volume`.
  `m : ℕ` and `hm : 1 ≤ m` give precisely the positive dimensions in the node.
- The specified square-integrable equivalence class is
  `u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin m)))`.
- Its Plancherel Fourier transform is `𝓕 u`, with the result explicitly typed as
  the same `Lp` space before evaluation. This is the instance built from
  `Lp.fourierTransformₗᵢ`, the continuous isometric extension from Schwartz
  functions (LpSpace.lean:47–82). It has the stated negative-exponent convention.
- The measurable representative is `h : EuclideanSpace ℝ (Fin m) → ℂ`, with
  `hh : Measurable h`. `hrep` says `h ξ = (𝓕 u) ξ` almost everywhere; it does not
  identify the arbitrary representative pointwise with Mathlib's chosen one.
- The nonnegative integer order is `r : ℕ`. The hypothesis `hmom` quantifies over
  all `j : ℕ` with `j ≤ r`, and uses `Integrable (fun ξ ↦ ‖ξ‖ ^ j * ‖h ξ‖) volume`.
  For this nonnegative measurable real function this is exactly finiteness of
  the displayed moment integral. The case `j = 0` supplies integrability of `h`.
- The first conclusion gives `Integrable` for the inverse integral's integrand
  at every `x`. `(Real.fourierChar (inner ℝ ξ x) : ℂ)` is the unit-modulus
  `exp (2πi ξ·x)`, so this states absolute convergence of the displayed integral.
- The function `g` is Mathlib's existing `𝓕⁻ h`, whose defining integral is this
  positive-phase integral (`Real.instFourierTransformInv`, `Real.fourierInv_eq`
  in Mathlib.Analysis.Fourier.FourierTransform, lines 432–450). Symmetry of the
  real inner product identifies `ξ·x` and `x·ξ` from the node.
- The second conclusion `ContDiff ℝ r (𝓕⁻ h)` is exactly real-coordinate `C^r`
  regularity of this complex-valued function.
- The third conclusion `𝓕⁻ h =ᵐ[volume] (u : EuclideanSpace ℝ (Fin m) → ℂ)`
  states equality almost everywhere with the canonical representative of the
  specified class. It implies square integrability and equality of its L²
  equivalence class with `u`; no representative of a different class is chosen.

Dependencies and source declarations read in full:

- `Field`, Mathlib.Algebra.Field.Defs:170–180, the sole statement dependency.
- `MeasureTheory.Lp.fourierTransformₗᵢ`, the Fourier instances, and
  `MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq`,
  Mathlib.Analysis.Fourier.LpSpace:47–139, defining the canonical Plancherel
  extension and giving the recorded L² test-duality proof input.
- `VectorFourier.contDiff_fourierIntegral`,
  Mathlib.Analysis.Fourier.FourierTransformDeriv:507–514, the recorded
  bilinear-moment regularity input.
- `MeasureTheory.MemLp.locallyIntegrable` and
  `ContinuousOn.locallyIntegrableOn`,
  Mathlib.MeasureTheory.Function.LocallyIntegrable:351–358,566–569.
- `HasCompactSupport.toSchwartzMap` and `SchwartzMap.integrable`,
  Mathlib.Analysis.Distribution.SchwartzSpace.Basic:555–567,1131–1133.
- `VectorFourier.integral_fourierIntegral_smul_eq_flip`,
  Mathlib.Analysis.Fourier.FourierTransform:242–248.
- `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`,
  Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff:205–213.
- Also read the evaluation formulas `Lp.toTemperedDistribution_apply` and
  `TemperedDistribution.fourierInv_apply` from the recorded test-duality match.

All seven proof dependencies are Mathlib leaves. Their source modules are
imported, directly or through the public statement imports. In particular,
LpSpace imports TemperedDistribution, which publicly imports SchwartzSpace.Fourier
and hence SchwartzSpace.Basic; FourierTransformDeriv imports FourierTransform.
LocalIntegrability and AEEqOfIntegralContDiff are explicit plain proof imports.
The docstring carries the four accepted proof steps and the node identifiers.

Edge cases checked: `r = 0` retains the zeroth moment, so both absolute
convergence and continuity are asserted. At `u = 0`, a nonzero representative
on a null set is allowed by `hrep` and has zero inverse integral. Changing `h`
on a null set does not change any conclusion. Dimension `m = 1` is included;
`m = 0` is excluded exactly as in the node. No continuity, L¹ hypothesis on
`u`, pointwise inversion hypothesis, or additional moment is imposed.
The real inner product and Fourier signs were checked against the Mathlib
function-transform definitions. No new definition, axiom, or hollow data is used.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder`: "An L2 function whose Fourier transform has
  integrable moments has a Cr inverse Fourier integral representative equal
  almost everywhere to the original class". Eight hits: pointwise inversion,
  Schwartz-to-L² compatibility, and Fourier instances, none the full statement.
- `msearch.py ... loogle`: `"contDiff", "fourier"`. Three hits:
  `Real.contDiff_fourier`, `ContDiff.fourierPowSMulRight`, and
  `VectorFourier.contDiff_fourierIntegral`; only regularity, no L² identification.
- `msearch.py ... grep`: `fourierInv.*ae|ae.*fourierInv|contDiff_fourierIntegral`
  under `Analysis`. Five hits on Fourier congruence and integral regularity.
- `msearch.py ... leansearch`: "Integrable polynomial moments of the L2 Fourier
  transform give a Cr inverse Fourier integral equal to the original L2
  function almost everywhere". Eight inversion hits, requiring continuity of
  the original function or giving the pointwise integral transform, not the
  asserted representative theorem for an arbitrary L² class. Read
  `Integrable.fourierInv_fourier_eq` at Inversion.lean:165 to check the mismatch.
- `rg -n 'fourier.*[Mm]oment|[Mm]oment.*[Rr]epresent|fourierInv.*ae|ae.*fourierInv'`
  over `lean/WeilConjectures` and `lean/Sheaf`: no match.
- `grep -rn 'lem-sfb-fourier-moment-representative' lean/WeilConjectures`:
  no match. Upstream name-index Fourier matches concern sheaf transforms,
  not this scalar Euclidean analytic assertion.

Validation: the first server compile exposed Lean selecting a function-valued
Fourier transform when the result of `𝓕 u` was coerced immediately. The statement
now types the result in L² before evaluating it. All binders are explicit and
`autoImplicit` is disabled. The repaired module compiled cleanly in sandbox mode (1.9 seconds) and library
mode (1.8 seconds), with only the expected sorry warning. The first deliver2.py
--no-push run passed preflight and compilation (dry-run commit 669066cf82a).

No statement dispute or mathematical node fault was found.

## Second reading by Q62

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
