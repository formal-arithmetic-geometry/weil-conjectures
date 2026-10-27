## Worker report

The module `Sheaf.Analysis.Complex.CutoffCauchyTransform` states the node verbatim in
mathematical content. Its main declaration is
`Complex.exists_cutoffCauchyTransform_parameters`. It also gives real data definitions
for the node's integrand, integral operator, and parameter multi-index derivative:
`Complex.cutoffCauchyIntegrand`, `Complex.cutoffCauchyTransform`, and
`Complex.cutoffCauchyParameterDeriv`. These expand objects introduced in the node itself;
they do not introduce an independent prerequisite notion. No new nodes, dependency
modules, statement correction, or mathematical dispute is needed. The sole postponed
proof is the main theorem, with the complete five-step DAG proof in its docstring.

Hypothesis and clause correspondence:

- The usual real and complex fields are Mathlib `ℝ` and `ℂ`, with their existing `Field`
  instances. The sole statement dependency `def-weil-field` records Mathlib `Field` in
  `Mathlib.Algebra.Field.Defs`; its full signature and docstring were read.
- `c : ℂ`, `r R : ℝ`, `hr : 0 < r`, and `hrR : r < R` are exactly the center and radius
  assumptions. The two disks are `Metric.ball c R` and `Metric.ball c r`.
- The existential cutoff has type `χ : ℂ → ℝ`. `ContDiff ℝ ∞ χ` means smooth in real
  coordinates. `∞` uses Mathlib's `ContDiff` scope: it is infinite differentiability,
  not the stronger analytic order `ω`.
- A neighborhood of the smaller disk's closure is expressed as
  `∃ U : Set ℂ, IsOpen U ∧ closure (Metric.ball c r) ⊆ U ∧ ∀ z ∈ U, χ z = 1`.
  Compact support inside the larger open disk is exactly
  `IsCompact (tsupport χ) ∧ tsupport χ ⊆ Metric.ball c R`; `tsupport` is the closure
  of the nonzero locus, as specified by the node.
- The cutoff is quantified before `m`, `P`, and `h`, so it depends only on `c,r,R`.
  `m : ℕ` ranges over every nonnegative integer. `Fin m → ℝ` is real coordinate space.
  `P : Set (Fin m → ℝ)` together with `IsOpen P` gives every open parameter domain.
- The input is an ambient representative `h : ℂ × (Fin m → ℝ) → ℂ`, subject only to
  `ContDiffOn ℝ ∞ h (Metric.ball c R ×ˢ P)`. This encodes exactly a smooth function
  on the specified open domain: every such function has an ambient extension by zero,
  without a continuity requirement outside the domain. None of the conclusions depends
  on representative values outside that domain. Conversely restriction gives the node's
  input function. This is an encoding, not a stronger extension hypothesis.
- `cutoffCauchyIntegrand` is `(χ ζ : ℂ) * h (ζ,t) / (z-ζ)` inside the larger disk and
  zero outside. This is precisely the stated zero extension `H` divided by `z-ζ`.
  Division in `ℂ` gives zero when `ζ=z`, including when that point is inside the disk.
- `cutoffCauchyTransform` is `(Real.pi : ℂ)⁻¹` times the Bochner integral of that
  integrand. The imported `Mathlib.MeasureTheory.Measure.Lebesgue.Complex` identifies
  `volume` on `ℂ` with planar Lebesgue measure; this is `dA`, without normalization.
- Absolute convergence is `Integrable (cutoffCauchyIntegrand ... z t) volume` for every
  `z` and every `t ∈ P`. For a finite-dimensional complex-valued function, this is the
  usual measurable, absolutely integrable condition. Joint smoothness is
  `ContDiffOn ℝ ∞ (cutoffCauchyTransform ...) (Set.univ ×ˢ P)`.
- The Wirtinger identity on the larger disk is the explicit expression
  `(fderiv ℝ (fun w ↦ T (w,t)) z 1 + I * fderiv ℝ (fun w ↦ T (w,t)) z I) / 2`
  equal to `(χ z : ℂ) * h (z,t)`, with `z ∈ Metric.ball c R` and `t ∈ P`.
  The real directions `1` and `I` are the `x` and `y` coordinate directions; no complex
  differentiability assumption replaces real differentiability.
- The parameter clause quantifies over exactly `ν : Fin m → ℕ` and all `z,t` with
  `t ∈ P`. `cutoffCauchyParameterDeriv` builds the ordered list containing coordinate
  `j` exactly `ν j` times using `List.ofFn`, `List.replicate`, and `List.flatten`,
  then folds real coordinate derivatives over it. Each derivative is the existing
  `fderivWithin ℝ (fun s ↦ g (q.1,s)) P q.2 (Pi.single j 1)`. On the open `P` this
  is the usual partial derivative. Thus the equality is exactly
  `∂_t^ν (Tχ h) = Tχ (∂_t^ν h)`. Fixed coordinate order is immaterial for smooth inputs.
- The smaller-disk conclusion repeats the same Wirtinger expression equal to `h (z,t)`
  with `z ∈ Metric.ball c r` and `t ∈ P`.
- Complex linearity quantifies over every other smooth representative `g`, both
  `α β : ℂ`, and every point of `ℂ × P`. It states pointwise
  `Tχ (α*h + β*g) = α*Tχ h + β*Tχ g`, exactly complex linearity on smooth inputs.

Dependencies and proof plan: the statement uses Mathlib `Field`, `ContDiff`,
`ContDiffOn`, `fderiv`, `fderivWithin`, `Integrable`, `volume`, `Metric.ball`,
`closure`, and `tsupport`. The full relevant signatures and docstrings were read.
The stated proof dependencies `lem-sfb-euclidean-smooth-ball-bump` and
`lem-sfb-locally-integrable-parametric-convolution` are Mathlib leaves, supplied by
`ContDiffBump` and the convolution declarations. The imports include
`Mathlib.Analysis.Calculus.BumpFunction.InnerProduct` as a proof import and
`Mathlib.Analysis.Calculus.ContDiff.Convolution` publicly, which also supplies the
calculus used by the statement. The latter contains
`MeasureTheory.contDiffOn_convolution_right_with_param` and
`MeasureTheory.hasFDerivAt_convolution_right_with_param`, whose source signatures
and docstrings were read. The proof dependency `lem-sfb-cauchy-green-test-function`
has no Lean record or Mathlib match and hence no module to import at this time.
It is needed only for the proof, not to type this statement; the docstring names
its two uses explicitly. All existing statement and proof splits are preserved.

Edge cases checked before writing: when `m=0`, the parameter space is a singleton,
the unique multi-index gives an empty derivative list and the derivative helper is
the identity. The same is true for the zero multi-index for every `m`. An empty
`P` imposes no evaluations, convergence, or linearity constraints, while the cutoff
existence remains required. At `ζ=z`, division gives zero. Boundary and exterior
values of the input are discarded by the conditional integrand; compact support
strictly inside the larger disk makes the zero extension smooth. The closure of
the smaller disk is explicitly included in an open region where the cutoff is one.
No boundedness, compactness, nonemptiness, or uniform-in-parameter growth assumption
on `P` or `h` is added. Every ambient space here is the usual finite-dimensional
real or complex space, so there are no implicit universe restrictions.

Searches made:

- `msearch.py leanfinder`, query "The cutoff Cauchy transform is smooth with real
  parameters and solves the antiholomorphic derivative equation": eight unrelated
  differentiability results, including `Complex.HadamardThreeLines.diffContOnCl_invInterpStrip`
  and `Function.Periodic.contDiff_qParam`; no match.
- `msearch.py loogle`, query `"convolution", ContDiff`: six generic convolution
  results, including `HasCompactSupport.contDiff_convolution_right` and
  `HasCompactSupport.hasFDerivAt_convolution_right`. These do not state the cutoff
  Cauchy--Green or multi-index right-inverse assertion.
- `msearch.py leansearch`, query "The cutoff Cauchy transform solves the
  antiholomorphic derivative equation and commutes with all real parameter derivatives":
  eight results on circle integrals and conformality, including
  `DifferentiableOn.deriv_eq_smul_circleIntegral`, `Complex.circleTransform`, and
  `complexOfReal_hasDerivWithinAt`; none is this real-smooth plane integral theorem.
- `msearch.py grep`, query
  `Cauchy.*transform|Cauchy.*Green|wirtinger|Wirtinger|barPartial|parameterPartial`
  in Mathlib `Analysis`: no hits.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf`, using
  `cauchyTransform|cauchy_transform|CauchyTransform|wirtinger|Wirtinger|barPartial|parameterPartial|lem-sfb-cauchy-transform-parameters`:
  no hits. A further search of `dag/lean_names_upstream.json` and both source trees
  for `cutoffCauchy|Cauchy.*transform|Cauchy.*Green|Wirtinger` also found no hit.
- Mathlib calculus source search for multi-index partial-derivative definitions
  found no existing named multi-index helper. The delivered helper directly iterates
  Mathlib's existing real derivative and is tied to the derivative clause of this node.

Source check: downloaded the exact Demailly PDF cited by the node and read printed
pages 21 and 61. Corollary (3.4) gives the locally integrable fundamental solution;
Exercise 8.5 uses partial convolution with a cutoff equal to one on a slightly
larger inner disk. The node's parameter derivative assertions are the indicated
smooth-parameter assembly, using the generic convolution proof dependency.

Validation: `scompile.py` compiled both its sandbox probe and the actual module
against the live published library, with no error or warning. The first probe
found a missing classical decidability instance for open-ball membership and a
missing `ContDiff` notation scope; both were repaired. No tests or proof search
were substituted for the required compiler check.

Earlier ending: the inherited unchanged-item rejection was from the stage-1
handoff. The current `coord/brief-stage2.md` §0 explicitly directs stage-2 workers
to continue when the node has no usable Lean record; `coord/queue.tsv` lists this
item at stage 2. This delivery preserves the accepted N9 split and only adds `lean`.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
