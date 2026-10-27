## Worker report

The module `Sheaf.Analysis.FixedSupportFourierLipschitz` states
`MeasureTheory.fixed_support_fourier_bounds_lipschitz`. Its sole proof is `sorry`;
there are no new definitions, auxiliary theorems, or statement corrections.

Source read: Demailly, Differential and pseudodifferential operators on manifolds,
§2, Lemma 2.7 proof, printed pp.5–6, at
https://www-fourier.univ-grenoble-alpes.fr/~demailly/analytic_geometry_2019/pseudodiff.pdf.
The source uses the kernel `exp (-2πi x·ξ)` and compact support to control Fourier
transforms of bounded families. The node explicitly specializes this argument
using the first spatial moment and scalar Cauchy–Schwarz. The theorem follows
that node, rather than imposing smoothness on `u` or proving the general
distributional derivative assertion of the source.

Hypothesis and conclusion correspondence:

- The fields are Mathlib's `ℝ` and `ℂ`; the statement dependency
  `def-weil-field` is the Mathlib leaf `Field`, in
  `Mathlib.Algebra.Field.Defs`. Its full signature and its extension of
  `CommRing` and `DivisionRing` were read. No extra field parameter is needed.
- `m : ℕ` and `hm : 1 ≤ m` give the stated positive integral dimension;
  `EuclideanSpace ℝ (Fin m)` has the Euclidean norm, real inner product,
  topology, and standard Lebesgue `volume`, rather than the supremum norm
  on an unadorned function type.
- `K : Set (EuclideanSpace ℝ (Fin m))` and `hK : IsCompact K` are precisely
  the fixed compact subset.
- `u : EuclideanSpace ℝ (Fin m) → ℂ`, `hu : MemLp u 2 volume` encode the
  measurable square-integrable function. `MemLp` is the existing conjunction
  of `AEStronglyMeasurable` and a finite extended Lp norm. For the separable
  complex target, a.e. strong measurability is equivalent to measurability
  for the Lebesgue completion: see
  `aestronglyMeasurable_iff_nullMeasurable_separable`. Thus arbitrary null-set
  modifications are allowed; Borel measurability is not imposed.
  `MeasureTheory.memLp_two_iff_integrable_sq_norm` identifies the finite-norm
  condition with `Integrable (fun x ↦ ‖u x‖ ^ 2) volume`. Both definitions and
  that full signature were read. The displayed L2 norm is written explicitly
  as `Real.sqrt (∫ x, ‖u x‖ ^ 2)` throughout.
- `hsupport : ∀ᵐ x ∂volume, x ∉ K → u x = 0` is exactly support almost
  everywhere in K, with no pointwise restriction.
- `volume K ≠ ⊤` gives finiteness of v; `IntegrableOn (fun x ↦ ‖x‖ ^ 2) K volume`
  gives finiteness of the second spatial moment defining b. Consequently
  `Real.sqrt (volume K).toReal` and `Real.sqrt (∫ x in K, ‖x‖ ^ 2)` are the
  stated real constants. Integrability of this continuous nonnegative
  function is equivalent to its finite integral on K.
- `Integrable u volume` is the L1 conclusion.
- The next quantified conjunct states `Integrable` of the explicit complex
  exponential Fourier integrand for every frequency: absolute convergence
  is stated, not inferred from the totalized integral alone.
- Mathlib's function Fourier transform `𝓕 u` is the h in the node.
  `Real.instFourierTransform`, `Real.fourier_eq`, and `Real.fourier_eq'` were
  read in `Mathlib.Analysis.Fourier.FourierTransform`: the latter gives exactly
  `exp ((↑(-2 * π * ⟪x, ξ⟫) : ℂ) * I) • u x`. On ℂ scalar multiplication
  is multiplication, agreeing with our explicit integrability conjunct.
- The following two conjuncts are the two pointwise inequalities with exactly
  `sqrt v ‖u‖₂` and `2π b ‖u‖₂ ‖ξ - η‖` on their right sides.
- `Continuous (𝓕 u)` states the explicit continuity conclusion.
- The final conjunct quantifies over `I : Type w` in an arbitrary explicitly
  declared universe, a family `f`, and `M : NNReal`. Its three premises require
  each member to be L2, to vanish a.e. off this same K, and to have L2 norm at
  most M. Its two conclusions give every member the common bound `sqrt v M`
  and the common Lipschitz constant `2π b M`, expressed directly by the global
  difference inequality. A finite real nonnegative bound is precisely the
  stated boundedness condition. Empty and arbitrary-size families are included.

Proof-dependency interfaces read and imported (including transitive imports):

- `lem-sfb-continuous-on-compact-integrable` is the Mathlib leaf
  `ContinuousOn.integrableOn_compact`,
  `Mathlib.MeasureTheory.Function.LocallyIntegrable` (direct proof import).
- `lem-sfb-real-l2-hilbert-pairing` records `MeasureTheory.L2.innerProductSpace`,
  `MeasureTheory.L2.inner_def`, `MeasureTheory.L2.integrable_inner` in
  `Mathlib.MeasureTheory.Function.L2Space` (direct public import),
  `MeasureTheory.Lp.instCompleteSpace` in
  `Mathlib.MeasureTheory.Function.LpSpace.Complete`, and `norm_inner_le_norm`
  in `Mathlib.Analysis.InnerProductSpace.Basic`. All signatures were read;
  the latter modules are included by L2Space.
- `lem-sfb-integrable-majorant-estimate` records `MeasureTheory.Integrable.mono'`
  in `Mathlib.MeasureTheory.Function.L1Space.Integrable`; the integral bound is
  `MeasureTheory.norm_integral_le_of_norm_le` in
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`, both included by FourierTransform.
- `lem-sfb-complex-phase-exponential-bound` records
  `Real.norm_exp_I_mul_ofReal_sub_one_le` in
  `Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds` (direct proof import),
  `Complex.norm_exp_I_mul_ofReal` in `Mathlib.Analysis.Complex.Trigonometric`,
  and `Complex.exp_add` in `Mathlib.Analysis.Complex.Exponential` (included).
- `lem-sfb-bochner-integral-subtraction` records `MeasureTheory.integral_sub`
  and `MeasureTheory.integral_congr_ae` in
  `Mathlib.MeasureTheory.Integral.Bochner.Basic` (included). Their full signatures,
  and those of the majorant and phase declarations, were read.

Edge cases checked mathematically before writing: K empty or measure zero forces
u = 0 almost everywhere, so all integrals and bounds are zero, while pointwise
values on null sets remain unrestricted. The zero function and M = 0 satisfy
all conclusions. If the spatial moment vanishes, the difference estimate forces
a constant Fourier integral as it should. Frequency zero and equal frequencies
are allowed. Dimension m = 1 is included; m = 0 is excluded exactly by the node.
No nonemptiness, interior, smoothness, or origin-centered support assumption is
imposed on K. An empty family has vacuous common bounds.

Searches made with the prescribed msearch.py wrapper:

- leanfinder: "Fourier integral of compactly supported square integrable function
  is bounded and Lipschitz with constants measure support and first spatial moment"
  returned eight hits, including `VectorFourier.norm_fourierIntegral_le_integral_norm`,
  `VectorFourier.fourierIntegral_convergent_iff`, and derivative estimates. None
  states the fixed-support L2 bounds and explicit global Lipschitz constant.
- loogle: `"fourier", "Lipschitz"` returned zero hits.
- grep in Analysis/Fourier: `fourier.*[Ll]ipschitz|[Ll]ipschitz.*fourier|norm_fourier_le_integral_norm`
  returned zero hits.
- leansearch: "Fourier integral of compactly supported L2 function has uniform
  bound and global Lipschitz constant controlled by L2 norm" returned eight hits:
  L1 Fourier bounds, Plancherel results, and Fourier differentiability under an
  integrable first-moment assumption. None is the node's statement.
- rg across `lean/WeilConjectures` and `lean/Sheaf` for Fourier/Lipschitz,
  fixed-support/Fourier, and the exact blueprint id found only a proof-plan
  mention in `Sheaf.Analysis.EuclideanFixedSupportRellich`, not a declaration.
  Searching these trees, Mathlib, and `dag/lean_names_upstream.json` for the
  proposed declaration name found no clash. The DAG search found this node
  and its supporting chain, with no other declaration for this theorem.

Validation: scompile.py compiled both its sandbox form and the actual library
module cleanly (2.9 s / 2.8 s), with no errors or warnings. The first attempt's
notation issue was repaired by spelling the nonnegative-real type `NNReal`.
All variables and the family-index universe are bound explicitly, and
`autoImplicit` is false. No node fault or STATEMENT-DISPUTED concern remains.

## Second reading by Q134

Final self-check against the open node and module: `MemLp` bundles exactly the
Lebesgue-measurable L2 premise, the a.e. support implication matches the node,
and each conjunct corresponds in order to finite volume, finite spatial moment,
L1 membership, absolute Fourier convergence, the two estimates, continuity,
and the uniform family assertion. In particular the finite L2 integral is not
asserted merely by an inequality involving a totalized real integral: it follows
from `hu`. No hypothesis or constant was changed. The only compiler repair
replaced unavailable notation by `NNReal`. This is a self-check; the dispatcher's
independent maintainer review remains the independent reading. No other agent
was started, as instructed.
