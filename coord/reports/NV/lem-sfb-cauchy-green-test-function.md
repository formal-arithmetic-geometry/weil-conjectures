## Worker report

The module `Sheaf.Analysis.Complex.CauchyGreenTestFunction` states
`Complex.cauchyGreen_test_function`, with one postponed proof and no definitions.
The item's statement and dependencies are unchanged. No new or dependency modules
are needed. Every variable is explicitly bound; there are no universe parameters.

Clause-by-clause correspondence:

- The standard fields R and C are Mathlib `ℝ` and `ℂ`, with their `Field`
  instances, realizing the sole statement dependency `def-weil-field` and its
  `mathlib_match` `Field` (`Mathlib.Algebra.Field.Defs`). I read its full class
  signature and docstring: it extends `CommRing K` and `DivisionRing K`.
- Planar Lebesgue measure is `volume` on `ℂ`, from
  `Mathlib.MeasureTheory.Measure.Lebesgue.Complex`. Its measurable equivalence
  with `ℝ × ℝ` preserves product volume; there is no normalization factor.
- The specified kernel is the literal expression
  `fun w : ℂ ↦ 1 / ((Real.pi : ℂ) * w)`. Away from zero it is exactly
  `1/(πw)`; at zero Mathlib's total division gives `1/0 = 0`. There is no new
  definition of a kernel or differential operator.
- Local integrability is the first conjunct `LocallyIntegrable ... volume`.
  I read `MeasureTheory.LocallyIntegrable` and `locallyIntegrable_iff` in
  `Mathlib.MeasureTheory.Function.LocallyIntegrable`: on `ℂ` this is equivalent
  to `IntegrableOn` on every compact set. Complex integrability is absolute
  integrability of the norm, with almost everywhere strong measurability.
- Every test function is bound by `∀ (u : ℂ → ℂ)`; real smoothness is
  `ContDiff ℝ ∞ u`. In particular it does not assume holomorphicity.
- Compactness of the closure of the nonzero locus is `HasCompactSupport u`.
  I read the support definitions in `Mathlib.Topology.Algebra.Support`:
  `tsupport` is the closure of `Function.support` and compact support is its
  compactness. Empty support is included.
- `∀ z : ℂ` has no restriction to the support or to its complement.
- The antiholomorphic derivative is written inline as
  `(fderiv ℝ u ζ 1 + I * fderiv ℝ u ζ I) / 2`. The real derivative applied to
  `1` and `I` is the x and y coordinate partial, respectively. Its full
  signature and docstring in `Mathlib.Analysis.Calculus.FDeriv.Defs` were read.
  This agrees with the coordinate derivative in the recorded annulus lemma
  and the existing cutoff transform module; no duplicate operator is introduced.
- Absolute convergence is `Integrable (fun ζ : ℂ ↦ k(z-ζ) * dbar(u)(ζ)) volume`,
  with both expressions expanded literally in the delivered signature.
- The next conjunct is exactly the reproduction identity, with that same
  integrand and the conclusion `= u z`.
- The immaterial pole value is explicit: every `F : ℂ → ℂ` agreeing with the
  displayed integrand for all `ζ ≠ z` is integrable and has integral `u z`.
  Its value at `z` is unconstrained. This just expresses the node's last
  sentence, since planar Lebesgue measure of a singleton is zero.

Proof dependency interfaces read and imported:

- `Sheaf.Analysis.Complex.CauchyGreenAnnulusFormula`,
  `Complex.cauchyGreen_annulus_formula`: read the full signature and proof
  docstring. It uses real coordinate `HasDerivAt` hypotheses, an open annulus
  neighborhood, and counterclockwise circles. Imported privately for stage 3.
- `Mathlib.MeasureTheory.Function.L1Space.Integrable`,
  `MeasureTheory.Integrable.mono'`, and
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`,
  `MeasureTheory.norm_integral_le_of_norm_le`, as recorded by
  `lem-sfb-integrable-majorant-estimate`. Read their full signatures;
  the former is transitively imported and the latter directly imported.
- `Mathlib.Analysis.SpecialFunctions.PolarCoord`,
  `Complex.lintegral_comp_polarCoord_symm` and
  `Complex.integral_comp_polarCoord_symm`, as recorded by
  `lem-sfb-planar-polar-integration`. Read their full signatures and the
  coordinate source, target, inverse and volume conventions. Imported privately.

Edge cases checked mathematically before writing:

- `u = 0` (empty support): the real derivative and displayed integral vanish;
  an arbitrary value at the exceptional singleton still contributes zero.
- `z = 0`, or `z` on or inside the support: no division-by-zero side condition
  is added; the pole is assigned zero and the `1/r` norm is locally integrable
  in two real dimensions.
- `z` outside the support: the theorem still quantifies over it and concludes
  the integral is zero; the support restriction is only on `u`.
- The kernel is not claimed globally integrable. Local integrability is
  independent of the subsequent quantification over test functions.
- The test function can have nonzero antiholomorphic derivative; using real
  rather than complex smoothness retains the actual content of the formula.
- The sign and normalization agree with the source: in Demailly (3.2), choose
  a disk containing both `z` and the compact support in its interior, so the
  boundary term vanishes. Negating the denominator `ζ-z` to `z-ζ` removes the
  minus sign; the measure is dx dy and the coefficient is exactly `1/π`.

Sources checked: the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`
provides the containing unit, not this analytic lemma. The item's specified
source was successfully opened online:
https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf,
I §3.A, formulas (3.1), (3.2), Corollary (3.4), printed pp.20–21.
The local node's old WANTED note is not changed. No statement fault or
STATEMENT-DISPUTED finding remains.

Searches made (all msearch calls use group NV and this item):

- `leanfinder`, query `Cauchy Green reproduction compactly supported smooth
  functions integral antiholomorphic derivative one over pi z`: eight hits,
  including `Complex.circleTransformDeriv`, `Complex.circleTransform`, the real
  rectangle boundary formulas, and holomorphic Cauchy circle formulas.
  None is the compact-support area reproduction statement.
- `loogle`, query `fderiv, HasCompactSupport, integral`: zero hits, with
  `unknown identifier 'integral'`; this unqualified-name failure was repaired
  by the next qualified query.
- `loogle`, query `ContDiff, MeasureTheory.Integrable`: eleven hits, principally
  smoothness and decay of Fourier transforms. No reproduction identity.
- `grep`, query `Cauchy.?Green|Cauchy.?Pompeiu|wirtinger|antiholo` in `Analysis`:
  four hits, all in `Mathlib/Analysis/Complex/Conformal.lean`, about conformal
  antiholomorphic functions; none is this theorem.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `cauchyGreen|CauchyGreen|cauchyKernel|Wirtinger|wirtinger|barDeriv|antiholomorphicDeriv|lem-sfb-cauchy-green-test-function`:
  found the annulus formula, a citation in `CutoffCauchyTransform`, and
  Wirtinger coordinate operators for higher-dimensional Hermitian charts.
  Read the first two modules and the latter operators. None states this node;
  the one-coordinate expression is written inline with Mathlib `fderiv`, as
  the cutoff transform already does. No separate derivative notion is created.
- `rg` for `cauchyGreen_test_function|cauchy_green_test_function|cauchyGreen_reproduction`
  in `dag/lean_names_upstream.json`, `lean/Sheaf`, `lean/WeilConjectures`:
  no existing declaration. The item-id search of the upstream source likewise
  found no implementation.

Validation: `scompile.py NV lem-sfb-cauchy-green-test-function` compiled the
sandbox and library module cleanly (35.7 s and 2.5 s, respectively), with no
warnings or errors. All Lean lines are at most 83 characters. The node's
`lean.statement` is extracted verbatim from `theorem` to the final `:=`.

## Second reading by NV

I reread the node and completed module clause by clause after the first clean
compile. This is a worker self-check, not an independent second agent review:
the dispatch brief forbids starting agents and assigns the independent review
to the maintainer. The standard field and planar measure, zero-valued kernel
at zero, local integrability, real smoothness, compact support, unrestricted
point `z`, the plus sign and factor `1/2` in the derivative, the factor `1/π`,
absolute convergence, reproduction, and arbitrary pole replacement all match.
There is no bound on the support added to the statement, no holomorphicity
assumption, and no claim of global integrability of the kernel. No mismatch
or subsequent signature change was found.
