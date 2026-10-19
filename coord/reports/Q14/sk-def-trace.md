## Worker report

The item module is `Sheaf.Paper.FourierTraceFunctions`. Its public trace dependency is
`Sheaf.Paper.WeilComplexTraceFunction`, supplied as the lean-only repair of
`def-fd-trace-function`. No natural-language statement or dependency list changes.
No new DAG node is introduced. All writes are in this item's sandbox.

Clause-by-clause correspondence for sk-def-trace:

- The finite-field and coefficient setting is the existing `WeilConjectures.FourierSetting`:
  its `field` contains p, a, q, k0 and its chosen closure; `coefficients` contains the distinct
  coefficient prime and chosen Qbar; `extension`, `finiteExtension` and `rootsOfUnity_mem`
  give the finite coefficient field E and the standing mu_p containment.
- A separated finite-type k0-scheme is `X₀ : Over (Spec (.of D.k₀))` with
  `[IsSeparated X₀.hom]`, `[LocallyOfFiniteType X₀.hom]` and `[QuasiCompact X₀.hom]`
  in the trace interface. No smoothness, connectedness, purity or dimension hypothesis is added.
- The Weil complex is `K : sfCommonStageWeilComplex D l hl X₀ Qbar`. This is the existing
  category of fixed pairs in the common-stage bounded constructible adic category, with
  its existing morphisms. It is not the discrete E-sheaf derived category and not the
  derived category of Weil sheaves. Arbitrary common-stage Weil isomorphisms are allowed.
- A finite-extension point is `(n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints X₀ n hn)`.
  Positivity is part of the cited local-operator convention: F_(q^0) is not a field.
  The point is a morphism over k0 from the canonical finite subfield of the fixed closure.
- The trace-function clause is `weilTraceFunction D l hl Qbar X₀ K n hn x` from the
  repaired dependency. Its unique-value specification says that, for EVERY finite-stage
  Weil model isomorphic to K, the value is `localExtensionTrace` included into Qbar by
  `Shrink.algEquiv` followed by `E.val.subtype`. Existence of a model is proved as part of
  that specification; it is not a hypothesis on the caller or a chosen arbitrary model.
- The displayed equality with the alternating sum is the defining expression of the
  reused `localExtensionTrace`, then `localAlternatingTrace`: `∑ᶠ j : ℤ`, with sign
  `(j.negOnePow : ℤ)`, of `LinearMap.trace` on the finite-dimensional cohomology modules.
  `localExtensionFrobenius` and `localFrobeniusCohomology` are the cited local operators.
  There is no new arbitrary endomorphism or new local-Frobenius construction.
- The classical clause is `classicalFiniteFieldFourierTransform F ψ n hn f y`.
  Both f and y have domain `F.field.extensionSubfield n hn`, exactly F_(q^n).
  It calls the EXISTING `FiniteField.fourierTransform ψ f y`, which is
  `∑ x, f x * ψ (Algebra.trace F.field.k₀ _ (x * y))`.
  `AddChar.compTrace` identifies the factor with psi_n(xy). The source's fixed
  nontrivial character is supplied as ψ; the definition of the sum itself also makes
  sense for the trivial character, just as the existing generic definition does.
  There is no inverse, normalization factor, additive sign change, or trace of f(x).

Dependency declarations read and used:

- `Sheaf.Paper.LocalFrobeniusTrace`: `localExtensionTrace`, `localAlternatingTrace`,
  `localFrobeniusOperator`, `localFrobeniusCohomology` and the extension-point/return maps.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`, `sfWeilComplex`,
  `sfWeilStageObject`, and its specified Frobenius pullback identification.
- `Sheaf.Paper.PbcQbarCategory`: the source Qbar pair-category/scalar convention;
  common-stage Weil pairs use the existing scheme-universe model of finite coefficients.
- `Sheaf.Paper.FourierSetting`: `WeilConjectures.FourierSetting`.
- `WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter`: `AddChar.compTrace`,
  `compTrace_ne_one`, `isPrimitive_compTrace`, `compTrace_compTrace`; its public Mathlib
  import gives `AddChar.FiniteField.primitiveChar` and its cyclotomic construction.
- `WeilConjectures.FourierTransform.Classical`: `FiniteField.fourierTransform`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum.extensionSubfield`, `extensionEmbedding`,
  `extensionPoints`; its unique-subfield theorem supplies the cardinality, hence the
  finite enumeration used for the classical sum. This helper changes no field data.

Edge cases checked by reading the formulas: zero complexes give zero traces; all negative
cohomological degrees are included with the correct parity; boundedness makes the sum
finite; shifts change the sign. The empty scheme has no extension-valued points, so the
trace has empty domain. n=1 uses exactly one Frobenius, via the existing positive-power
index n-1. n=0 is excluded by the source local-operator dependency. Arbitrary prime p,
including p=2, and arbitrary finite coefficient extensions, including ramified ones, are
retained. The Fourier transform of delta at zero is 1; the transform of the constant 1
is q^n delta at zero for the source's nontrivial induced character. No cardinality factor
is inverted. Site and coefficient universes are independent (`u v`) in the trace repair.

Searches (all on 2026-10-18):

- msearch leansearch, "trace function of Weil complex and finite field Fourier transform":
  eight analytic Fourier hits, no matching adic trace definition.
- msearch leanfinder, "trace function Weil complex local Frobenius alternating trace
  classical finite field Fourier transform": eight field-trace/matrix-trace hits, no match.
- msearch loogle, "FiniteField.fourierTransform, AddChar.compTrace": unknown first
  identifier; no hits. These are project declarations, not Mathlib declarations.
- msearch grep, `traceFunction|fourierTransform|compTrace`: analytic Fourier hits in
  Mathlib; no adic Weil-complex trace. Direct rg in Mathlib and upstream located the
  primitive-character construction and the upstream classical transform and older trace.
- rg `sk-def-trace` in upstream found the generic classical transform and
  `WeilComplex.traceFunction`; the latter's full docstring and formula were read, together
  with `WeilSheaf.traceFunction`. The former is reused; the latter does not expose the
  source's common-stage adic coefficient interface, and the recorded sheaf-only binding
  cannot take arbitrary complexes.
- rg `traceFunction|localFrobenius|TraceFunction|fourierTransform|FourierSetting` in
  lean/Sheaf found LocalFrobeniusTrace and FourierSetting, which are reused. Further
  searches found no common-stage trace function or names colliding with the new names.
- Read the published AddCharacter source with `scompile.py --source`: it supplies the
  complete existing trace-composition interface. Source probes for the two new module
  names reported unavailable, confirming they are not already published modules.
- Read the current main-20261015 source sections for sk-def-trace, def-fd-trace-function,
  sk-def-char and sk-def-fourier-set. They agree with the node statements used here.

The only postponed theorem is `WeilConjectures.weilTraceFunction_existsUnique`, a
well-definedness theorem owned by the definition node def-fd-trace-function. Its docstring
gives the complete finite-model descent, common-overfield comparison, conjugacy, scalar
trace invariance, bounded signed-sum argument and uniqueness. The definition chooses a
uniquely specified scalar; no data is chosen from a mere existence theorem. All definitions
have actual bodies, and no theorem is proved in this stage.

Both files compiled separately via scompile.py, including the importing module against
the private overlay of the dependency module; no errors or warnings remain.

## Dependency modules

`def-fd-trace-function`: the old record `AlgebraicGeometry.WeilSheaf.traceFunction`
accepts sheaves rather than the requested complexes. The new module
`Sheaf.Paper.WeilComplexTraceFunction` states the full common-stage trace function,
using precisely the alternating local trace of the recorded local-operator dependency.
Its named uniqueness theorem is definition well-definedness, not a new independent
mathematical input. Only this dependency node's lean field changes.

`sk-def-char`: no lean record was present. Its existing published AddCharacter module
already gives trace composition, nontriviality, primitive scalings and transitivity,
and imports the Mathlib cyclotomic primitive character. The lean-only repair records
these existing declarations; no module is written for them.

`sk-def-fourier-set`: no lean record was present and the audited older generic discrete
derived-category name is not the adic setting stated in the source. The already landed
`FourierSetting` of def-fourier-set is the required coefficient datum. The lean-only
repair reuses that declaration and its existing six-functor interpretation, without
redefining the datum or the adic category.

## Second reading by Q14

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
