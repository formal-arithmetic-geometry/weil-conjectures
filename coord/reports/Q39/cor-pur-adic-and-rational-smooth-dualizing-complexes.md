## Worker report

The delivery states the corollary on the actual complete finite-Tor constructible integral
category, its recorded rational localization, and its recorded common-stage algebraically
closed coefficient category. The module supplies the missing canonical unit-specialization
interfaces; it does not replace these categories by constant-coefficient derived categories.

The integral identification is `existsUnique_integralIdentification` and its uniquely
specified choice `integralIdentification`. `rationalIdentification` and
`closedIdentification` are literal coefficient transports of this inverse purity map.
The main theorem asserts integral finite-trace normalization and both transported counit
equations. Every definition has real data; postponed assertions are named theorems with
source and proof docstrings. The selected comparisons are uniquely determined by displayed
root, scalar-unit, identity, tensor and shift formulas. `EtalePowerPresentation` bundles
the complete recursive tensor normalization in its type. The uniqueness theorem fixes
its entire data before `etalePowerComparison` selects it; no arbitrary line isomorphism
is chosen. Each successor factor is heterogeneously equal to its actual published
tensor, shift, flat-single, or sheaf-power comparison. Heterogeneous equality merely
transports the endpoints between their existing presentations.

Hypothesis and clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed purity conventions | `P : PurityFiniteSetting.{u}`; its finite-field datum, coefficient prime and closure are reused |
| Finite extension E and O_E | `P.extension`, the recorded valuation-ring and completed coefficient sheaves |
| X over Spec k | `X : Scheme.{u}` with `X.Over (Spec (.of P.field.k))` |
| a_X separated finite type | `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on `X ↘ Spec (.of P.field.k)` |
| Smooth pure dimension d | `d : ℕ`, `SmoothOfRelativeDimension d` on the same structure morphism |
| The actual constructible exceptional adjunction | `S : ConstructibleExceptionalCoefficients.System ...`; `operation` selects its normalized operation at the recorded Nagata compactification |
| Completed coefficient unit | `integralTwist ... 0`, the regular completed module in degree zero with its canonical zero-shift presentation |
| Lambda_X(d)[2d] | `integralTwist ... d`: the existing positive root-line tensor power, its genuine single complex, and shift `2 * (d : ℤ)` |
| omega = Ra_X^! Lambda | `(operation ... (.integral ...)).G.obj` at the completed unit; analogously at rational and closed stages |
| Canonical integral identification | `existsUnique_integralIdentification`, determined by `IsNormalizedIntegralIntegration` |
| Inverse of integral purity | The orientation of `integralIdentification` is exceptional pullback to shifted Tate unit; its docstring follows the source reconstruction and inversion |
| E purity transported from integral purity | `rationalIdentification`, using the recorded exceptional comparison `b.symm` and the same rationalization functor |
| Qbar purity by common-stage descent | `modelEmbedding`, `modelScalar`, and `closedIdentification`, using the actual small coefficient model and common-stage inclusion |
| Counit is normalized integration | `integralCounitAmbient` has finite reductions prescribed by `finiteIntegration`; the main theorem gives the rational and closed counit equations |
| Normalized finite trace | `finiteIntegration` uses the published coordinate-counit-normalized `diagonalDualizingObject`, its inverse, and the actual exceptional counit |
| Canonical quotient and twist identifications | `lineProjection` is fixed on every completed scalar and root tensor; `rootComparison` is fixed by `IsFiniteTateSiteComparison`; the tensor/shift comparison is explicit |
| RΓ_c -> Lambda | The counit maps are in the recorded coefficient category over Spec k. The existing compact-support realization and coefficient-point fibre give exactly the ordinary compact-cohomology presentation |

`S` is presentation data for the recorded canonical operations, not an additional geometric
condition or an arbitrary exceptional map. The existing `exists_system` provides such a
system for every separated finite-type morphism in the standing setting. Its left
realizations, coefficient q maps, and unit/counit equations remain in force. The statement
is valid for every such normalized presentation, hence is independent of the presentation.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`.
- `Sheaf.Paper.IntrinsicCoefficientTwists`, `Sheaf.Paper.PbcCoefficientTwists`:
  `coefficientTwistPower`, `finiteCoefficientTwist`, the existing integral Tate line and
  the recorded coefficient categories.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.System`, `C`, `Stage`, `rationalization`,
  `rationalScalar`, `commonField`, `commonInclusion`, and normalized field/common comparisons.
- `Sheaf.Paper.FiniteTateSiteDescent` (existing declaration owner): `finiteTateProSheaf`,
  `finiteTateProPowerGenerator`, and `IsFiniteTateSiteComparison`. The corollary uses
  these existing definitions through the new definition-node record with `existing: true`.
  It does not use `finite_tate_site_descent` in its signature.
- `Sheaf.Paper.PurityDiagonalDualizingObject`: `diagonalDualizingObject`, whose normalization
  is the coordinate Kummer counit. This is reexported by the imported smooth-trace module.
- `Sheaf.Paper.SmoothTrace`: the existing coefficient-unit and finite exceptional-counit
  interfaces; the delivered finite integration keeps the published normalized orientation.
- `Sheaf.Paper.BoundedConstructibleTower`: `pbcDerivedExtend`, `pbcRestrict`, and the uniquely
  tensor-unit-normalized `pbcDerivedScalarAdjunction`.
- `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`: actual proper/open `image`,
  `finiteImageIso`, coefficient `projection`, `reduction`, and canonical scalar comparison.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`: reexports the recorded ordinary compact
  cohomology and coefficient-point constructions.
- The upstream Adic/Rational reconstruction declarations and Reduction/Normalization
  declarations are imported for the source proof. Their signatures were read. The first
  two alone are partial reconstruction/transport statements, so neither is claimed as an
  existing match for this full corollary.

Edge cases checked: d = 0 uses the coefficient unit and identity shift, not a positive-power
induction hypothesis; the empty scheme is permitted and no nonempty cover is assumed;
all quotient levels are n+1, so no zero quotient is introduced; all positive uniformizer
levels are retained without a ramification-divisibility assumption; negative shifts use
`2 * (d : ℤ)` with the standard cohomological convention; the Qbar small field model uses
`Shrink.algEquiv`, with no site/coefficient universe equality. No integration is asserted
to be an isomorphism for arbitrary X and no affine-space fundamental class is posited on X.

Searches for an existing exact statement:

- `msearch.py ... leanfinder "adic rational smooth dualizing complex purity counit normalized integration"`:
  unrelated period-ring/formal-smoothness results; no exact declaration.
- `msearch.py ... loogle "dualizingComplex, twistShift"`: no match; unknown queried name.
- `msearch.py ... grep "dualizing|upperShriek|TateTwist" AlgebraicGeometry`: no Mathlib match.
- `msearch.py ... leansearch "dualizing complex smooth scheme adic rational coefficients purity counit trace"`:
  unrelated pseudofunctor and field-trace results; no exact match.
- `rg` of upstream `WeilConjectures` for the node id and smooth/adic/rational dualizing
  terminology: the published finite trace and partial adic/rational reconstruction steps
  were found and read; none states this corollary with its three coefficient and normalized
  counit clauses.
- `rg` of `lean/Sheaf`: found finite diagonal orientation, detailed twists, ordinary compact
  cohomology, the canonical finite Tate site descent, and the normalized constructible
  exceptional coefficient system. Those definitions and comparisons are reused.
- The source blueprint corollary and its proof were read in the current main-20261015
  snapshot. The old reconstruction declarations were not treated as the full modern node.

There is no statement correction and no disputed mathematical assertion. The corollary's
Lean declarations, signatures and bodies are retained. Its public import now names
the live module that owns the required finite Tate definitions. The elaboration-only
transparency settings described below keep compilation within the fixed limit.

## Repair of immutable head 84cf5d8f9059

The required first dry run of the saved packet passed as `c8afd22cc7`. The independent
return nevertheless identified a real duplicate-declaration defect in that extraction.
I compared all twelve extracted definitions with the current main source and read the
live source through `scompile.py --source Sheaf.Paper.FiniteTateSiteDescent`. Every
signature and body is identical after changing only the blueprint docstring tag.

The corollary now publicly imports `Sheaf.Paper.FiniteTateSiteDescent` and reuses those
existing declarations. The new definition node records that existing module with
`existing: true` and no `file`. Both extracted/replacement modules have been removed
from this delivery, as has the dependency-node rewrite. The descent lemma and its live
module are not changed. No declaration is renamed. The corollary keeps its definition
node as statement dependency, rather than making its statement depend on the colocated
descent theorem. The retained diagonal theorem is still used through its actual chosen
`diagonalDualizingObject`.

The missing unit-specialization helpers belong to the corollary and remain listed in
its `lean.declarations`. `exactSingleShiftIso` composes the existing exact-functor
shift and single-complex comparisons. `IsScalarUnitRealization` records equality on
every scalar-unit section. `structureIsOver` is the base-field triangle, a Prop-valued
instance stated as a named theorem with proof `sorry` and a proof docstring (`Spec.map_id`,
then the right identity law), registered by `attribute [instance]` (reviewer fix).

## New nodes

`def-pur-finite-tate-site-comparison` records the twelve existing definitions in
`Sheaf.Paper.FiniteTateSiteDescent`, using `existing: true`. It introduces no Lean
module or declaration. The sources are Stacks 03PK (unit-valued roots), 03EK
(sectionwise tensor and sheafification), and 099R/0GLZ (comparison adjunction and
test-object restriction). This definition node records conventions only, and makes
no existence, uniqueness, invertibility or descent assertion. The existing descent
lemma node states such assertions rather than the independent definition of these
predicates. This retains the definition-node ownership requested in the preceding
H12/H13 return while satisfying the present instruction to import and reuse.

| Hypothesis or clause | Lean |
| --- | --- |
| Prime and finite extension | `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, `[FiniteDimensional ℚ_[l] E]` |
| Positive quotient level | `n : ℕ`; `finiteTateCoefficient` is the existing quotient at `n + 1`, lifted to `u + 1` |
| Arbitrary scheme and root limit | `T : Scheme.{u}`; `purTwistZlOne` is the existing `limit (proEtaleRootsOfUnityTower ...)` |
| Fixed constant scalar encoding | `finiteTateConstantRestriction` uses the canonical constant-ring comparison and `constantRingModuleRestriction` |
| Prescribed pro-etale twist | `finiteTateProSheaf` is the restriction of `finiteCoefficientTwist ... (a : ℤ)` |
| Pure pro-etale generators | `finiteTateProGenerator` applies the coefficient-extension sheafification unit to the root tensor; `finiteTateProPowerGenerator` recurses with the scalar in the first factor |
| General etale coefficients and exponent | `A : Type (u + 1)`, `[CommRing A]`, `m : ℕ`, `hA : (m : A) = 0` |
| Pure etale generators | `finiteTateEtalePowerGenerator` uses `finiteEtaleTateOneGenerator` and the existing sheaf tensor comparison |
| Underlying finite root unit | `finiteTateEtaleRootValue` uses `kernel.ι` into `gmSheaf` and removes only `ULift`/additive notation |
| Underlying root-limit projection | `finiteTateLimitRootValue` uses `limit.π ... (op r)` and `proEtaleRootsOfUnityInclusion` |
| Site comparison predicate | `IsFiniteTateSiteComparison` quantifies over all `U`, `W`, `f`, `a`, `z`, `x`, and uses the actual comparison adjunction unit followed by restriction along `f.op` |
| Etale pullback predicate | `IsFiniteTateEtalePullback` fixes the adjunct on root tuples on the actual scheme fibre product |
| Pro-etale pullback predicate | `IsFiniteTateProPullback` fixes the adjunct when every root projection agrees with scheme pullback |
| Exponent-transition predicate | `IsFiniteTateEtaleTransition` uses exactly the power `l ^ (r' - r)`; the predicate itself permits arbitrary natural `r,r'` |
| Zero power and empty tuple | Both generator recursions at zero return the scalar-unit section; every predicate quantifies over `Fin 0` without excluding it |
| No extra geometric assumptions | No invertibility, nonemptiness, flatness, or ramification-divisibility binder in these definitions |


The original search records remain in `mathlib_searches`: LeanSearch and LeanFinder
returned unrelated algebra/site facts; Mathlib and upstream grep found no match;
the side-library search found exactly these declarations in the existing descent
module. That positive result is now used by the `existing: true` binding. A further
source comparison confirms the equality of all twelve bodies and signatures; no
new search for a different mathematical notion is needed for this import repair.

## Second reading by Q39

I reopened the corollary node and module, the new definition node, the current main
finite-descent module and its node, and the live source returned by the wrapper.
The twelve compared definitions have identical bodies, explicit universes and
parameters. The table above matches each convention to its existing declaration,
including tensor power zero, empty root tuples, arbitrary test objects and arbitrary
schemes. The corollary's hypothesis/clause table remains valid: no geometric binder,
coefficient category, normalization equation or canonical transport changes. The public import and elaboration-only transparency settings change. The new node's recorded signature is verbatim from the
existing definition, and its declaration list contains precisely the twelve reused
names. There is no duplicate declaration or replacement descent theorem in this
packet. The original corollary proof docstrings, `sorry` proofs and real definition
data are retained. This is the required worker self-check; the dispatcher prohibits
starting another agent and assigns independent review to the maintainer.

## Compile validation

The first import-only repair timed out locally and in server confirmation at the
unchanged 60-second limit. A profiler scratch compile showed repeated unfolding
of derived-functor compositions during definitional equality checks. The module
now respects transparency by default, with the former permissive setting scoped
only to `existsUnique_rootComparison` and `finiteIntegration`, where coefficient
and identity-morphism instance transport needs it. This changes no signature,
definition body or mathematical normalization. The scratch probes are not delivered.

The repaired `scompile.py` run passed without errors or warnings: sandbox 46.9 s,
actual library path 54.7 s. The one remaining module is compiled in both forms
against the existing finite-descent module. Recorded signatures, explicit universes,
JSON formatting, all twelve existing declaration names and Lean line widths were
checked again. The final preflight is run through `deliver2.py --no-push`.


## Repair of immutable head a678344eb21b

The returned arithmetic helper `WeilConjectures.AdicSmoothDualizing.twiceSucc`
duplicated `WeilConjectures.PurityFiniteSetting.frameDegreeNext` in
`Sheaf.Paper.PurityFrameClass`. I read the existing module, namespace, preceding
binders and docstring, and confirmed its live source with `scompile.py --source`.
Both signatures have exactly the sole binder `(d : ℕ)` and conclusion
`2 * (d : ℤ) + 2 = 2 * ((d + 1 : ℕ) : ℤ)`; neither depends on a purity setting,
a scheme, a coefficient ring or a universe. There is no binder-dependent distinction.

The duplicate theorem and its docstring are deleted. The corollary module publicly
imports `Sheaf.Paper.PurityFrameClass` and its `EtalePowerPresentation.normalized`
field now uses `PurityFiniteSetting.frameDegreeNext d` directly, including inside
the `congrArg` passed to `eqToIso`. The proof explanation names that existing
theorem too. The item's `lean.declarations` no longer lists `twiceSucc`.
No replacement alias or duplicate arithmetic declaration is introduced.

For the required self-check I reopened the saved node, source corollary, delivered
module and existing frame theorem. The hypothesis and clause table in the worker
report still applies verbatim: the fixed setting, separated finite-type smooth
structure morphism, dimension d, completed integral unit, rational and closed
coefficient transports, and all three counit-normalization clauses are retained.
The only equality proof used to align the successor shift is now the existing
one. At d = 0 it still reads `0 + 2 = 2`; arbitrary d, the empty scheme and the
zero-power unit presentation are unaffected. All universes and binders remain
explicit. The current shared branch has the existing frame module and no landed
corollary module; wrapper delivery bookkeeping rebases the saved packet on the
current main branch. The rest of the retained packet is not rewritten.


The repaired module passed `scompile.py` with no errors or warnings: sandbox
29.2 seconds and actual library path 30.6 seconds, both under the unchanged
60-second limit. The main signature is still verbatim in `lean.statement`,
all 48 remaining listed declarations occur in the file, and its longest line
is 96 characters. The final dry run and delivery use the prescribed wrappers.


The required initial saved-packet dry run reported a stale
`lean.declarations` entry for the removed `twiceSucc`: it had staged the old
node while reading the module after the repair. The repaired node removes
that entry. A fresh dry run now checks the consistent repaired packet;
there is no attempt to bypass the declaration-list diagnostic.


## Reviewer fix (maintainer review of 28b4f446f9c8)

1. `structureIsOver` was delivered a third time as an instance with a proof term.
   `Hom.IsOver` is a Prop-valued class, so that term is a local proof, which stage 2 does
   not allow (H6). The reviews of 84cf5d8f9059 and a678344eb21b made the same fix, and
   this re-delivery was rebuilt from the unfixed packet. It is restored as
   `theorem structureIsOver ... := by sorry` with a proof docstring, plus
   `attribute [instance] structureIsOver`.
2. Compile margin: the a678344eb21b reviewer fix, which this head also dropped, is
   re-applied. In `finitePowerComparison` and `finiteIntegration`, the non-instance local
   `let`s (`F`, `E`, `a`, `Q`) are inlined. The terms are equal after zeta reduction, and no
   signature, type or mathematical content changes.
3. This head's own repair is kept unchanged: `twiceSucc` is removed, and the module imports
   `Sheaf.Paper.PurityFrameClass` and uses `PurityFiniteSetting.frameDegreeNext`.
   The fixed module compiles clean through `nt_compile.py --json` against the local side
   overlay, in 48 s and 29.6 s at load ~80.
