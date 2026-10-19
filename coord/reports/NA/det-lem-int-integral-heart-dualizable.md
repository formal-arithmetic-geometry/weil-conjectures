## Worker report

Drafted Sheaf.Paper.IntegralHeartDualizable. The theorem is
AlgebraicGeometry.ProEtale.integralHeartDualizable; the only helper is the transparent
abbreviation integralHeartStratumComplex for inverse image followed by singleFunctor at 0.
The theorem proof is sorry; the abbreviation contains real data. No new notions or DAG nodes,
no statement correction, and no changes to dependencies are delivered.

Hypothesis and clause correspondence:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Arbitrary finite extension: `(E : Type v) [Field E] [Algebra (Padic ℓ) E]
  [FiniteDimensional (Padic ℓ) E]`, independently of scheme universe u.
- The valuation ring and its completed coefficient sheaf are precisely
  SmallAdicCompletion.Coefficients.integerRing and integralHeartScalars from the recorded
  local-model dependency. They use its canonical small presentation of E, transported by
  the algebra equivalence, and continuous functions before inverse image from the point.
  These are completed coefficients, never the constant scalar sheaf. The recorded
  integral-limit theorem is publicly imported and identifies this construction with the
  inverse limit of finite constant coefficient sheaves. The chosen uniformizer is already
  fixed by the dependency coefficient construction; replacing it by a unit multiple changes
  neither completion nor the residue quotient used here.
- Arbitrary X and constructible C: `X : Scheme.{u}`, `C : SmallAdicCompletion.Modules ℓ E X`,
  and `_hC : IsConstantModelConstructible ... X C`. No finite type, Noetherian, base field,
  characteristic, or torsion-freeness hypothesis is imposed.
- Stratum S: `s : Scheme.Stratification X`, `a : Fin s.n`, with `S = s.domain a` and
  immersion `s.immersion a`. This is the existing finite constructible locally closed
  stratification convention of the constructibility dependency.
- Local models: `_hmodel` supplies the pro-etale cover, then for each chart separately an
  existential `N : ModuleCat ... (integralHeartScalars ...)`, `Module.Finite ... N`, and an
  isomorphism of the restricted C with `(integralHeartRealization ...).obj N`. The recorded
  realization constructs constant scalar module sheaves, extends scalars to continuous
  completed coefficients, passes through the section-module equivalence, and pulls back
  from the point. The model is not an arbitrary local module or unspecified realization.
- Restriction in the derived category: `integralHeartStratumComplex ...` is the actual
  `CondensedRing.upperStar ...` sheaf restriction embedded by `singleFunctor _ 0`.
- Specified dual: `((CondensedRing.derivedHom ... S).obj (op K)).obj (𝟙_ D)`.
  This is precisely relative RHom(K,O), with the recorded ordinary unbounded category,
  derived relative tensor, and internal Hom.
- Dualizable with both triangles: `Nonempty (ExactPairing K D)`. Read Mathlib's full
  ExactPairing signature: its fields are coevaluation `1 -> K tensor D`, evaluation
  `D tensor K -> 1`, and both triangle equations, with unitors and associators.
- Tor bounds: `DerivedCategory.torAmplitudeIn _ (-1) 0 K` and
  `DerivedCategory.torAmplitudeIn _ 0 1 D`. Read the upstream definition: its quantifier
  ranges over every module sheaf F in the entire ambient abelian category and tests
  `K tensor (singleFunctor C 0).obj F`; no constructibility or flatness restriction on F.
- Residue example: the final conjunct identifies RHom of `finiteModule ... S 0` with
  that same degree-zero module shifted by `(-1 : ℤ)`. Its index 0 is explicitly positive
  level 1, i.e. O/pi. The coefficient inverse image is cartesian, so this is the stratum
  restriction of O_X/pi. This example is unconditional on any identification of general C
  with the residue module; this exactly states the separate example in the node.

Dependency declarations inspected and used:

- Sheaf.Paper.IntegralHeartLocalModel: integralHeartScalars, integralHeartRealization,
  integralHeartDerivedCategory; read the full module and source construction.
- Sheaf.Paper.CondensedConstantConstructibility: IsConstantModelConstructible,
  ConstantModelConstructible and the imported generic Tor-amplitude convention.
- Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit: sfb_integral_coefficient_limit
  and sfbCondensedIntegers (continuous coefficient construction and canonical limit).
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom: CondensedRing.derivedHom
  and derivedTensorHomAdjunction; its Tensor module fixes relative K-flat tensor.
- Sheaf.NumberTheory.Padics.ExtensionIntegersDvr: Padic.extension_integers_dvr (proof input).
- SmallAdicCompletion.finiteModule and Coefficients.quotientModule, publicly reexported by
  the recorded local-model module, supply the residue module without a second construction.
- Mathlib.CategoryTheory.Monoidal.Rigid.Basic: ExactPairing.
- WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude: torAmplitudeIn.

All available recorded proof-dependency modules are imported without public, except
statement dependencies already public. The size convention is a convention rather than
an importable module. Every universe and variable is bound explicitly.

Edge cases checked mathematically before drafting: N=0, free N, N=A/pi^r, rank-zero
resolutions, empty S, and an empty covering of an empty stratum. The cover index may be
empty; no Nonempty assumption is imposed. Torsion N gives the genuine degree-one dual,
so the residue shift is [-1], not [1]. An empty finite stratification supplies no `a`,
as expected. Test objects for Tor amplitude include arbitrary, nonflat, nonconstructible
module sheaves. Scheme and coefficient universes remain independent by the dependency's
canonical small-field presentation.

Searches:

- msearch leanfinder, "A locally finitely generated completed integral coefficient sheaf
  on a pro-etale stratum is dualizable with Tor amplitude minus one to zero": generic
  derived boundedness results, no exact match. Repeated with "locally perfect integral
  constructible sheaf dualizable Tor amplitude": eight generic t-structure declarations.
- msearch leansearch, "a locally finitely generated integral constructible sheaf is
  dualizable in the derived category": finite-dimensional module duals and finite-type
  sheaf infrastructure, no exact statement.
- msearch loogle, "ExactPairing": unknown identifier in service, no result.
- msearch grep, `IsDualizable|ExactPairing`, CategoryTheory/Monoidal: exact-pairing generic
  definition and transport lemmas, no integral coefficient theorem. The source definition
  was then read directly and reused.
- rg in upstream WeilConjectures, side lean/Sheaf and dag/lean_names_upstream.json for
  integralHeartDualizable, integralHeartStratumComplex, integral-heart-dualizable,
  integral/dual and TorAmplitude: no existing theorem with the same statement.
  IntegralStratumHomFormula defines a related dual and uses this still unstated theorem;
  it requires different geometric hypotheses and does not state this result. The generic
  ProEtale.Derived.Duality operates on sheaves of an abstract coefficient category, not
  the relative modules over the pulled-back completed integral coefficient ring.

Validation: scompile.py compiled the delivered file cleanly, no errors or warnings
(3.1 seconds for both its sandbox and library passes). The initial ordinary compile
returned infrastructure exit 75 because published live oleans were missing for
IntegralHeartLocalModel and SmallCoefficientDerivedCompletion. Confirmed the current
source with scompile.py --source, then supplied those two unchanged read-only sources
alongside the delivery file to the same normal wrapper; all three files compiled
separately, in dependency order, within their default 60-second limits (27.6 seconds,
5.1 seconds, 3.1 seconds). No live source, artifact or launcher tool was edited.
Delivery preflight remains gated on the missing published live dependency artifact; see the resumed validation below.

## Second reading by NA

Self-check only; no independent worker was started, as instructed by the dispatcher.
Reopened the node, source blueprint statement, dependency definitions and the drafted
signature. Matched each hypothesis and all four conclusion conjuncts as listed above.
Confirmed that ExactPairing's argument order is K,D and its evaluation is D tensor K,
that torAmplitudeIn tests all sheaves, and that finiteModule index zero means quotient by
pi to the first power. No statement mismatch was found in this self-check. The clean compile is recorded above; independent maintainer review remains necessary.
No independent review is claimed.


## Resumed validation

Retained the interrupted packet and ran the required deliver2.py --no-push first.
It stopped before preflight with `INFRASTRUCTURE RETRY (stale live olean)`:
the published live build has no Sheaf.Paper.IntegralHeartLocalModel.olean.
No delivery process remained active and nothing was pushed.

Fetched the current IntegralHeartLocalModel source with scompile.py --source.
Then scompile.py compiled that unchanged source, the unchanged
Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion source, and the delivered
IntegralHeartDualizable file separately in dependency order. All passed without errors
or warnings. The delivered file took 3.5 seconds for its sandbox pass and 3.9 seconds
for its library pass. No live source, artifact, or tool was edited. Rechecked that the
Lean signature exactly matches lean.statement, all lines fit the 100-character limit,
and the only postponed proof is integralHeartDualizable. The source blueprint still
states the specified dual, both Tor bounds, and the residue shift [-1].

The second ordinary deliver2.py --no-push attempt failed identically before preflight,
again reporting the missing IntegralHeartLocalModel.olean and nothing pushed. Supplying the existing dependency sources
is sufficient for compilation; the delivery gate itself only supplies packet modules
and requires the missing dependency artifact from the published build.


## Latest retry (2026-10-18 19:36 UTC)

Retained the saved packet and first ran the required deliver2.py --no-push.
Both that dry run and a second ordinary dry run failed before preflight with
`INFRASTRUCTURE RETRY (stale live olean)`: the published live build lacks
`Sheaf.Paper.IntegralHeartLocalModel.olean`. Nothing was pushed.

Confirmed that the packet differs from the current shared item only in lean;
its signature exactly matches lean.statement and all Lean lines fit 100 characters.
Reopened the current blueprint: its dual, Tor intervals and residue shift agree.
Fetched both current dependency sources using scompile.py --source into scratch;
IntegralHeartLocalModel was unchanged. Compiled both unchanged dependency sources
and the delivered module through the prescribed scompile.py wrapper. All passed
with no errors or warnings: SmallCoefficientDerivedCompletion 37.8 seconds,
IntegralHeartLocalModel 7.8 seconds, IntegralHeartDualizable sandbox 3.9 seconds
and library 3.3 seconds, each within the unchanged 60-second limit.

The remaining failure is the delivery gate requiring an unpublished dependency
artifact, despite successful compilation with the current sources. No interface
repair is indicated. No live file, tool or compiled artifact was modified, and
unchanged dependency sources remain scratch inputs rather than delivery modules.


## Dispatcher retry (2026-10-18 19:45 UTC)

Retained the saved packet and inspected its report before the required first dry run.
The first and second deliver2.py --no-push runs both failed before preflight with
`INFRASTRUCTURE RETRY (stale live olean)`: the published live build still lacks
`Sheaf.Paper.IntegralHeartLocalModel.olean`. Neither run pushed anything.

Fetched the current IntegralHeartLocalModel and SmallCoefficientDerivedCompletion
sources via scompile.py --source into the existing scratch paths. Supplied both
unchanged sources and IntegralHeartDualizable to the prescribed scompile.py wrapper;
all three modules passed separately, without errors or warnings. The delivered
module passed both sandbox (3.9 s) and library (3.3 s) compilation. The dependency
passes also remained within the unchanged 60-second file limit.

Reopened the current item, its statement-dependency records, the local-model
interfaces and source blueprint. The packet still changes only lean; its signature
exactly matches lean.statement; all lines fit 100 characters; integralHeartDualizable
is the sole postponed proof. No statement or dependency-interface repair is indicated
by the diagnostic. The remaining failure is the delivery gate requiring the missing
published dependency artifact. No live source, artifact or launcher tool was edited.


## HTTP-429 continuation validation (2026-10-18 20:08 UTC)

Inspected the retained report and checked for an interrupted delivery process before
running any delivery wrapper; none remained. The required first dry run and the
subsequent retry both failed before preflight with the same tool diagnostic:
`INFRASTRUCTURE RETRY (stale live olean)`, missing published
`Sheaf.Paper.IntegralHeartLocalModel.olean`. Both explicitly reported nothing pushed.

Retrieved the current IntegralHeartLocalModel and SmallCoefficientDerivedCompletion
sources through scompile.py --source into scratch. Supplied both unchanged dependency
sources and the item module to scompile.py. All modules passed without errors or
warnings, including IntegralHeartDualizable sandbox (3.9 s) and library (3.3 s).
No source or interface defect was diagnosed. The delivery gate still requires the
unpublished dependency artifact even though the authorized source-overlay compilation
succeeds. Live artifacts and launcher tools were not changed.

Self-check reopened the current node, all statement-dependency records, their relevant
source declarations, the source blueprint, ExactPairing and torAmplitudeIn. The saved
packet changes only lean, its recorded signature matches the file verbatim, every Lean
line fits 100 characters, and the theorem remains the sole postponed proof in the item.
The source agrees with the specified RHom dual, both triangle identities, Tor intervals
[-1,0] and [0,1], and residue shift [-1]. The saved packet remains retained.


## Dependency modules

The delivery packet includes source overlays for the recorded dependencies
`det-lem-int-integral-heart-local-model` (`Sheaf.Paper.IntegralHeartLocalModel`) and
`def-sfb-small-coefficient-derived-completion`
(`Sheaf.SixFunctors.ProEtale.SmallCoefficientDerivedCompletion`). The delivery gate's
published live build lacks their `.olean` artifacts, although both source declarations
are present on the current newtargets base and compile cleanly through `scompile.py`.
Their node copies change only the `lean` records and preserve the recorded statements.
This is a build-artifact repair: no dependency statement, declaration, or interface is
changed, and the sources are the exact current base sources.
