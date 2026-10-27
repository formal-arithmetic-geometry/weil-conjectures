## What changed

Proved `AlgebraicGeometry.ProEtale.internal_integral_residue_criterion` from the existing
Stacks criterion and two separate coefficient comparisons. Its statement and all public
imports stay unchanged. The new completion and residue comparisons are separate parts
of the original argument, with no constructibility hypothesis on the integral complex.
Neither repeats the integral criterion.

Proved the new `AlgebraicGeometry.ProEtale.integral_constant_local_tor` completely.
This generalizes the proved PID argument in `PadicConstantLocalModelTor` from Type-0
coefficient rings to the actual Type-u integer ring. The private helpers prove
constant-to-continuous flatness by torsion-freeness and the local equational criterion;
then the existing finite scalar presentation and cover-descent arguments give [-1,0].
The existing stratified and cohomology-interval theorems now prove the entire second
conjunct, including its zero/empty and possibly reversed bound cases.

Instance removals used during elaboration are scoped to the individual theorem, and
the auxiliary fixed-universe instances are local. They do not change importer instance
search.

The main proof transports boundedness and homology constructibility through the canonical
point coefficient isomorphism before applying `integral_models_stacks`. All new proof-only
imports are private. No existing definition or declaration signature was changed, and no
other group's module was adapted.

## Proved and sorry left

Closed the original one hole in
`AlgebraicGeometry.ProEtale.internal_integral_residue_criterion`, by decomposition into
two strictly smaller coefficient comparisons and a complete integral finite-Tor proof.

New proved theorem (zero holes):
`AlgebraicGeometry.ProEtale.integral_constant_local_tor`
(`lem-sfb-integral-constant-local-tor`).

Two new holes, each exactly one public theorem with `:= by sorry`:

- `AlgebraicGeometry.ProEtale.internal_completion_stacks_comparison`
  (`lem-sfb-internal-completion-stacks-comparison`): identify actual Roos completeness
  with constant scalar completeness, with no residue constructibility claim.
- `AlgebraicGeometry.ProEtale.internal_residue_stacks_comparison`
  (`lem-sfb-internal-residue-stacks-comparison`): compare the two first-residue
  constructibility/Tor predicates, with no completeness or integral constructibility claim.

Thus the item has zero holes left; this packet adds two holes and closes one original
hole. This is a decomposition, not a net hole reduction. Existing imported holes are
unchanged. The complete DVR Tor proof adds no hole.

## No longer needed

Removed direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`: the item uses the separately
  stated actual-completion comparison; this module remains a dependency below that step.
- `Sheaf.Paper.IntegralLfpConstantModelComparison`: no lfp-versus-constant
  conversion is needed for the local Tor argument, which starts with finite constant models.
- `Sheaf.Paper.FiniteCoefficientModelComparison`: finite residue transport
  is isolated in its own step, where this dependency remains needed.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`: moved to the proved local Tor module.

The old direct proof dependencies
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`det-prop-integral-criterion-constant-coefficients`,
`lem-pe-finite-coefficient-model-comparison`, and
`lem-weil-l-adic-extension-integers-dvr` are now recorded below the relevant comparison or
local Tor step, not as unused global mathematics. The direct lfp dependency
`lem-sfb-integral-lfp-constant-model-comparison` is unnecessary for this route. It may
still be imported transitively by existing coefficient realization/heart-closure modules;
no claim is made that its whole module can be withdrawn. No module is deleted or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The declared dependencies do not themselves identify the actual `IsDerivedComplete`
Roos augmentation with the Stacks small-site completeness predicate, nor do they state
an unconditional comparison with the actual `derivedReduction` at index zero. Existing
`completion_transport` uses the ordinary Scheme adic-completeness predicate, while
`residue_transport` assumes that completeness and concludes an etale-origin predicate.
Their signatures cannot directly supply these two steps for arbitrary K.

The original local Tor plan can be completed using already proved scalar PID,
stratified and bounded-cohomology devissage results. Only the coefficient-universe
specialization of the scalar flatness proof needed to be supplied. The proved stratified and cohomology Tor-interval lemmas, and the PID proof helpers,
are used as generic tools from the coefficient/localizing-closure units; they do not
replace a step of the adic unit route. No statement was
found false; empty schemes, zero models, torsion scalar modules and unbounded inputs
to the comparison statements were checked mathematically.

## New nodes

`lem-sfb-internal-completion-stacks-comparison`: the actual augmentation/completeness
comparison, a proper part of step 1 of the original node; one new hole.

`lem-sfb-internal-residue-stacks-comparison`: the flat common-quotient first-residue
comparison, a proper part of step 2; one new hole.

`lem-sfb-integral-constant-local-tor`: the fully proved local DVR Tor interval,
separating the arithmetic/scalar argument from stratified and bounded-complex devissage.

All three have separate new modules, source citations, proof text, search records and
Lean attachments. The original node's proof and proof dependencies follow the new proof.
There are no statement/definition change records because existing interfaces are unchanged.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
