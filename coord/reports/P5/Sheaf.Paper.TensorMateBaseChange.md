## What changed

Proved `AlgebraicGeometry.ProEtale.tensorMateBaseChange` in
`Sheaf.Paper.TensorMateBaseChange`, with exactly its existing signature and definitions.
The first conjunct uses the proved source-library fixed-scalar pro-etale pullback APIs:
`constructibleFiniteTor_leftDerivedFunctor_upperStar_obj` and
`torAmplitudeIn_leftDerivedUpperStar`. They already allow arbitrary morphisms.
The coefficient-unit normalization is definitional.

The tensor equation applies `Adjunction.projectionTensorMap_mateEquiv` to the actual etale
compact-support projection/exchange square
`Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`. Three fully proved private
helpers specialize to the coefficient unit and insert the canonical left unitor.
They generalize the existing private calculation in
`Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange` from a chosen pullback to an arbitrary
`IsPullback` square. Applying the comparison functor to that equality proves the final
conjunct, for every retained origin. The calculation proves it even without the
constructibility premise; the public theorem retains that premise.

Added private imports of the source-library `LocalizationFiniteTor`,
`LowerShriekProjectionExchange` and `UpperStarMonoidal.Unit` modules. The helpers use the
canonical etale universe model and braiding instances. The two backward-definitional-equality
transparency options are disabled while elaborating these helpers, then restored before the
original public declarations: this lets Lean recognize the explicit derived tensor as the
monoidal tensor and infer the component projection-formula instances.

Updated the existing node's proof, proof dependencies and proof origin to this shorter route,
and removed obsolete tool-use approvals. No source-library file is changed. The unit
`sk-prop-cohsm` route is retained: this is still the projection/exchange counit-mate argument
required in its arbitrary-base-change step.

Validation: `lcompile.py` compiled the complete module cleanly in 31.1 seconds. Import-direction
checks passed for all three new proof imports. The delivery checks compile the final version
with the axiom probe. All existing public signatures and definition bodies are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.tensorMateBaseChange`
(node `lem-pur-tensor-mate-base-change`).

All three added private helpers are completely proved:
`AlgebraicGeometry.Etale.unit_tensor_base_change`,
`AlgebraicGeometry.Etale.exceptional_tensor_base_change`, and
`AlgebraicGeometry.Etale.dualizing_tensor_base_change`.

Actual textual holes remaining in the item: **0**. Holes added: **0**. Split-off theorems: **0**.
This is a proof, not a decomposition into new sorry statements.

## No longer needed

Removed all 16 old private proof imports:

- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.ComparisonTorAmplitude`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.AlgebraicGeometry.EtaleStalkTorTest`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.FiniteCoefficientTensorCtf`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Sheaf.Paper.CanonicalFiniteLevelCompactSupportBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`
- `Sheaf.AlgebraicGeometry.CompactificationProjectionExchangeCoherence`
- `Sheaf.Paper.FiniteSiteCounitProjectionTransport`
- `Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The old node's additional proof dependencies are no longer needed by this proof:

- `lem-sf-proetale-constructible-origin`
- `lem-sf-comparison-tor-amplitude`
- `prop-weil-pbc-inverse-image-modules-exact`
- `prop-constructible-pullback`
- `lem-sf-etale-stalk-tor-test`
- `lem-weil-pbc-comparison-pullback`
- `def-weil-exceptional-inverse-image`
- `lem-sf-tensor-ctf`
- `thm-sf-ambient-adjoint-class`
- `lem-kun-dimension-finite-type`
- `thm-cbc-finite-level-proetale`
- `lem-weil-pbc-transport-identifies-exchange`
- `lem-cbc-proetale-extension-zero-comparison`
- `lem-pur-co-smooth-pf-exchange-coherence`
- `lem-pur-finite-site-counit-projection-transport`
- `lem-weil-finite-compact-projection-formula`
- `def-weil-derived-pullback-tensor-hom`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`

The fixed-scalar definition already supplies an etale origin, and the upstream pro-etale
pullback API preserves its interval directly. Thus no reconstruction through intrinsic
coefficient presentations or separate stalk test is necessary. Likewise the specified maps
are written as comparison images of the etale maps, so the already proved etale
projection/exchange square and abstract mate calculation prove their equality before applying
comparison. Separate pro-etale exceptional-class Hom bijections, dimension bounds, tensor
closure, compactification-exchange comparison and site-counit transport are unnecessary here.
All twelve obsolete top-level `tool_uses` entries are removed for these reasons.

These are dependencies pruned from this item, not a claim that their modules have no other
users or that existing source declarations may be deleted. Existing public statement imports
continue to provide their recorded API.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically valid but longer than needed for the actual fixed-scalar
comparison-coordinate statement. Its stage-2 review already notes the unit clause is `rfl`.
The source library now provides arbitrary pro-etale pullback preservation, and the abstract
projection-tensor mate theorem together with the etale projection/exchange square handles
all remaining map algebra. None of theta, the exceptional base-change map, or beta is cancelled.
No smoothness, separatedness of g, or invertibility of these three maps is introduced.

The first compilation attempts exposed the concrete/generic monoidal-instance elaboration
issue documented upstream in `TensorStructure` and `UpperShriekCanonicalMapsCoherence`.
Local instance choices plus the local transparency options resolve it; no definition,
statement or global option was changed. Edge cases include zero complexes, empty schemes,
identity squares, and proper/open f; the reused preservation and abstract mate arguments
require no nonzero or smoothness hypothesis.

## Second reading by P5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
