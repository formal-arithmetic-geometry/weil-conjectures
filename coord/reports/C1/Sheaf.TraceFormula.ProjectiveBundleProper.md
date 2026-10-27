## What changed

Added `Sheaf.TraceFormula.CanonicalRelativeProjProper` with the strictly smaller
intermediate theorem `AlgebraicGeometry.canonicalRelativeProj_proper`. Proved
`AlgebraicGeometry.projectiveBundle_proper` from it by unpacking the presentation,
using properness of closed immersions, and composing proper morphisms. Updated the
item node's proof, proof dependencies and proof origin to match this argument.

For the return at head `0395fb4fd`, removed the `warn.sorry` option from both
modules. The ledger was treating the option name as an unattributed hole. The
ledger now reports precisely one hole, in the named intermediate theorem.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.projectiveBundle_proper`.
Added one hole in `AlgebraicGeometry.canonicalRelativeProj_proper`, node
`lem-trf-canonical-relative-proj-proper`. The item has zero holes and the new
module has one. This is a decomposition: one hole closed, one added, net zero.
The new theorem treats only the canonical projection; the item's proof supplies
the closed immersion, composition and factorization equality.

## No longer needed

Removed these unused direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle`
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic`
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`

Removed the unused public imports of
`Sheaf.AlgebraicGeometry.ProjectiveBundleAffinePresentations` and
`Sheaf.AlgebraicGeometry.GloballyGeneratedProjectiveBundle` from the new module;
they are not needed by its statement.

The affine-presentation, quotient-geometry and target-locality nodes remain
needed by the split theorem. No module is withdrawn. The item's assembly no
longer needs the separate closed-immersion base-change argument: the global
projection is proper before composition with the original closed immersion.
Its closed-immersion and composition facts come from
`lem-kun-projective-implies-proper`.

## Where the brief, the DAG or earlier work was wrong

The previous packet left an option name that the hole ledger counted as an
unattributed hole. This repair removes that option; it does not hide a proof hole.
The original mathematical plan remains valid. Its local relative-Proj argument
is retained in the new intermediate node rather than completed here. The previous
packet also omitted the item node's proof-route update; that is included now.
The new node now records the three actual Mathlib searches. Their returned
properness instances concern absolute Proj over an affine target.

## New nodes

`lem-trf-canonical-relative-proj-proper`, in
`dag/nodes/sec-trace-formula/lem-trf-canonical-relative-proj-proper.json`, states
properness of the canonical relative projective-bundle projection. Its proof plan
uses affine finite-generator presentations, their open-base identification, local
H-projective properness and target-locality. The statement includes the zero
module and empty-base cases: empty Proj and morphisms over the empty base are
proper, so neither a nonzero module nor a nonempty base is required.

## Related modules compiled before delivery

26 related module(s) compiled against this delivery by deliver3.py: 26 OK.

```json
{"capped": false, "direct": 26, "left_out": 0, "own": {"Sheaf.TraceFormula.CanonicalRelativeProjProper": "b2edbcb81c7463844d03fa0a048a5b519b74d99f", "Sheaf.TraceFormula.ProjectiveBundleProper": "46fdef3147eb7510d9badd84c2307c9e38ae34cd"}, "results": {"Sheaf.AlgebraicGeometry.AbelianLevelCoarseModuli": {"hash": "ca2f8d992d44542bc617127f563aea4ca1b63f6a", "status": "OK"}, "Sheaf.AlgebraicGeometry.ArithmeticStableIsomFinite": {"hash": "9706adaf7727686754ef866425472a854471b1cb", "status": "OK"}, "Sheaf.AlgebraicGeometry.ArithmeticStableOpenBounded": {"hash": "d8dcdc3e3ef7c93e84ab31ba78d02328491f5328", "status": "OK"}, "Sheaf.AlgebraicGeometry.EquivariantLogSmoothFanRegularization": {"hash": "3fbe94af829faae9e9076ab172c99546811eb6b7", "status": "OK"}, "Sheaf.AlgebraicGeometry.EquivariantNodalSmoothPairResolution": {"hash": "b7b7a41a039bb1a74b2f7e0b025ddf6fec7ab7f7", "status": "OK"}, "Sheaf.AlgebraicGeometry.FiniteConstantProjectiveGraph": {"hash": "1fb8221b080b313ea2ee7380cc3c3abfcf570427", "status": "OK"}, "Sheaf.AlgebraicGeometry.GabberLogBlowupRegularization": {"hash": "69f9cf247c9649ef9415164959f45f51a453fce0", "status": "OK"}, "Sheaf.AlgebraicGeometry.InvariantNormalizedBlowupDomination": {"hash": "311937d2a2edae3c3a99cc361c534ccd5a475872", "status": "OK"}, "Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve": {"hash": "4ad347613cf6da2f7534e08f1ac401f498a11e99", "status": "OK"}, "Sheaf.AlgebraicGeometry.LogCanonicalDeletionAlgebra": {"hash": "acbcdd50e00896b736073d4e8a8fef53e743261a", "status": "OK"}, "Sheaf.AlgebraicGeometry.NodalBirationalBaseChangeGeometry": {"hash": "7fdb73af2204cec1fdd18ffe24c93dea7a50c565", "status": "OK"}, "Sheaf.AlgebraicGeometry.NodalMultidegreeZeroLocus": {"hash": "4eb4597fb77bb80ff6c93363043db7199bfbf7c8", "status": "OK"}, "Sheaf.AlgebraicGeometry.NormalizedBlowupTowerEtaleDescent": {"hash": "98e2c25837c9381faada95956d4398246c853ae7", "status": "OK"}, "Sheaf.AlgebraicGeometry.ProjectiveBundleComposition": {"hash": "71f0c55f2db0fbe8e487f35a56ee0193805b4a17", "status": "OK"}, "Sheaf.AlgebraicGeometry.ProjectiveBundleFiberHomLift": {"hash": "23a37a54142b6a7eae18a6057e39650188f6b5d9", "status": "OK"}, "Sheaf.AlgebraicGeometry.ProjectiveBundleFiberIsoSpread": {"hash": "b3ba74a1c04a7adc622322d8c73dc3eabea53815", "status": "OK"}, "Sheaf.AlgebraicGeometry.ProjectiveBundleRelativeAmple": {"hash": "9ca15767e748ecc1ae6ec21c3d8854be7829d540", "status": "OK"}, "Sheaf.AlgebraicGeometry.QuasiSplitTowerSmoothResolution": {"hash": "65b51a28edfd4a0f1ebc84420af756a03cf530bf", "status": "OK"}, "Sheaf.AlgebraicGeometry.RelativeAbelNonspecialChart": {"hash": "4aa5e409791bce87affadddd185095d836b4fa40", "status": "OK"}, "Sheaf.AlgebraicGeometry.RelativeDegreeGMinusOneTheta": {"hash": "12322d005e45aee0a7e07cc051e0bdcd10fcc984", "status": "OK"}, "Sheaf.AlgebraicGeometry.RelativeSectionImageFlatFP": {"hash": "b3e70d8e156c5cf174191cdf36f8cd91b2d9e5de", "status": "OK"}, "Sheaf.AlgebraicGeometry.SectionIdealProjExpansion": {"hash": "897e2fdd52ebf97dace5b243b93e7aa8046f6e89", "status": "OK"}, "Sheaf.AlgebraicGeometry.SmoothProjectiveCurveCohomologyLocalSystem": {"hash": "b14b5c605428e38642a7ac716c6c12f9604d673b", "status": "OK"}, "Sheaf.AlgebraicGeometry.StableCurveFramedTraitSmoothing": {"hash": "42c6a82d4425c81bf2ac5229d5c48805896c1a3a", "status": "OK"}, "Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids": {"hash": "1f1ca98bc70a1951db2d562579ad119819efc7fe", "status": "OK"}, "Sheaf.SixFunctors.TraceFormula.DeJongArbitraryBaseMarkedSemistable": {"hash": "43e79022f369393022915df99ef76b5ee9c3771a", "status": "OK"}}, "seconds": 111, "time": "2026-10-28T02:07:34+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
