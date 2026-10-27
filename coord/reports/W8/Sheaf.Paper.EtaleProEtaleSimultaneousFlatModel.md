## What changed

Withdrew `Sheaf.Paper.EtaleProEtaleSimultaneousFlatModel` under brief step 8d,
and set its retained node's `lean` attachment to `null`.

The actual replacement is the already-proved canonical scalar/site comparison
`((pbcComparisonReduction T a).app K).symm` from
`Sheaf.Paper.WitnessCompatibility`. It identifies comparison of the actual étale
scalar extension with actual pro-étale scalar extension of the comparison, in the
unbounded derived category of B-module sheaves. Therefore it is B-linear and
preserves the properties transported in finite compact-support domains.

Updated Step 5, `proof_deps`, `proof_origin`, and the obsolete direct `tool_uses`
entry of `lem-sp-finite-compact-support-domains` to use this existing isomorphism.
Its quarantined source and Lean attachment are preserved unchanged. Its current
source already publicly imports `WitnessCompatibility` and has no import of the
withdrawn module. No source-library declaration or target statement changes.

Change record: `coord/changes/etale-proetale-flat-model-pruning.md`.

## Proved and sorry left

Proved 0 of the item's original 1 holes. The declaration
`AlgebraicGeometry.ProEtale.ScalarCubeFlatModel.simultaneous_flat_model` is pruned,
not claimed proved. The withdrawn module has zero remaining holes; zero holes
are added and zero statements are split off.

The unchanged quarantined parent still has its two existing holes,
`AlgebraicGeometry.ProEtale.finiteCompactSupportDomains` and
`AlgebraicGeometry.ProEtale.finiteCompactSupportDomains_comparison_isIso`
(node `lem-sp-finite-compact-support-domains`). Neither is copied, weakened,
replaced, or claimed proved by this packet.

The replacement component is checked by the isolated Lean probe
`scratchpad/ReplacementScalarSite.lean`: lcompile passed in 2.1 seconds,
with no warnings and no holes in the probe.
The replacement term is simply:

```lean
((pbcComparisonReduction T a).app K).symm
```

Its source is `(comparisonUpperStar (ModuleCat B) T).mapDerivedCategory.obj
((pbcFixedScalarExtension T.smallEtaleTopology a).obj K)`; its target is
pro-étale scalar extension of
`(comparisonUpperStar (ModuleCat A) T).mapDerivedCategory.obj K`.
This is the exact isomorphism used in the rewritten parent Step 5.

The earlier attempted full flat-model proof remains only in scratchpad, is not
validated as a complete module, and is not part of the delivery.

## No longer needed

Pruned module and node attachment:
`Sheaf.Paper.EtaleProEtaleSimultaneousFlatModel`,
`lem-sfb-etale-proetale-cube-flat-model`. There are no Lean imports or uses of its
declarations in `lean/` or `quarantine/`. An exhaustive scan of live node
`stmt_deps`, `proof_deps`, and step `uses` found only the finite compact-support
parent's Step 5, replaced in this packet. No unit or chapter references this node.
The historical split/review descriptions are retained as history.

The other historical parent,
`Sheaf.Paper.EtaleProEtaleScalarPullbackCube`, already has a complete direct mate
proof with no live edge to the flat model. Its final proof explicitly documents
that replacement. Its declaration, imports and node remain unchanged.

Withdrawal removes all imports of the item:

- `WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal`
- `Sheaf.Paper.EtaleProEtaleScalarMate`
- `Sheaf.Paper.PurEtaleScalarMateProjection`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Homology.QuasiIso`
- `Mathlib.AlgebraicGeometry.Scheme`
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
- `Sheaf.SixFunctors.RingedDerivedComparisonData`
- `Sheaf.SixFunctors.RingedDerivedCompositionComparison`
- `Sheaf.SixFunctors.RingedDerivedTwoIsoComparison`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`

These dependencies remain available wherever the rest of the library uses them;
no dependency module is withdrawn. The finite compact-support parent no longer
needs simultaneous preservation, representative invertibility, six-face
normalization, or chain-map naturality to transport its scalar-domain properties.
The existing inverse component of `pbcComparisonReduction` is exactly the needed
comparison. The scalar-six unit and the finite compact-support unit retain their
own statements and proof steps: only this auxiliary tool is replaced.

## Where the brief, the DAG or earlier work was wrong

The item remained reachable only because the finite compact-support domain proof
cited the full simultaneous flat model for a single scalar/site isomorphism.
`pbcComparisonReductionMap_isIso` already proves invertibility of the actual
canonical adjunction mate for arbitrary coefficients; `pbcComparisonReduction`
packages it as the required isomorphism. Its inverse at K supplies the parent
step without any premise on six cube faces or a chosen common representative.
This also covers zero rings, empty schemes, identity maps, nonflat coefficient
maps, and unbounded inputs, since the existing isomorphism is defined on the
whole derived category.

The archive at `quarantine/Sheaf/Paper/FiniteCompactSupportDomains.lean` was read
in full and preserved. Its absence from lean/ was not used as evidence for
withdrawal. Withdrawal rests on the actual replacement argument and live parent
updates above.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
