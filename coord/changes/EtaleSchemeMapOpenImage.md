# Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage proof environment

## Reason

The completed proof uses `CategoryTheory.Limits` names in private helpers and therefore
adds that namespace to the module's open environment. It also enables the two
proof elaboration options shown below. The declaration signatures and
public theorem statement are unchanged. This is a proof-support interface change
required by the completed proof.

## Old

```lean
open CategoryTheory Opposite
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage | S9 | Compiles the private pullback and sheaf helpers. |

The downstream query also reports the following transitive importers. None uses a
changed declaration signature or definition. They require no adaptation: public imports
and signatures are identical, and module namespace openings and proof elaboration
options do not alter their imported theorem types. The only direct importer is
`Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover`, whose proof is still
`by sorry`; there are no call sites to adapt.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineAtlasOpenCover | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.EtaleSheafSpaceAtlasBootstrap | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.InertiaFreeFiniteCoverCoarse | S9 | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.IsolatedLCICurveSmoothOpen | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.ProEtaleLocalSystemRepresentability | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable | W8 | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedLqfAffineRelationCover | T2 | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.SeparatedSpaceDimensionOneScheme | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.Paper.NormalLatticeFiniteCoverPresentation | M6 | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.Paper.NormalProEtaleMonodromy | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.Paper.TameIntegralReductionFamily | unclaimed | Signature and definition semantics unchanged; no adaptation. |
| Sheaf.SecPurity.NormalLocallyConstantFiniteSection | S8 | Signature and definition semantics unchanged; no adaptation. |

## Status

landed 20261023T124422-L-1397268 2026-10-23 (merge of deliver/S9/Sheaf.AlgebraicGeometry.EtaleSchemeMapOpenImage)
