# Remove the obsolete warning option from the specified pullback comparison

## Status

landed 20261021T170728-L-2755019 2026-10-21 (merge of deliver/H1/Sheaf.Paper.SpecifiedPullbackComparisonAlpha)

Module: `Sheaf.Paper.SpecifiedPullbackComparisonAlpha`, held by H1.

## Reason

The returned delivery at `737fd1e48` was rejected by the landing hole
scanner at the file-level warning option. The scanner recognizes the `sorry`
component of the dotted option name as an unattributed hole. The theorem has a
complete proof, so this warning suppression is unnecessary.

## Old

The module contained `set_option warn.sorry false` following
`set_option autoImplicit false`.

## New

Remove that warning-suppression command. Retain every other option,
the full theorem signature, all public imports, and the completed theorem proof
of the returned packet. The packet's private proof import pruning and revised DAG
proof are unchanged from that packet. No other module is edited.

## Users

No declaration, instance, notation, or public import changes.
Removing a warning option changes diagnostic suppression only; it changes no
mathematical definition or theorem statement. Options set while elaborating this
module are not new declarations exported to its importers. In particular, the
existential completeness witness in the theorem remains proof-valued, so its
consumer's choice is unchanged by proof irrelevance.

`tools/downstream.py` reports these 13 downstream modules, all of which retain
the same available declarations and statements and require no adaptation:

- `Sheaf.EtaleCohomology.Purity.RealSheaves.RealSemisimplification`
- `Sheaf.Paper.AdicLocalCharacteristicFactor`
- `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy`
- `Sheaf.Paper.FourierArtinSchreierProperties`
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`
- `Sheaf.Paper.IsomorphismScalarAugmentationCone`
- `Sheaf.Paper.IsomorphismScalarComparisonAgreement`
- `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality`
- `Sheaf.Paper.LocalWeilModelTraceIndependence`
- `Sheaf.Paper.PointAutomorphismTransportScalarExtension`
- `Sheaf.Paper.PullbackIdentitiesScalarExtension`
- `Sheaf.Paper.RealWeights`
- `Sheaf.SixFunctors.FrobeniusPointTransportNatural`

The sole external textual user of `specifiedPullbackComparisonAlpha` is
`Sheaf.Paper.IsomorphismScalarComparisonAgreement`, whose statement uses its
completeness witness via `.choose`. Its hypotheses, conclusion, and the type of
that witness stay identical. The other downstream modules import the same API.
No target definition or target statement changes.

Validation: the repaired item compiles through `lcompile.py` without diagnostics
(exit 0, 17.1 seconds). The source hole scanner reports one named theorem, no hole
markers, and no warnings. The signature and public imports match the current
repository exactly. The delivery tool performs the packet preflight; the global
build remains the maintainer's verification of downstream compiled modules.
