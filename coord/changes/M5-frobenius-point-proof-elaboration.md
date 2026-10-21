## Reason

Make the section and derived localization proofs elaborate predictably without
expanding the entire constant-sheaf, completed-coefficient or intrinsic-pullback construction.
The static checker classifies attribute commands as interface changes, so this record
makes their scope and users explicit.

## Old

The item had no local reduction attributes or local suppression of the generic
GrothendieckTopology.hasSheafify_of_essentiallySmall instance. All existing theorem
signatures, public imports and both SigmaDerived definitions were as they are now.

## New

Inside a section, disable the generic hasSheafify_of_essentiallySmall instance while
checking the proofs against the specialized project instances. Locally mark constantSheaf,
completedIntegralCoefficientSheafUnrestricted, HasDerivedCategory.standard and
sfIntrinsicPullback irreducible, so elaboration uses their APIs. The section ends before
the namespace ends. These are local proof-elaboration choices and do not change any
existing statement, definition, instance declaration or public import. Added private
helpers are all proved. A new public statement in a new module isolates coefficient
passage and is recorded by its own DAG node.

## Users

No changed public declaration signature or definition is used by a consumer. The
attribute commands are scoped to the proof section and are restored at its end.
No consumer adaptation is required; target statement meanings remain unchanged.
For review, the direct importers of the item in the current shared source are:

- `Sheaf.Paper.A1FiniteEtaleWeilFibreComparison`.
- `Sheaf.Paper.A1LisseSectionsStalkEvaluation`.
- `Sheaf.Paper.AdicLocalFrobeniusModelConjugacy`.
- `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence`.
- `Sheaf.Paper.DlConstantFieldCharts`.
- `Sheaf.Paper.FixedPairTruncationCohomology`.
- `Sheaf.Paper.FourierArtinSchreierProperties`.
- `Sheaf.Paper.LocalFrobeniusConjugacyClass`.
- `Sheaf.Paper.LocalFrobeniusTransportNormalization`.
- `Sheaf.Paper.LocalFrobeniusWeilMorphismNaturality`.
- `Sheaf.Paper.LocalWeilModelTraceIndependence`.
- `Sheaf.Paper.ProperCoincidenceFrobenius`.
- `Sheaf.Paper.ProperSectionsSemilinearGerms`.
- `Sheaf.Paper.RationalStalkExact`.
- `Sheaf.Paper.WeilPullbackLocalFrobenius`.
- `Sheaf.Paper.WeilTateTwistFrobenius`.
- `Sheaf.Paper.ZlImmersionWeilLocalBehavior`.
- `Sheaf.SixFunctors.FrobeniusCohomologyTransportIso`.
- `Sheaf.TraceFormula.CompactFrobeniusTransportComposition`.

## Status

landed 20261021T214839-L-1868477 2026-10-21 (merge of deliver/M5/Sheaf.SixFunctors.FrobeniusPointTransportNatural)
