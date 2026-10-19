## Worker report

The module `Sheaf.TraceFormula.ValuationMarkingSemistableSeparation` states
`AlgebraicGeometry.exists_semistableEtaModification_of_isSepClosed` with proof `sorry`.
It uses `MultipointedCurve`, `IsStrictlySemistableCurve`, `Smooth`, `Etale`,
`MultipointedCurve.Hom.IsEtaModification`, and `MultipointedCurve.IsSemistable` exactly for
the input and conclusion of the item. The valuation-ring, finite-height, separably closed,
generic-smoothness, and generic-etaleness hypotheses are each explicit. The conclusion
contains a new multipointed curve, a morphism to the input, its eta-modification property,
and semistability.

The declarations are imported from `Sheaf.AlgebraicGeometry.MultipointedCurveModification`
and `Sheaf.AlgebraicGeometry.StrictlySemistableCurve`; the valuation and separably closed
classes are imported from Mathlib. No dependency module was needed. I searched the project
and upstream source by the item id and by `semistableEtaModification`, `marking-semistable`,
and `valuation-marking`; no existing declaration states this item. I also searched Mathlib
for valuation-ring semistable modification declarations; no exact match exists.

Edge cases represented by the statement include an empty marking (the existing
`MultipointedCurve` permits it), a height-zero valuation ring, and nonseparated/nonproper
curves (the existing structures impose no such assumptions). The generic morphisms use
`V.subtype`, the canonical fraction-field map of `ValuationSubring`.

## Second reading by N9

The theorem has no extra assumptions beyond the node: `hstrict` renders strict
semistability of `Y`, `hsmooth` renders smoothness of `Y_eta`, and `hmarking` renders
étaleness of `E_eta`. The existential pair renders `(Z,F)` and its map to `(Y,E)`;
`IsEtaModification` renders the required proper pair maps, schematically dense isomorphism
opens, and generic-fibre isomorphisms, while `IsSemistable` renders nodal geometric fibres,
etale marking, and marking in the relative smooth locus. The proof is intentionally
postponed with `sorry`, as required for stage 2.
