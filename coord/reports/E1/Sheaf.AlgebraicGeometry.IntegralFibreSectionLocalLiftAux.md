## What changed

Completed the listed zero-hole retirement of
Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux, removing its duplicate
AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison via deleted.txt.
Its node, lem-sbc-integral-strict-local-fibre-comparison, now attaches to the existing
WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux theorem, with its
exact full-model signature. The node's statement_change records the canonical change
of presentation, audits the sole current DAG citer, and retains the mathematical
comparison as a dependency. The proof steps now describe the adopted full-model proof.

The listed old consumer Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLift has already
been retired. Its current realization,
WeilConjectures.AlgebraicGeometry.IntegralFibreSectionLocalLift, privately imports the
adopted comparison and combines it with full-model qcqs continuity. Its explicit proof
obtains e and b, extracts a representative of e.inv (b.inv t) from the filtered module
stalk colimit, and combines he and hb to identify its restriction with t. This is the
replacement argument already present in the library. Neither adopted module needs
adaptation; their source text, signatures, public imports and proofs remain verbatim.
No Lean source under WeilConjectures is delivered.

The canonical smallStrictHenselizationColimitIso and
smallStrictHenselizationColimitIso_toBase identify the former small colimit and structure
map with the adopted full model. Thus the theorem retains the same mathematical meaning,
including the representative restriction formula, all schemes, coefficient universe,
integrality, and arbitrary algebraically closed geometric field. It still asserts no
neighbourhood representative existence; that remains the parent's separate continuity
argument. No target statement or definition changes. The unit sk-lem-universal-datum
has empty realized statement and step lists; its route is unchanged.

Change record: coord/changes/E1-integral-fibre-section-local-lift-aux-retirement.md.

## Proved and sorry left

Actual initial item hole count: 0. Holes closed by declaration: none (0 of 0).
Holes added: none. Split-off statements: none. No sorry remains in the retired item,
and no new Lean declaration is introduced. The adopted
AlgebraicGeometry.Etale.exists_integralStrictLocalFibreComparison and its consumer
AlgebraicGeometry.Etale.integralFibreSection_localLift were already proved.

Verification: unchanged sandbox copies of both adopted modules compiled together through
lcompile.py in 3.8 and 2.4 seconds, exit code 0, with no warnings. An explicit axiom probe
imports both modules because the parent's import of the comparison is private.
Both declarations use only propext, Classical.choice and Quot.sound.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux.
No replacement duplicate, transport wrapper, helper module or new node is created.
No consumer import edit is needed: rg over lean/Sheaf, lean/WeilConjectures and quarantine
finds no remaining importer of the retired copy, and tools/downstream.py reports zero
downstream modules. This census is reconciled with the current parent node: its adopted
module already imports and applies the correct full-model twin.

The withdrawn module's public imports were GeometricFibreExchangeGerms and
QcqsStrictLocalModuleComparison under WeilConjectures, and EtaleUnitSectionRestriction
and SmallStrictLocalSectionMaps under Sheaf. Its private imports were
Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility,
Sheaf.Paper.StrictHenselizationPointedMap,
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison, and
WeilConjectures.AlgebraicGeometry.IntegralStrictHenselianGeometricFibreSections.
These imports disappear with the copy. The upstream proof keeps its own required imports
unchanged; no claim is made that other users of these modules can be pruned.

The adopted proof needs neither the small-model closed-fibre comparison node
lem-weil-pbc-strict-henselization-small-closed-fiber-comparison nor the direct graph
calculation nodes lem-weil-pbc-etale-unit-section-restriction-comp and
def-weil-pbc-small-strict-local-section-maps. It uses the adopted singleton-fibre theorem
lem-weil-pbc-strict-henselization-closed-fiber and the adopted compatibility theorem
lem-sbc-strict-local-fibre-restriction-compatibility instead. The old proof's direct
lem-sbc-geometric-fibre-exchange-germs edge is unnecessary; its section map is already
part of the statement's imported interface. No DAG node is deleted, and nodes needed
through the adopted proof or other consumers remain needed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed module, but the live queue explicitly classifies
this item as retire. The current Sheaf theorem has zero holes and already has a complete
proof. This packet repairs the assigned duplicate rather than claiming a proof gain.
The retirement row's consumer is historical: its Sheaf path is absent and its current DAG
attachment is the adopted parent. That parent already uses the adopted comparison.

The two theorem signatures are not definitionally equal: the old one uses
strictHenselizationStructuralMap and unitSectionRestriction along the small-model leg;
the adopted one uses strictLocalizationToBase and qcqsStrictLocalSectionRestriction.
The canonical comparison identifies the presentations. The statement_change explicitly
records this difference and marks the sole current DAG citer,
lem-sbc-integral-fibre-section-local-lift, holds:true, because its existing proof already
uses the full-model theorem and continuity comparison. No quarantined parent requires
the old presentation, and no realized unit node is removed.

Searches were run with msearch.py: LeanFinder returned eight unrelated algebra/etale-locus
results; LeanSearch returned eight structure-sheaf section results, none matching the
etale-module fibre comparison. The Loogle query reported unknown identifier IsIntegralHom
and supplies no negative mathematical evidence. Mathlib grep returned zero hits. Local
rg found the adopted exact-name theorem and its already-adopted consumer, which give the
shortest route for this assigned retirement. No new mathematical statement was needed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
