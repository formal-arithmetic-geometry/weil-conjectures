## What changed

Complete the retirement item for
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale (zero original holes).
Withdraw its duplicate triples-colimit proof. Repoint its existing node to the adopted
upstream twin, whose theorem uses the full affine-neighbourhood strict localization.

Add Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale, a proved transport
corollary for existing small-model consumers. Its private compatibility lemma proves
that the canonical small/full colimit isomorphism respects the structural map.
The public theorem composes the given spectrum isomorphism with that comparison,
rewrites the base-map equation, and applies the upstream theorem unchanged.
The upstream import is private because exposing its full-model structural-map helper
would clash with the different small-model helper already in consumer environments.

All 17 live direct consumers change their import; 12 live theorem calls use the new
corollary name. Two archived consumers remain quarantined, with their sources, Lean
attachments and dependencies preserved. Other signatures, definitions, hypotheses, universes and algebra
structures remain unchanged. The intentionally private helper module
Sites.AffineLineInfinityStrictLocalModel disables the private-module linter enabled
by the new proof import; its public theorem is already taken out in the baseline.
All affected consumer nodes now cite the small-model corollary in their proof routes.
The original theorem's node records the existing upstream proof and its triples-colimit
dependency. The unit's statement and realized proof steps remain unchanged.

Change record: coord/changes/G3-retire-strict-henselization-affine-chart-ind-etale.md.
Its user table lists every current downstream Sheaf module and the retained
quarantined consumers; no adopted source-library file or target statement is edited.

## Proved and sorry left

This is a retirement repair: proved 0 of 0 original sorries; 0 holes added,
0 split off. The new theorem
AlgebraicGeometry.Scheme.smallStrictHenselization_indEtale_of_affine_chart and its
private structural-map compatibility lemma are completely proved.

The four existing live consumer holes are untouched:

- AlgebraicGeometry.Scheme.indEtale_strictLocal_invariance
  (lem-trf-ind-etale-strict-local-invariance).
- AlgebraicGeometry.Scheme.isZero_cohomology_projective_strictLocal_intersection
  (lem-trf-projective-strict-local-intersection-acyclic).
- AlgebraicGeometry.Scheme.strictHenselization_quasiFinite_ring
  (lem-trf-strict-henselization-quasi-finite-ring).
- AlgebraicGeometry.smooth_geometric_stalk_algebra
  (lem-trf-smooth-geometric-stalk-algebra).

Validation: the new corollary and the adapted live consumers compile remotely.
23 unchanged intermediate modules were compiled in import order to refresh stale
artifacts left from the preceding StrictHenselization retirement. During this repair,
FieldHigherDirectImageStalk was also recompiled unchanged to replace a stale private
comparison signature referring to smallStrictHenselizationDiagram. These unchanged
source copies are excluded from the delivery. The new theorem's #print axioms lists only propext, Classical.choice and Quot.sound.
Final packet checks are recorded by deliver3.py.

## No longer needed

Withdraw Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale.
No current Lean source imports the retired copy after the consumer changes.
Its direct private import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
is no longer needed by our compatibility proof; the adopted upstream theorem still
uses it and WeilConjectures.RingTheory.EtaleResidueTriplesColimit, so these modules
and their DAG dependencies are retained. No upstream declaration is removed.

Remove the unused private import
WeilConjectures.AlgebraicGeometry.StrictHenselization from
Sheaf.AlgebraicGeometry.IndEtaleStrictLocalInvariance and
Sheaf.TraceFormula.StrictHenselizationQuasiFiniteRing. The module itself remains
in the adopted source library and is not claimed pruned.

The new module exposes only the upstream small structural-map definitions and the
IndEtale statement API. Its private upstream-twin import supplies the mathematical
proof without exporting the conflicting full-model helper. No mathematical dependency
of the upstream proof is claimed pruned; exactly one duplicate Sheaf module is withdrawn.
DAG parents citing the original mathematical ind-etaleness result still have the upstream
node; adapted consumer proof routes cite the proved small-model corollary instead.

## Where the brief, the DAG or earlier work was wrong

Repair of returned head f755a769e0: add
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel to the change
record's Users table. This new direct consumer calls the retired theorem in its
private flatness proof. Migrate that private import and identity-chart call to the
proved small-model corollary, preserving every declaration signature and all other
proof lines; update its node's proof dependency accordingly. The module is unclaimed.
The current-source audit also found a new identity-chart call in
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData (now unclaimed);
migrate its private import and call in the same way and update its proof node.
Refresh the Users table to include all current transitive consumers.
Compare every retained live consumer edit with current shared sources.
Current main has quarantined GabberStrictLocalTorsionBound and
Sites.AffineInfinityBoundarySupport again. Exclude their stale restoration files and
node edits from this packet: their archives, Lean attachments and original dependencies
are preserved. They are not withdrawn or counted as pruned. Their original mathematical
dependency remains the affine-chart node, now realized by the upstream full-model
theorem; the proved small-model transport in this packet supplies its original small
API when these consumers are restored. The prepared import/call migrations are retained
in the sandbox scratchpad. Preflight correctly refused restoration because the live
sources of StrictHenselizationStalkFormula, GabberNearbyCycleDimensionBound and
Sites.FieldHigherDirectImageStalk are themselves quarantined. No such unrelated
restoration is part of this retirement.


Earlier reconciliation (before the current re-quarantine): main had restored
GabberStrictLocalTorsionBound and Sites.AffineInfinityBoundarySupport, and the
retained packet migrated their imports and proof routes. These two restoration
files and node edits are now excluded as described above. Independent
landings have already moved AffineStrictLocalRingComparison and NormalConstantGenericUnit
to the upstream full-model theorem; exclude their stale sandbox copies and node edits
so those current proofs and new private helpers are preserved. The quarantined
Gabber theorem retains its archived sorry; this delivery adds no holes.

Repair of returned head bf31bb5248: the reviewer passed the earlier packet, but
landing found a newly added direct consumer,
Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale.
Add its import and identity-chart theorem-call migration, update its node proof
dependency, and refresh the Users table against the current 85 downstream modules.
No existing theorem signature or mathematical argument changes. deliver3.py rebuilds
the retained packet on current sheaf-dag before preflight and push.

Repair of returned head 223b4bcfea: the earlier packet omitted the current direct
consumer Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit.
Add it to the change record Users table, migrate its private import and theorem call,
and update its node proof dependency to the proved small-model corollary.
Its theorem signature and proof argument remain unchanged. The delivery tool rebuilds
the packet on current sheaf-dag; all sandbox Lean changes were compared with the
current shared sources before recompilation.

The generic brief describes proving a sorry, but the current retirement TSV and queue
assign this zero-hole copy for retirement. The upstream twin is not a literal API
replacement: its e targets strictLocalization and its base map is strictLocalizationToBase,
whereas consumers use strictHenselizationScheme and strictHenselizationStructuralMap.
Replacing imports literally fails before the theorem call because full/small helper
names meet; stale compiled dependencies can also import the already retired old
StrictHenselization module. Rebuilding the unchanged intermediate sources and keeping
the full-model proof import private resolves those issues without changing definitions.

The existing source reference was checked against Stacks etale-cohomology.tex,
lemma-describe-etale-local-ring (04HX), and algebra.tex,
lemma-strict-henselization-different (04GW). The new result is the canonical
cofinal-colimit transport of the existing result, with no new mathematical assumption
or unfinished split. The small category is nonempty because it contains representatives
of pointed etale neighbourhoods; arbitrary choices of e are handled by composition.
The blueprint search found no separate imported node for this model-transport corollary.

## New nodes

lem-weil-pbc-small-strict-henselization-ind-etale records the fully proved small-model
corollary of the existing upstream theorem. Its proof first compares structural maps
using the inverse coprojection equation of smallStrictHenselizationColimitIso, then
applies the upstream affine-chart ind-etale theorem to the transported isomorphism.
This adds zero holes. The node inherits the original chapter and unit.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
