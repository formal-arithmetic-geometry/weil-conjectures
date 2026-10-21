## What changed

Repair returned head 19d77ccdb (reviewer C-19d77) against current shared sources.
Retire the redundant Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
wrapper, migrate its 29 current direct importers to the upstream owners, and
replace the small-cone equation in those and three indirect consumers with the
identical `(exists_strictHenselizationStructuralMap s).choose_spec j` proof.
Backward rewrites retain explicitly typed equalities. Existing consumer signatures,
definition data, and unrelated proofs remain unchanged.

Rebase by excluding seven stale consumer copies. In particular, preserve the
current complete colimit-comparison helpers and upstream imports of
StrictHenselRootNormalizationFinite (M2 at the return) and
StrictHenselRootNormalizationGenericEtale (G8 at the return). Neither module has
changed lines in this delivery. Preserve the independently withdrawn
CompatibleStrictHenselizationResidueLift instead of restoring its former proof.

Change record: coord/changes/M4-retire-strict-henselization-structural-map.md.

## Proved and sorry left

The assigned module has 0 sorries before retirement. Closed 0 holes; added 0 holes;
split off 0 statements. This is a wrapper retirement, not a proof-count increase.
The following five consumer holes are unchanged:

- `isIso_upperStarGmSheafToGmSheaf_strictHenselization`
  (node `lem-weil-pbc-gm-pullback-strict-henselization`).
- `indEtale_strictLocal_invariance`
  (node `lem-trf-ind-etale-strict-local-invariance`).
- `isIso_strictHenselizationClosedImmersionCartesian`
  (node `lem-trf-closed-immersion-strict-localization-cartesian`).
- `exists_boundedDimension_projective_local_model`
  (node `lem-trf-bounded-dimension-projective-local-model`).
- `smooth_geometric_stalk_algebra`
  (node `lem-trf-smooth-geometric-stalk-algebra`).

## No longer needed

Withdraw Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap via deleted.txt.
Replace all current direct imports of that wrapper with its upstream owners.
Its compatibility equation is replaced by its own choose_spec proof expression.
No upstream declaration, mathematical node, unit step, or quarantined source is
withdrawn. The structural-map node retains its upstream Lean attachment.

Omit stale adaptations of StrictHenselRegularDivisorQuotientNoetherian,
StrictHenselRegularDivisorQuotient, and StrictHenselizationAffineChartIndEtale.
The first two current modules already use the upstream API; the third is already
withdrawn. Preserve all current SmallStrictHenselizationIndEtale imports and calls.

## Where the brief, the DAG or earlier work was wrong

The returned packet omitted forced-adaptation evidence and holders for the finite
and generically etale normalization modules. Current shared sources have since
migrated both modules to the upstream API. Their retained sandbox copies would
revert complete comparison proofs and imports, so those copies are removed.
The change record now names both modules and their returned holders M2 and G8,
and records that rebasing eliminates their adaptations. The current residue-lift
module is independently withdrawn and is also preserved verbatim.

## Forced adaptations

`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite`
was held by M2 at returned head 19d77ccdb.
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale`
was held by G8. Current changed lines in each: none. Both current originals already
publicly import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap;
the finite proof already uses choose_spec directly, and neither uses the withdrawn
Sheaf equation. Both retain their full small-colimit comparison helpers and every
existing signature and proof. The stale sandbox adaptations are excluded entirely.
Thus no original compiler error caused by this withdrawal is claimed: compilation
of the unmodified current originals against an empty wrapper tests that no forced
edit is needed. Server results are recorded below.

`Sheaf.AlgebraicGeometry.CompatibleStrictHenselizationResidueLift` formerly held
by R8 is now an independently withdrawn empty module. Changed lines: none.
Its stale restoration is excluded. The current R4 Noetherian module and M1 regularity
module likewise remain verbatim; their earlier adaptations stay excluded.
The same rebase removes stale copies of RegularDivisorStrictHenselRootSection,
StrictHenselRootFiniteEtaleModel, StrictHenselRootPurityData and
StrictHenselRootTameNormalization, which already use the upstream owner.

StrictHenselizationClosedLift retains the previously reviewed forced public
StructuralMap import: its existing public theorem signature uses that map.
The prior original-consumer check failed at line 38 with
`Unknown identifier strictHenselizationStructuralMap` and Lean's note that it was
imported privately. Its Extension import remains private. Other adaptations change
only wrapper imports, direct equation uses, or explicitly typed backward rewrites.
AffineLineProjectionStalkBound retains the previously reviewed privateModule
linter suppression; no new diagnostic option is added.

The retained set passes the server compile: all 32 adapted consumer modules and
the temporary empty-wrapper overlay compile (exit code 0). The temporary wrapper
source is removed after verification; deleted.txt alone carries its withdrawal.
The assigned module has zero holes, and the five retained consumer holes are
unchanged. No new nodes or proof holes are introduced.

Both unchanged normalization originals compile on the server with the empty-wrapper
overlay: StrictHenselRootNormalizationFinite in 12.2 s and
StrictHenselRootNormalizationGenericEtale in 0.1 s (exit code 0). The initial
request received no server answer; the retry passed. This confirms that the two
returned adaptations are unnecessary against current shared sources and are
correctly omitted. Their source snapshots match the current repository verbatim.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
