# Sheaf.Paper.SmoothPurityTowerBound

## Reason

The proof replaces the inherited proof imports with the interfaces actually used by
`sp_tower_bound`: right-derived D+ compatibility, the compact-support uniform bound,
and the section-normalized tower levels.  The removed imports are transitively needed
for the definitions and are not bypassed.  The unit-route import
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` is retained explicitly because
stage 3 requires the recorded unit route to remain visible.  Local irreducibility
attributes and local transparency options keep dependent coefficient definitions from
unfolding during elaboration; these commands are confined to this module and do not
alter any exported declaration or target statement.

The theorem signatures and both public definitions are unchanged.  The node copy is
updated only to record the proof route and its actual dependencies.  No definition or
statement meaning changes.

## Old

The module imported `Sheaf.Paper.ConstantModelTorAmplitude`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and
`Sheaf.Paper.SmoothPurityCoefficientTowers` directly and had an unproved theorem.

## New

The module imports the right-derived plus compatibility interface, the compact-support
uniform Tor bound, the tower-level route, and retains the coefficient-extension unit
route.  It proves `AlgebraicGeometry.ProEtale.sp_tower_bound` with the original
signature and leaves no `sorry`.  The removed coefficient modules remain in the
transitive import closure of the definitions used by the theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SmoothPurityTowerBound | J3 | item module; proof imports and local attributes updated |
| Sheaf.Paper.CompactSupportUniformTorBound | unclaimed | imported proof interface; no source changes |
| Sheaf.Paper.SmoothPurityTowerLevels | unclaimed | retained unit route; no source changes |

## Status

landed 20261019T231220-L-561961 2026-10-19 (merge of deliver/J3/Sheaf.Paper.SmoothPurityTowerBound)
