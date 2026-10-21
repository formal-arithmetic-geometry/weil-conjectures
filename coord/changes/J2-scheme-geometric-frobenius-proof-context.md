# schemeGeometricFrobenius_naturality

## Reason

Prove the existing naturality theorem from the normalized Frobenius trivialization
and the stated factorized-square pasting theorem. The preflight conservatively
classifies the new local reducibility attributes and declaration-local options as
commands affecting the public environment. This record documents those commands;
they change only proof elaboration. Existing signatures, visibility, definitions,
instances, and public imports remain unchanged. No target meaning changes.

## Old

The existing public theorem `schemeGeometricFrobenius_naturality` ended in
`:= by sorry`. There were no local irreducibility attributes following
`frobeniusOrdinaryComposition`, and no declaration-local options on this theorem.

## New

Three completely proved private helpers precede `frobeniusDerivedComposition`.
Their proof elaboration uses the following section-local command:

```lean
attribute [local irreducible] proEtaleRingModuleAdjunction
  proEtaleRingModulePullback proEtaleRingModulePullbackObj proEtaleRingModulePullbackMap
```

The private normalization and categorical naturality helpers each have
`set_option backward.isDefEq.respectTransparency false in`.
The existing public naturality theorem, whose signature is unchanged, has:

```lean
set_option maxHeartbeats 800000 in
-- Normalizing the chosen compositors elaborates dependent derived-functor transports.
set_option backward.isDefEq.respectTransparency false in
```

The theorem proof is complete, with zero remaining holes. The heartbeat setting
is an elaboration allowance; the server's 60-second file limit is unchanged.
The finalized packet passed delivery's compile and axiom probe before its first
server preflight requested this record. The prior standalone compile took 26.7 seconds.

Added private import `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting`.
Removed redundant private imports `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`,
`Mathlib.AlgebraicGeometry.Pullbacks`, `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`,
`WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`, and
`WeilConjectures.AlgebraicGeometry.BaseChangeConventions`.
All required declarations are provided through retained public imports.

## Users

`tools/downstream.py Sheaf.SixFunctors.SchemeGeometricFrobenius --names` reports
no current Lean importers. A direct ripgrep import check likewise finds none.
The item remains required by its DAG parents, so no withdrawal is proposed.
All public statements and constructions have exactly their previous meaning;
no consumer adaptation is needed. The attributes are local, and the options
are scoped to the indicated declarations, so neither propagates to importers.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.SchemeGeometricFrobenius | J2 | One hole proved; private helpers and local proof context only. |

## Status

landed 20261021T170736-L-2756523 2026-10-21 (merge of deliver/J2/Sheaf.SixFunctors.SchemeGeometricFrobenius)
