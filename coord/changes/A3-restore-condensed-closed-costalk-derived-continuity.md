# Restoring condensed closed-costalk derived continuity

## Reason

The assigned rework row preserves the item in quarantine after the merge queue
reverted a cluster restore. Restore its actual proof and dependencies at the live
module path. Compiling the archive against the current recollement interface exposes
a dependent-elimination failure in its witness extraction, which is repaired here.

## Old

The live path lean/Sheaf/Paper/CondensedClosedCostalkDerivedContinuity.lean is absent.
The authoritative source is quarantine/Sheaf/Paper/CondensedClosedCostalkDerivedContinuity.lean.
It contains zero sorry proofs and retains both public theorem declarations:
AlgebraicGeometry.ProEtale.condensed_closed_costalk_derived_continuity and
AlgebraicGeometry.ProEtale.colimit_isStrictlyGE.

In the archived proof the dependent witnesses were extracted by:

```lean
  obtain ⟨hclosed, hr⟩ := CondensedRing.condensed_open_closed_recollement Λ i W.ι hk
  let _ := hclosed
```

and subsequently:

```lean
  rcases hr.the project server.the project server.the project server with ⟨H₀, hAdd, hLim, ash, aj, bj, ai, bi, hjs, his, hdata⟩
```

## New

Restore every declaration, signature, visibility, exported attribute, import, and
definition from the archive. In the main theorem proof, name the existential proofs before
unpacking their dependent witnesses:

```lean
  have hrec := CondensedRing.condensed_open_closed_recollement Λ i W.ι hk
  obtain ⟨hclosed, hr⟩ := hrec
```

and:

```lean
  have hs := hr.the project server.the project server.the project server
  rcases hs with ⟨H₀, hAdd, hLim, ash, aj, bj, ai, bi, hjs, his, hdata⟩
```

This avoids the compiler's `Tactic generalize failed: result is not type correct`
error at the archived obtain and rcases commands. The mathematical argument and
the DAG route are unchanged. Add only these file-local transparency settings to
keep the closed structure and coefficient inverse image behind their existing APIs:

```lean
attribute [local irreducible] CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
```

They are not exported and change no mathematical definition. The restored file
compiles cleanly against the current dependency build in 34.8 seconds.
No new public declarations or unproved statements are introduced. No definition
used by any target changes meaning and no target statement review is reopened.

## Users

The live downstream script reports an unknown module because the assigned source
is quarantined. A direct import scan of lean/Sheaf, lean/WeilConjectures,
quarantine/Sheaf, and quarantine/WeilConjectures gives exactly these three direct
consumers, all quarantined when inspected. None is adapted: public and private
interfaces, including the helpers accessed by import all, remain identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | not queried; unchanged consumer | Archived import-all consumer; identical helper interfaces and public statements. |
| Sheaf.Paper.CondensedClosedCostalkInjectiveContinuity | not queried; unchanged consumer | Archived consumer; identical derived continuity theorem. |
| Sheaf.Paper.CondensedLocalPieceCostalkModel | not queried; unchanged consumer | Archived consumer; identical colimit_isStrictlyGE theorem. |

## Status

landed 20261021T022425-L-2845653 2026-10-21 (merge of deliver/A3/Sheaf.Paper.CondensedClosedCostalkDerivedContinuity)
