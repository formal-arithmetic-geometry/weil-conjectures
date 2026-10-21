# AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum

## Reason

Restore the quarantined module assigned in coord/rework.tsv, preserving its complete
proof, Lean attachment, dependency imports, public signature and definitions. Its
archived qcqsCostalkModel proof partially applies the changed closed-support exactness
theorem: Lean cannot infer its implicit open-complement scheme U. The current theorem
requires the specified quasi-compact complementary open and the complement identity.

## Old

In the archived private qcqsCostalkModel proof:

```lean
  have hclosed := CondensedRing.closedSupport_lowerStarExact Λ i
  let H₀ := CondensedRing.closedSupport Λ i k
  have hik' : Set.range i.base = (Set.range k.base)ᶜ := by
    rw [hik, compl_compl]
  let ash := CondensedRing.closedSupportAdjunction Λ i k hik'
```

## New

```lean
  let H₀ := CondensedRing.closedSupport Λ i k
  have hik' : Set.range i.base = (Set.range k.base)ᶜ := by
    rw [hik, compl_compl]
  let := CondensedRing.closedSupport_lowerStarExact Λ i k hik'
  let ash := CondensedRing.closedSupportAdjunction Λ i k hik'
```

The exactness result is now installed locally after the complement identity is proved.
In `qcqsInjectiveCostalkContinuity`, the expanded construction of the truncation
projection and its `IsColimit` witness is replaced by the existing proved helper:

```lean
  let d := condensedContinuityCocone J a
  have hd : IsColimit d := canonicalContinuityIsColimit J a hJ
```

This is the same construction already used in this file. It avoids a profiled
20-second elaboration step; the optimized complete file compiles in 44.5 seconds.
All archived public signatures, public imports, attributes and definitions are unchanged.
No target meaning changes. The existing node keeps its Lean attachment and dependencies;
proof step 4 documents the local instance required by the composed derived adjunction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum | A6 | Restore archive and repair private proof. |
| Sheaf.Paper.ConstructibleExtContinuity | quarantined; unclaimed in local snapshot | Archived direct importer and theorem consumer. Public interface unchanged; no adaptation required. |

`tools/downstream.py` with `--allow-missing --uses` finds zero live downstream modules
and zero live uses. Searching quarantine identifies the direct consumer above, whose
application supplies the identical public theorem arguments. No module is withdrawn.
No source-library file is changed.

## Status

landed 20261021T151100-L-1118417 2026-10-21 (merge of deliver/A6/Sheaf.AlgebraicGeometry.ConstructibleExtContinuityStratum)
