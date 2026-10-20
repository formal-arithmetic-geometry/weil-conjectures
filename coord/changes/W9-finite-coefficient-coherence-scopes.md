# Finite-coefficient pushforward coherence scope repair

## Reason

The scheduled sync quarantined the module because its empty `Eta` section
retained two dangling `omit ... in` commands. The recorded compiler error is
`Unexpected name Eta after end`, followed by a namespace mismatch. The returned
packet at `2551dae6b3` also conflicted with a concurrent write after base
`e0d550965`. Reconstruct this repair from the
current quarantined source and use the matching current upstream proofs.

## Old

```lean
section Site

end Site
```

The `Eta` section ended with:

```lean
section Eta

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
end Eta
```

Five identical `omit ... in` commands preceded the associativity theorem.
The original header imported:

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
```

The two theorem proofs took homs of the legacy isomorphism coherences and
simplified (canceling the associator in the first proof).

## New

Both empty sections and the dangling modifiers are removed. One `omit ... in`
remains before each theorem. Both existing public signatures remain unchanged;
their proofs are now respectively:

```lean
  exact ProEtale.lowerStarComp_assoc A h₁ h₂ h₃
```

```lean
  exact ProEtale.lowerStarComp_id_left A k
```

The retained public import is:

```lean
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
```

Its own public import re-exports `CoherenceLegacy`, so removing the redundant
import loses no declarations. The generated header comment is wrapped.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence | W9 | Restored; scope repair and direct upstream proofs; zero holes. |

Exact import and declaration searches in `lean/` and `quarantine/` found no
consumers. The quarantined item is absent from the live downstream index.
No other modules need adaptation, and no definitions or target statements change.
There are no attached DAG nodes to update.

## Status

landed 20261020T145550-L-2413621 2026-10-20 (merge of deliver/W9/Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence)
