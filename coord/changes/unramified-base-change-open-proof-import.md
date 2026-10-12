# AlgebraicGeometry.unramified_baseChange_restrict_open

## Reason

The statement uses locally finite type morphisms, open immersions, pullbacks and open
restrictions, all supplied by Mathlib.AlgebraicGeometry.Morphisms.FiniteType.
FormallyUnramified is used only in its proof and must be privately imported.
This corrects import visibility without changing any declaration's signature or meaning.
The unused private Thickening import is also pruned.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Sheaf.AlgebraicGeometry.Thickening
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
```

## Users

The repository-wide import/name search found these four importing modules. None uses the
proved declaration yet in a proof body; all independently import their statement vocabulary.
Their signatures and meanings are unchanged and no adaptation is required. No definition
used by a target changes, so no target statement review is reopened. Claim ownership is
unchanged; no importing module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.UnramifiedFibrePointIsolated | not queried; no edit | Own public FiniteType/OpenImmersion imports; unchanged. |
| Sheaf.AlgebraicGeometry.UnramifiedEtaleLocalDecomposition | not queried; no edit | Own public Etale/Separated/Pullbacks imports; unchanged. |
| Sheaf.AlgebraicGeometry.FiniteUnramifiedOnePointClosed | not queried; no edit | Own public Finite/OpenImmersion/Restrict imports; unchanged. |
| Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite | not queried; no edit | Own public QuasiFinite/OpenImmersion imports; unchanged. |

## Status

landed 20261012T063525-L-3162425 2026-10-12 (merge of deliver/W2/Sheaf.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen)
