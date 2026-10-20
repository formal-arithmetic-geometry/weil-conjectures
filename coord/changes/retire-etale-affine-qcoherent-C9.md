# AlgebraicGeometry.Etale.etale_affine_qcoherent_succ

## Reason

The current queue and coord/retire-items.tsv assign retirement of the unused Sheaf copy.
It contains zero sorry holes. There are no importers, and neither declaration has an
external consumer. The adopted source theorem proves the same positive-degree vanishing;
the successor-degree result is its specialization at n + 1. Keeping the Sheaf copy
would retain a duplicate public name and a duplicate proof.

## Old

```lean
theorem etale_affine_qcoherent_succ
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (Sheaf.H
      (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) (n + 1))

theorem etale_affine_qcoherent
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] :
    ∀ (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q)
```

## New

Withdraw lean/Sheaf/AlgebraicGeometry/EtaleAffineQcoherent.lean using deleted.txt.
The existing source theorem remains verbatim:

```lean
theorem etale_affine_qcoherent
    (X : Scheme.{u}) [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H (AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf F) q)
```

Reattach lem-sc-etale-affine-qcoherent-succ to that theorem, specialized at n + 1
using Nat.zero_lt_succ n. Its mathematical statement and proof dependencies stay intact.
No target or source-library declaration changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleAffineQcoherent | C9 | Retired; its internal wrapper is its only declaration consumer. |

Both downstream.py queries found zero downstream modules. A whole-library rg search
found no imports of the retired module and no external declaration references.
The DAG attachment moves to the source theorem; the unit has no realized step assigned
to the retired wrapper. No forced adaptations are needed.

## Status

landed 20261020T135354-L-1815537 2026-10-20 (merge of deliver/C9/Sheaf.AlgebraicGeometry.EtaleAffineQcoherent)
