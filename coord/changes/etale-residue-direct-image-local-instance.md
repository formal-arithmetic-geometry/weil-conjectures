# AlgebraicGeometry.Etale.hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound

## Reason

The completed proof specializes a generic coefficient-ring argument to nested quotient
rings. As in ResidueTorAmplitudeTest, prefer CommRing.toRing locally so that checking
this specialization follows the same ring-instance path rather than repeatedly unfolding
the quotient construction. The command is local to the namespace/file; it introduces no
exported instance or declaration and changes no public statement or definition.
The mechanical preflight conservatively flags a local attribute with an explicit priority
as a command change, hence this record. The complete file compiled in 35 seconds, and
its corrected version passed delivery compilation and axiom checks before this record.

## Old

```lean
namespace AlgebraicGeometry.Etale
```

No local override of CommRing.toRing priority was present.

## New

```lean
namespace AlgebraicGeometry.Etale

-- Use the same quotient-ring instance path as the residue criterion.
attribute [local instance 20000] CommRing.toRing
```

All existing declaration signatures and public imports remain verbatim. The added generic
helper is private and proved; the original theorem's single sorry is replaced by a proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow | B5 | Local proof elaboration only. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Existing theorem application retains precisely the same signature; no adaptation. |

The table is the union of downstream.py's downstream modules and declaration users.
The consumer at its existing htF application supplies exactly the original hypotheses.
No target meaning changes because the local command changes no exported definition.

## Status

landed 20261023T102421-L-2895888 2026-10-23 (merge of deliver/B5/Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow)
