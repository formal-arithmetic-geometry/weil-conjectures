# AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction.integralProjectiveLine_adjunction

## Reason

The proof uses monoidal notation and additional private categorical helpers. Increase
the instance-search size for this file and check declarations synchronously. These
file-local elaboration settings and namespace openings change no exported declaration,
instance, notation, or statement. The static preflight treats command changes as an
interface risk; this record explains their scope. The new public declarations all have
new nodes and live in four new Sheaf modules.

## Old

```lean
set_option synthInstance.maxSize 2048
```

The original module did not set Elab.async and did not open MonoidalCategory locally.
Its sole public theorem had a sorry proof.

## New

```lean
set_option synthInstance.maxSize 4096
set_option Elab.async false
open CategoryTheory.MonoidalCategory
```

These commands affect only elaboration within the file. Three proved private helpers
supply residue-field units and cancellation of the two integrated scalar composites.
The original theorem signature, visibility, and public imports stay byte-identical.
The theorem proof now invokes the three new geometric interfaces and the unit-counit
constructor. No existing definition body is modified.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralAffinePurityInduction | unclaimed | Same public adjunction statement and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionLine | unclaimed | Same public adjunction statement and imports; no adaptation. |
| Sheaf.SixFunctors.IntegralProjectiveLineAdjunction | K5 | Private proof helpers and file-local elaboration commands only. |

Both direct consumers are being checked unchanged against the replacement. No source
module or quarantined module is withdrawn. Every other downstream consumer sees the
same original public interface.

## Status

landed 20261025T202418-L-2714738 2026-10-25 (merge of deliver/K5/Sheaf.SixFunctors.IntegralProjectiveLineAdjunction)
