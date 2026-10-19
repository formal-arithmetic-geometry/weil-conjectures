# AlgebraicGeometry.Etale.sf_directImage_torAmplitude

## Reason

The proof specializes generic derived-category lemmas to a reducible quotient
coefficient ring. Competing ring and braiding instance paths caused repeated
unfolding of quotient and derived tensor constructions during kernel checking.
Local instance priorities align these paths with those used in the existing
residue criterion. The clean file and axiom probe compile within the file limit.
Preflight classifies the new context commands as an interface change and requires
this record, although these registrations are local to the namespace in this file.

## Old

The context before the existing private helpers was:

```lean
attribute [local irreducible] derivedTensor
```

The public theorem's complete signature is unchanged. Its old proof was `sorry`.

## New

```lean
attribute [local irreducible] derivedTensor
-- Use the canonical ring instance when specializing generic lemmas to quotient coefficients.
-- Alternate instance paths otherwise make kernel checking unfold the quotient repeatedly.
attribute [local instance 20000] CommRing.toRing
-- Match the braidings in the existing derived tensor and residue-test constructions.
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory
```

The existing global instances, definitions, public imports, signatures and
visibility remain identical. The new finite-module conversion helper is private
and fully proved. The public theorem now has a complete proof. No profiling
options remain, and no consumer inherits the local priorities.

## Users

`tools/downstream.py Sheaf.Paper.DirectImageTorAmplitude --uses
AlgebraicGeometry.Etale.sf_directImage_torAmplitude` finds 498 transitive importers
and no use of the declaration outside its owning module. The only change that
preflight identifies as affecting importers is the local context commands.
They expire at the end of the namespace and are not exported. Thus the 498
transitive importers retain their existing elaboration context and statements.
The direct importers and the owning module are listed below; none is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.DirectImageTorAmplitude` | S9 | Complete proof; private helper and local instance priorities. |
| `Sheaf.Paper.FiniteCoefficientDirectImage` | G8 | Public signature unchanged; local priorities are not exported. |
| `Sheaf.Paper.FiniteTorStability` | unclaimed | Public signature unchanged; local priorities are not exported. |
| `Sheaf.Paper.EtaleGeometricBiduality` | G1 | Public signature unchanged; local priorities are not exported. |

No target definition or target statement changes; no target meaning review is
reopened by these proof-context registrations.

## Status

landed 20261019T192834-L-1874940 2026-10-19 (merge of deliver/S9/Sheaf.Paper.DirectImageTorAmplitude)
