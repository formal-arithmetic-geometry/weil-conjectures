# WeilConjectures.cachedCochainMonoidal and WeilConjectures.cachedDerivedMonoidal

## Reason

Proving adicPurityDerivedTensorGeneric_existsUnique requires repeated inference of
the monoidal structures on complexes and the derived category. Caching the existing
inferred structures locally reduces the focused check from 29.5 to 20.2 seconds;
the initial complete module then compiled cleanly in 55.5 seconds. Since delivery's
appended probe exceeded 60 seconds, the existing concrete existence proof also
uses the proved private finiteTensorIsoType_eq to transport its comparison once,
rather than repeating a large definitional conversion. This is the identical
isomorphism type and retains the original heterogeneous normalization. The proved
private nonempty_heq_transport and heq_model_unique perform the elementary transport
and uniqueness reasoning abstractly, keeping concrete coefficient terms out of
repeated kernel conversions. Only the existing existence and uniqueness theorem
proofs change; their statements and all definition bodies remain verbatim.
The cache bodies are exactly inferInstance. No mathematical construction changes,
and no instance registration escapes the TensorRealization section.

## Old

The TensorRealization section had no local monoidal cache declarations. Every use
reconstructed the same instances through the generic typeclass search.

## New

```lean
local instance cachedCochainMonoidal : MonoidalCategory (CochainComplex A ℤ) :=
  inferInstance
local instance cachedDerivedMonoidal : MonoidalCategory (DerivedCategory A) :=
  inferInstance
```

The names are public because the same canonical structures occur in public theorem
types; both instance registrations are local. Existing source signatures, definition
bodies and attributes are unchanged. The fully proved private singleTensorIso and
singleTensorIso_eq implement the generic comparison from the existing right K-flat
counit and its equality with the prescribed counit. No sorry is added.

## Users

The downstream text search reports zero modules mentioning either new cache name.
The local registrations cannot affect importers, and the cached structures are
definitionally the original inferred structures. No consumer needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicPurityTwistReduction | X9 | Proved the generic comparison; reuse identical monoidal instances locally. |

## Status

landed 20261025T164805-L-1081864 2026-10-25 (merge of deliver/X9/Sheaf.Paper.AdicPurityTwistReduction)
