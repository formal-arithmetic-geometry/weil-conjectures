# FrobeniusSystemExchangeInverse private inverse calculation

## Reason

Finish the direct integral inverse formula and reduce compact inverse evaluation
into forward compatibility and an explicit inverse construction. Derived objects
carry large typeclass instances, so the existing kernel-checked structural
congruence helper is also used to compare the defining forward maps.

## Old

The three public theorems `frobeniusSystemCompact_inverse_evaluation`,
`frobeniusDirectIntegral_inverse` and `frobeniusCompactIntegral_inverse` had their
existing signatures and proofs `:= by sorry`; the compact integral inverse remains
unproved because its geometric-fiber wrapper needs a separate transport lemma. The private categorical helper
`inverse_realization`, `repairRealizationApplication` and local proof tactic
`frobenius_realization_exact` were absent.

## New

The three existing theorem signatures are unchanged. The private helper proves
that the inverse of `alpha.hom ≫ L.map e.hom ≫ beta.hom` is
`beta.inv ≫ L.map e.inv ≫ alpha.inv`, by equality of isomorphisms. The existing private structural congruence helper now normalizes the inclusion
and lift of a full subcategory, the named realization wrappers, and the object,
morphism and whiskering formulas of composite functors. These are computational
reductions of the specified functors, not new mathematical assumptions.
`repairRealizationApplication` transports the final four arguments of the inverse
calculation along explicit equalities of their types. The local tactic
`frobenius_realization_exact` uses these transports and the existing structural
congruence proof to avoid costly implicit kernel conversions. Every generated
term is checked by Lean's kernel. The original `repairApplication` and its
existing callers are preserved.

The new proof import `Sheaf.Paper.SystemCompactExchangeEvaluation` provides the
strictly smaller forward evaluation identity for the actual proper/open system
composite. Its only theorem, `systemCompactExchange_evaluation`, is deferred and
has its own DAG node, source and complete proof in words. The parent uses this
identity to construct the finite isomorphism and calculate its inverse. No data
is chosen from this deferred equality.

Proof-local instance selection and reducibility attributes are confined to the
integral proof section or theorem commands. No public signature, definition,
instance registration, existing public import or target meaning changes.

## Users

Source search finds one direct importer. The new private helpers are unavailable
to consumers, and the new compatibility module is imported only for the proof.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | J7 | Existing signatures and public exports preserved; no adaptation. |

## Status

landed 20261027T234040-L-4173645 2026-10-27 (merge of deliver/K6/Sheaf.Paper.FrobeniusSystemExchangeInverse)
