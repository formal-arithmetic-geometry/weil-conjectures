# WeilConjectures.frobeniusCoefficientModulesTower_existsUnique proof context

## Reason

The two proofs in Sheaf.SixFunctors.FrobeniusCohomologyTransportIso use a proved
private tensor equivalence. After its pure-tensor formula is proved, the helper
is locally irreducible so subsequent naturality and uniqueness proofs use the
formula rather than repeatedly unfold its tensor construction. The delivery
compile initially exceeded 60 seconds; the next profiled full-file compile with
this attribute completed in 41.4 seconds. Profiling options were removed.

A local unused-section-variable linter option preserves the full signature of
the coefficient-stage embedding theorem, including its unused algebraic-closure
instance. Every existing public signature, definition body, visibility and public
import is unchanged. No target meaning changes or consumer adaptations occur.

## Old

No private coefficientTowerEquiv helper or local irreducibility attribute existed.
The existing public theorem proof bodies were `by sorry`.

The existing embedding theorem header is verbatim:

```lean
theorem frobeniusCohomologyStageEmbedding_comp (E L : Index l Ω) (h : E ≤ L) :
    (frobeniusCohomologyStageEmbedding.{u, v} l Ω L).comp
        (coefficientInclusion.{u} l Ω E L h).toRingHom =
      frobeniusCohomologyStageEmbedding.{u, v} l Ω E
```

## New

The public header above and all other public headers remain verbatim. The added
proof-context commands are:

```lean
attribute [local irreducible] coefficientTowerEquiv
```

This applies only after the private helper's pure-tensor formula, within this file.

```lean
set_option linter.unusedSectionVars false in
```

This applies only to frobeniusCohomologyStageEmbedding_comp. Three private helpers
are fully proved. The newly imported tensor Tower module is a private proof import.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FrobeniusCohomologyTransportIso | Z6 | Two original theorem holes closed; local proof-context commands only. |

The new helper is private and has no external consumers. The read-only
`tools/downstream.py Sheaf.SixFunctors.FrobeniusCohomologyTransportIso --names`
audit lists the existing transitive consumers, all of which keep the identical
public interface and definition bodies. They require no adaptations.

## Status

landed 20261025T124531-L-2058099 2026-10-25 (merge of deliver/Z6/Sheaf.SixFunctors.FrobeniusCohomologyTransportIso)
