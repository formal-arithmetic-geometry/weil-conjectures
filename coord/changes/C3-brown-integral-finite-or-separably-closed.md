# CategoryTheory.brownHypotheses_padicIntegers_of_finite_or_separablyClosed

## Reason

Provide the integral Brown bundle in the supported finite-or-separably-closed
base-field case, by connecting the existing upstream uniform Ext bound to the
proved integral Brown criterion. Preserve the disputed arbitrary-field unit
statement and its original named hole, as required by the maintainer rollback
`maintenance-K4-brown-false-split-rollback.md`.

## Old

No declaration with this name existed. Every existing signature, definition,
instance, attribute and public import of the item is preserved.

## New

```lean
theorem brownHypotheses_padicIntegers_of_finite_or_separablyClosed
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] (hk : Finite k ∨ IsSepClosed k) :
    BrownHypothesesFor (Profinite.padicIntegersRingObj ℓ E) X
```

A proved private helper transports finite constant-model constructibility to
ordinary constructibility. Four private proof imports supply that helper, the
uniform Ext bound, and the integral Brown criterion. The new signature's
`IsSepClosed` is already publicly imported through BrownHypothesesDefinitions.
No target definition or target statement changes, and no false unrestricted
compactness lemma is reintroduced.

## Users

The declaration-use search finds zero current users of the added name.
The four direct importers of the item are listed for interface review; none
requires an adaptation, since all previously exported declarations are preserved.
The delivery tool checks these consumers against the changed file.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctorsBasics.BrownHypothesesFiniteField | unclaimed | Direct importer; existing signatures preserved. |
| Sheaf.SixFunctorsBasics.BrownHypothesesCoefficientIso | unclaimed | Direct importer; existing signatures preserved. |
| Sheaf.Paper.LocalizingExceptionalAdjoint | unclaimed | Direct importer; original Brown assertion unchanged. |
| Sheaf.Paper.ExceptionalInverseImageExistence | unclaimed | Direct importer; original Brown assertion unchanged. |

Holder labels refer to the current claim records checked during this session.
No source-library module is edited. No existing node is changed.

## Status

landed 20261028T072348-L-1937428 2026-10-28 (merge of deliver/C3/Sheaf.SixFunctorsBasics.BrownHypotheses)
