# AlgebraicGeometry.Scheme.shortExact_of_retract

## Reason

Repair of returned delivery 9e5db492b5: its comparison module duplicated this
existing generic retract lemma. The original lemma was private, so importing
its module alone could not expose it. Make the existing lemma public in place,
remove the duplicate, and use the existing qualified name. The original module
is unclaimed in coord/claims at repair time (2026-10-18).

## Old

```lean
private theorem shortExact_of_retract
    {A : Type*} [Category A] [Abelian A] {S T : ShortComplex A}
    (i : S ⟶ T) (r : T ⟶ S) (hir : i ≫ r = 𝟙 S) (hT : T.ShortExact) :
    S.ShortExact
```

## New

```lean
theorem shortExact_of_retract
    {A : Type*} [Category A] [Abelian A] {S T : ShortComplex A}
    (i : S ⟶ T) (r : T ⟶ S) (hir : i ≫ r = 𝟙 S) (hT : T.ShortExact) :
    S.ShortExact
```

Only visibility changes; all binders and the proof are retained. Add a one-line
docstring. No definition or target statement changes meaning.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom
--uses AlgebraicGeometry.Scheme.shortExact_of_retract` finds only the defining
module. Repository search confirms that its only existing call is internal.
The added consumer is included below. All other downstream modules use the
unchanged existing public API and need no adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom | unclaimed | Expose the existing helper; its internal call and proof stay unchanged. |
| Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomMapQuasiIso | K3, new in this delivery | Remove the duplicate private helper, import the original module, and call the qualified existing theorem. |

No module held by another group is adapted. The existing theorem about strictly
perfect complexes is unchanged. The new import direction was checked with
`tools/import_direction.py may` and has no cycle.

## Status

landed 20261018T091407-L-3256704 2026-10-18 (merge of deliver/K3/Sheaf.Algebra.Homology.RingedSiteBoundedFreeRHomModel)
