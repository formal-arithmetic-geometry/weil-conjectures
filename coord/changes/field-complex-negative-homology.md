# AlgebraicGeometry.Scheme.Modules.homotopyEquiv_of_single_field_homology

## Reason

The old intermediate is false because its vanishing hypothesis only ranges over
natural degrees although its complex is indexed by integers. The already landed
certified counterexample is the rank-one free sheaf placed in degree -1, with
i = r = 0. Add explicit negative-degree homology vanishing. This is the missing
assumption already supplied by the original field-fibre argument's strict support.
The counterexample helpers are retained, without edits, as evidence about the old interface.

## Old

```lean
theorem homotopyEquiv_of_single_field_homology
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ)
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r)))))
```

## New

```lean
theorem homotopyEquiv_of_single_field_homology
    {R : CommRingCat.{u}} (hR : IsField R)
    (P : CochainComplex (Spec R).Modules ℤ)
    (i r : ℕ) (hzero : ∀ q : ℕ, q ≠ i → IsZero (P.homology q))
    (hnegative : ∀ q : ℤ, q < 0 → IsZero (P.homology q))
    (hrank : (P.homology i).IsFiniteLocallyFreeOfRank r) :
    Nonempty (HomotopyEquiv P
      ((CochainComplex.singleFunctor (Spec R).Modules (i : ℤ)).obj
        (SheafOfModules.free (R := (Spec R).ringCatSheaf) (ULift.{u} (Fin r))))) := by
  have hzeroInt : ∀ q : ℤ, q ≠ (i : ℤ) → IsZero (P.homology q)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FieldComplexHomotopyNormalForm | N2 | Corrected intermediate signature; proof reduced to contraction onto cohomology and a proved free-sheaf identification. |
| Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre | unclaimed | Forced proof adaptation only: install the existing hge as an instance, transport strict nonnegative support through termwise pullback, and supply negative homology vanishing. Its signature and visibility are identical. |

No definition, target signature, or meaning of a target is changed. All transitive
users keep their signatures and conclusions. The direct caller already assumes
strictly nonnegative support and so does not acquire a new hypothesis. Its original
application fails against the corrected dependency because its former hrank argument
is now supplied where negative-degree vanishing is required. The adaptation changes
only the final application and adds the support-instance setup needed for that argument.
The caller's node is updated to name the two declarations that its actual proof uses.

## Status

landed 20261012T184323-L-4011726 2026-10-12 (merge of deliver/N2/Sheaf.AlgebraicGeometry.FieldComplexHomotopyNormalForm)
