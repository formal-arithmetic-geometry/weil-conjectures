# CategoryTheory.rawCouple

## Reason

Repair the returned delivery on the current shared module after its concurrent
replacement. The current file has a hollow `rawCouple` definition and two theorem
holes. The retained delivery used `BigradedExactCouple.ofShifted`, which is absent
from the current compiled API. Construct the current exact-couple structure
explicitly, using raw objects and maps and only proof fields from
`truncation_raw_exact`. Simplify its projections directly in the naturality proof.
The public theorem and all existing signatures and visibility stay identical.

## Old

```lean
private noncomputable def rawCouple
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) : BigradedExactCouple B 0 := by
  sorry
```

## New

```lean
private noncomputable def rawCouple
    {A : Type uA} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
    [HasDerivedCategory.{wA} A]
    {B : Type uB} [Category.{v} B] [Abelian B] [IsGrothendieckAbelian.{v} B]
    [HasDerivedCategory.{wB} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    (K : CochainComplex.Plus A) : BigradedExactCouple B 0 := by
  let h := truncation_raw_exact F K
  exact
    { D := TruncationCouple.D F K
      E := TruncationCouple.E F K
      alpha := TruncationCouple.alpha F K
      f := TruncationCouple.f F K
      g := fun p q ↦ TruncationCouple.g F K p q ≫ eqToHom (by simp)
      alpha_f_zero := fun p q ↦ (h.1 p q).choose
      f_g_zero := fun p q ↦ (h.2.1 p q).choose
      g_alpha_zero := fun p q ↦ (h.2.2 p q).choose
      exact_alpha := fun p q ↦
        (ShortComplex.exact_iff_image_eq_kernel _).mp (h.1 p q).choose_spec
      exact_f := fun p q ↦
        (ShortComplex.exact_iff_image_eq_kernel _).mp (h.2.1 p q).choose_spec
      exact_g := fun p q ↦
        (ShortComplex.exact_iff_image_eq_kernel _).mp (h.2.2 p q).choose_spec }
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.NaturalTruncationCouple --uses rawCouple`
was checked again. No external declaration can use this private helper. Its
consumers are `abutmentMap_isIso` and the public existence theorem, both in the
item module; both proofs are completed in this delivery. No public signature or
public definition changes, and no target statement needs renewed review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.NaturalTruncationCouple | T1 | Construct raw data; prove two theorem holes. |

## Status

landed 20261017T003429-L-3317743 2026-10-17 (merge of deliver/T1/Sheaf.CategoryTheory.NaturalTruncationCouple)
