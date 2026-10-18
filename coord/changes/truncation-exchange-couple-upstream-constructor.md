# CategoryTheory.TruncationExchange.couple

## Reason

The upstream sync removed `BigradedExactCouple.ofShifted`. The sync replaced the private
constructor and its accessor proof with `sorry`. Construct the current upstream structure
from the already proved zero composites and exact short complexes. The data fields are
explicit; only proof witnesses are extracted from existential propositions.

## Old

```lean
private noncomputable def couple
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) : BigradedExactCouple B 0 := by
  sorry

```

## New

```lean
private noncomputable def couple
    (F : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B) [F.CommShift ℤ]
    [F.IsTriangulated] (K : DerivedCategory.Plus A) : BigradedExactCouple B 0 where
  D := D F K
  E := E F K
  alpha := alpha F K
  f := f F K
  g := gShifted F K
  alpha_f_zero := fun p q ↦ (exact_f_alpha F K p q).choose
  f_g_zero := fun p q ↦ (exact_gShifted_f F K p q).choose
  g_alpha_zero := fun p q ↦ (exact_alpha_gShifted F K p q).choose
  exact_alpha := fun p q ↦
    (ShortComplex.exact_iff_image_eq_kernel _).mp (exact_f_alpha F K p q).choose_spec
  exact_f := fun p q ↦
    (ShortComplex.exact_iff_image_eq_kernel _).mp (exact_gShifted_f F K p q).choose_spec
  exact_g := fun p q ↦
    (ShortComplex.exact_iff_image_eq_kernel _).mp (exact_alpha_gShifted F K p q).choose_spec

```

The private `couple_data` lemma is also proved. Its statement is unchanged; its final
component uses `Function.hfunext` and `comp_eqToHom_heq` to remove the zero-degree transport.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TruncationExchangeCouple | R2 | Private constructor; exactness and all five data identities now proved. |

`tools/downstream.py Sheaf.AlgebraicGeometry.TruncationExchangeCouple --uses
CategoryTheory.TruncationExchange.couple` lists only this module as a declaration user.
The direct module consumers are `Sheaf.AlgebraicGeometry.FiniteRangeComparison`,
`Sheaf.AlgebraicGeometry.TruncationExchangeAbutment`, and
`Sheaf.Paper.ExactCoupleDifferential`. None can access this private constructor.
Their imported public signatures, definitions, and visibility are identical; no adaptation
is necessary. No target statement uses the changed private definition in its type.

## Status

landed 20261018T062859-L-672122 2026-10-18 (merge of deliver/R2/Sheaf.AlgebraicGeometry.TruncationExchangeCouple)
