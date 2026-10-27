# WeilConjectures.PurityFiniteSetting.agreementCartierEtale

## Reason

The original successor-indexed Cartier-family witness forces large dependent coefficient
conversions in kernel checking. Use the existing `cartierRelativeCoefficientBoundary`
instead. This is the canonical scalar adjunct of the same integral relative boundary,
with its specified complementary section and roots-projection coefficient map. Its full
`SupportedKummerBoundary` normalization uniquely identifies it with the published
Cartier etale family. This retains the effective-Cartier construction at every positive
coefficient level, including ramified coefficients and empty divisors.

## Old

```lean
def agreementCartierEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2 := by
  cases P with
  | @mk F C E hE level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n =>
      letI : FiniteDimensional (Padic C.l) E := hE
      let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
      have hT : IsUnit (C.l : Γ(T, ⊤)) :=
        (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
          (by simpa only [diagonalExponent, Nat.cast_pow] using Q.diagonalExponent_isUnit a)
      exact (Etale.cartier_kummer_map C.l E).2.exists.choose.1
        n n Q.diagonalExponent_annihilates i hI hT
```

## New

```lean
def agreementCartierEtale (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Abelian.Ext
      ((Etale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj (P.constantEtale D))
      (P.frameTwistEtale T 1) 2 :=
  P.cartierRelativeCoefficientBoundary a i hI
```

Add the public import `Sheaf.Paper.CartierRelativeBoundaryRealization`, required by the
new definition body. The existing `agreementCartierMap` body, all existing declaration
signatures, and the target statements are unchanged. Reuse the last equality of
`cartier_relative_boundary_realization` for the first theorem clause. The second clause
uses normalized-family etale pullback and the existing site-comparison pullback law.
This definition change is submitted for independent semantic review in the target closure.

## Users

`tools/downstream.py Sheaf.Paper.CartierClassAgreement --uses agreementCartierEtale`
and `--uses agreementCartierMap` were run on the current source. Their output lists
the item itself and the two direct users below; FlagLocalComparison is a transitive
consumer. None unfolds the repaired definition, and their statements retain the same
canonical Cartier class. No consumer is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CartierClassAgreement | B7 | Reuse canonical normalized scalar adjunct. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | Same normalized representative; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | B5 | Same normalized representative; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Same transitive interface; no adaptation. |

## Status

landed 20261025T201433-L-2510229 2026-10-25 (merge of deliver/B7/Sheaf.Paper.CartierClassAgreement)
