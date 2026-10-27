# Relative Cartier Kummer realization presentation and proof scope

## Reason

The original relativeCartierProExt transports its chosen class through an equality of
entire Ext types. Unfolding that transport in the arrow realization exceeded the
existing compile limit in focused and whole-file checks. A direct successor match
selects exactly the same published class, at the same positive coefficient level,
without transporting through an equality of Ext presentation types. No coefficient
quotient, normalizing unit, annihilating exponent, source, or target changes.

RelativeCartierRootNormalized also uses a direct positive-level match, replacing
nested tactic cases and their dependent transports by the same explicit successor
predicate. Its public signature and root-tensor formula are identical. The node's
mathematical statement remains unchanged.

The item adds a proved private positive-level induction helper and proof-local
irreducibility attributes for derived and supported-Hom presentation aliases. No private helper
occurs in a public signature or definition. Public imports are preserved.

## Old

```lean
@[no_expose] def RelativeCartierRootNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (q : P.frameTwist T 1 ≅ P.relativeCartierProLine T) : Prop := by
  cases P with
  | @mk F C E hE level hlevel =>
    cases level with
    | zero => exact False.elim (Nat.not_succ_le_zero 0 hlevel)
    | succ n =>
      letI : FiniteDimensional (Padic C.l) E := hE
      let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
      dsimp only [relativeCartierProLine, frameTwist, frameTwistEtale, Coefficient, Ring,
        coefficientCommRing, ringCommRing] at q ⊢
      exact Scheme.IsFiniteTateSiteComparison C.l E n T n Q.diagonalExponent_annihilates 1 q

```

```lean
@[no_expose] def relativeCartierProExt (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Ext
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))
      (P.relativeCartierProLine T) 2 := by
  have hT : IsUnit (P.coefficients.l : Γ(T, ⊤)) :=
    (isUnit_pow_iff (Nat.ne_zero_of_lt P.level_pos)).mp
      (by simpa only [diagonalExponent, Nat.cast_pow] using P.diagonalExponent_isUnit a)
  exact (P.relativeCartierProExt_type i).mp
    ((Etale.cartier_kummer_map P.coefficients.l P.extension).2.exists.choose.2
      (P.level - 1) i hI hT)
```

## New

```lean
@[no_expose] def RelativeCartierRootNormalized (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (q : P.frameTwist T 1 ≅ P.relativeCartierProLine T) : Prop :=
  match P with
  | @PurityFiniteSetting.mk _ _ _ _ 0 hlevel =>
    False.elim (Nat.not_succ_le_zero 0 hlevel)
  | @PurityFiniteSetting.mk F C E hE (n + 1) hlevel => by
    letI : FiniteDimensional (Padic C.l) E := hE
    let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
    dsimp only [relativeCartierProLine, frameTwist, frameTwistEtale, Coefficient, Ring,
      coefficientCommRing, ringCommRing] at q ⊢
    exact Scheme.IsFiniteTateSiteComparison C.l E n T n Q.diagonalExponent_annihilates 1 q

```

```lean
@[no_expose] def relativeCartierProExt (P : PurityFiniteSetting.{u}) {D T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) (i : D ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) : Ext
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))
      (P.relativeCartierProLine T) 2 :=
  match P with
  | @PurityFiniteSetting.mk _ _ _ _ 0 hlevel =>
    False.elim (Nat.not_succ_le_zero 0 hlevel)
  | @PurityFiniteSetting.mk F C E hE (n + 1) hlevel => by
    letI : FiniteDimensional (Padic C.l) E := hE
    let Q : PurityFiniteSetting.{u} := @PurityFiniteSetting.mk F C E hE (n + 1) hlevel
    have hT : IsUnit (C.l : Γ(T, ⊤)) :=
      (isUnit_pow_iff (Nat.succ_ne_zero n)).mp
        (by simpa only [diagonalExponent, Nat.cast_pow] using Q.diagonalExponent_isUnit a)
    unfold relativeCartierProLine
    dsimp only [Coefficient, Ring, coefficientCommRing, ringCommRing]
    have c := (Etale.cartier_kummer_map C.l E).2.exists.choose.2 n i hI hT
    unfold Etale.cartierSupported at c
    exact c
```

Three original theorem holes are filled. The unused relativeCartierProExt_type
presentation theorem is removed: the direct successor definition no longer uses it.
No external consumer exists, and the mathematical realization statements are retained.
No new public declaration or hole is introduced. Retained signatures are identical.

The removed declaration was:

```lean
/-- The canonical positive-level coefficient reindexing identifies the two Ext types.
Source: def-pur-conventions and the predecessor convention in lem-amb-cartier-kummer-map
(blueprint: lem-pur-cartier-relative-kummer-realization).
Proof: write P.level=m+1 using P.level_pos. Unfold the positive branch of
relativeCartierProLine and finiteTateCoefficient, and unfold Coefficient and Ring.
Both sides are then the same Ext type for the same standard size lift of the
coefficient quotient, with its existing ring and HasExt structures. Reflexivity
proves the equality. This is only a change of presentation of that fixed type. -/
theorem relativeCartierProExt_type (P : PurityFiniteSetting.{u})
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    Ext (Etale.cartierSupported P.coefficients.l P.extension (P.level - 1) i)
      (Scheme.finiteTateProSheaf P.coefficients.l P.extension (P.level - 1) T 1) 2 =
    Ext
      ((ProEtale.lowerStar (ModuleCat.{u + 1} P.Coefficient) i).obj
        ((constantSheaf (Scheme.ProEt.topology D) (ModuleCat.{u + 1} P.Coefficient)).obj
          (ModuleCat.of P.Coefficient P.Coefficient)))
      (P.relativeCartierProLine T) 2 := by
  induction P using positive_induction with
  | h F C E hE n hlevel =>
    let : FiniteDimensional (Padic C.l) E := hE
    unfold relativeCartierProLine Etale.cartierSupported
    rfl
```

Its equality is definitionally true on each successor branch and was checked in
focused proofs. Its whole-type kernel comparison is unnecessary once the definition
selects the published class directly. This prunes a presentation obligation; it is
not counted as a proved theorem.

## Users

For each of relativeCartierProExt and RelativeCartierRootNormalized,
tools/downstream.py reports zero downstream modules; the only textual use is the
item module itself. The table also records the surrounding agreement interface.

Source search and tools/downstream.py identify these consumers. CartierClassAgreement is held by B7; the other consumers were unclaimed at inspection. CartierClassAgreement itself
is not changed; its original definition is handled by proof-local transparency. No consumer needs adaptation:
all public types and the chosen data on each positive coefficient branch are the same.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CartierClassAgreement | B7 | Unchanged dependency. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | Three holes filled; unused Ext type presentation pruned; equivalent Ext presentation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Public API unchanged; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | unclaimed | Public API unchanged; no adaptation. |

No target statement is changed. This definitional presentation repair does not change
the meaning of a target; the independent reader can inspect the same class selection
in the two displayed successor branches.

## Status

landed 20261025T201454-L-2533881 2026-10-25 (merge of deliver/B8/Sheaf.Paper.CartierRelativeKummerRealization)
