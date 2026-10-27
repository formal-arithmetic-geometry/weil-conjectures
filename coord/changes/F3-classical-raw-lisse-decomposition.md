# classical_system_raw_lisse_realization

## Reason

The existing conclusion combines finite classical realization, actual finite operations,
coherence, common-stage descent, and restricted fibres. The available dependency theorems
provide the mathematical models but do not directly state all bridges between their Lean
presentations. Isolate four strictly smaller bridges so they can be proved separately.
The parent proves its coherence lifts and restricted-fibre composite explicitly.

## Old

The statement of `WeilConjectures.ClassicalRawLisse.classical_system_raw_lisse_realization`
is unchanged. Its whole proof was `by sorry`. The four helper declarations did not exist.

```lean
theorem classical_system_raw_lisse_realization :
    ∃ (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
      (s : Family D l hl a b) (o : Operations D l hl a b s)
      (h : Coherence D l hl a b s o)
      (c : ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W : PerAdic.Base D.k), Common D l hl W Ω a b s o h.toScalarCoherence),
      (∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (CommonRestriction D l hl W Ω a b s o h.toScalarCoherence V f (c Ω W) (c Ω V))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W : PerAdic.Base D.k), Nonempty (PointComparison D l hl E W a b s)) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (RestrictedFibres D l hl E W a b s V f)) ∧
      (∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
        [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
        (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
        (f : V.scheme ⟶ W.scheme) [IsImmersion f],
          Nonempty (Mixed D l hl E W F a b s o i V f)) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
        Nonempty (LisseRealization.PointNormalized D l hl E
          (a.realization E (LisseRealization.point D l hl)) (a.point E))) ∧
      (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
        Nonempty (LisseRealization.PullNormalized D l hl E f
          (a.realization E X) (a.realization E Y) (a.along E f))) ∧
      (∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
        [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
        (i : E →ₐ[ℚ_[l]] F) (X : LisseRealization.Base D l hl),
        Nonempty (LisseRealization.FieldNormalized D l hl E F i X
          (a.realization E X) (a.realization F X) (a.fieldChange E F i X)))
```
No existing definition, theorem signature, public import, or target is changed.

## New

Four new theorem signatures (section variables D, l and hl have their original types):

- `classical_raw_lisse_finite_construction`: existence of finite realization and point data.
- `classical_raw_lisse_finite_operations`: operations relative to an existing realization.
- `classical_raw_lisse_intrinsic_fibre_pullback`: the intrinsic completed fibre comparison.
- `classical_raw_lisse_common_descent`: common-stage descent of existing finite data.

```lean
theorem classical_raw_lisse_finite_construction
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (hp : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E],
      Nonempty (LisseRealization.PointNormalized D l hl E
        (a.realization E (LisseRealization.point D l hl)) (a.point E)))
    (hr : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
      Nonempty (LisseRealization.PullNormalized D l hl E f
        (a.realization E X) (a.realization E Y) (a.along E f))) :
    ∃ s : Family D l hl a b,
      ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
        (W : PerAdic.Base D.k), Nonempty (PointComparison D l hl E W a b s)
```

```lean
theorem classical_raw_lisse_finite_operations
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b)
    (hr : ∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      {X Y : LisseRealization.Base D l hl} (f : X.scheme ⟶ Y.scheme),
      Nonempty (LisseRealization.PullNormalized D l hl E f
        (a.realization E X) (a.realization E Y) (a.along E f)))
    (hf : ∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
      (i : E →ₐ[ℚ_[l]] F) (X : LisseRealization.Base D l hl),
      Nonempty (LisseRealization.FieldNormalized D l hl E F i X
        (a.realization E X) (a.realization F X) (a.fieldChange E F i X))) :
    Nonempty (Operations D l hl a b s)
```

```lean
theorem classical_raw_lisse_intrinsic_fibre_pullback
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f]
    (x : Spec (.of D.k) ⟶ V.scheme) :
    Nonempty (@rationalDerivedPullback l _ E _ _ _ V.scheme W.scheme f
      (baseInvertible D l hl V) (baseInvertible D l hl W) ⋙
      sfAdicRationalFiber l E V.scheme x ≅ sfAdicRationalFiber l E W.scheme (x ≫ f))
```

```lean
theorem classical_raw_lisse_common_descent
    (a : LisseRealization.Family D l hl) (b : ContinuousRational.Family.{u} l)
    (s : Family D l hl a b) (o : Operations D l hl a b s)
    (h : Coherence D l hl a b s o)
    (hm : ∀ (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
      [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
      (W V : PerAdic.Base D.k) (i : E →ₐ[ℚ_[l]] F)
      (f : V.scheme ⟶ W.scheme) [IsImmersion f],
      Nonempty (Mixed D l hl E W F a b s o i V f)) :
    ∃ c : ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
      (W : PerAdic.Base D.k), Common D l hl W Ω a b s o h.toScalarCoherence,
      ∀ (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
        (W V : PerAdic.Base D.k) (f : V.scheme ⟶ W.scheme) [IsImmersion f],
        Nonempty (CommonRestriction D l hl W Ω a b s o h.toScalarCoherence V f
          (c Ω W) (c Ω V))
```

Each helper is a named public theorem in its own module with a source and full prose proof.
The parent's private helpers prove finite module full faithfulness and all scalar,
restriction, and mixed coherence by fully faithful lifting. Its theorem proof assembles
these with the existing lisse normalization witnesses and constructs restricted fibres.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ClassicalSystemRawLisseRealization | F3 | Imports and combines all four new statements. Its signature and public imports stay identical. |

No other current module imports a new module. No existing consumer needs adaptation,
because no existing public interface changes. New public helpers have no prior consumers.
The target statements and their definitions retain the same meanings.

## Status

landed 20261025T122838-L-1812732 2026-10-25 (merge of deliver/F3/Sheaf.Paper.ClassicalSystemRawLisseRealization)
