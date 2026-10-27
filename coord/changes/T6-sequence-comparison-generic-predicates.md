# SequenceKInjectiveComparison shared generic comparison predicates

## Reason

The concrete coefficient categories contain large sheafification and localization terms.
Repeated specialization of the same identities costs substantial kernel checking time. Factor
these formulas through predicates parameterized by an exact additive functor `F` and an additive
functor `G`; instantiate them with coefficient restriction and inverse limit. Each predicate
has the same quantifiers and equations as before. This is a definitional refactoring, with
canonical termwise shift structures and no extra assumptions in the specialization.

The existing `replacementIso` definition is preserved verbatim. The generic `comparisonIso`
is the same three-isomorphism composite.
`restrictedMapFor` is the same transport through exact localization. The public generic
predicate definitions and their private complete proofs remain in the one item module.
No proof is split into another module and no new hole is introduced.

## Old

### Normalization

```lean
def Normalization
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  (∀ N : CochainComplex (coefficientSequenceModules l E W) ℤ,
    η.app N ≫ κ.hom.app (DerivedCategory.Q.obj N) =
      limitUnit l E W ((restrict l E W).obj N) ≫
        (coefficientConstantTowerLimit l E W).map ((restrictionFactors l E W).inv.app N)) ∧
  ∀ (I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (j : (restrict l E W).obj I ⟶ J) [QuasiIso j],
    QuasiIso ((limitComplex l E W).map j) ∧
      η.app I ≫ κ.hom.app (DerivedCategory.Q.obj I) ≫
        (replacementIso l E W I J j).hom =
          DerivedCategory.Q.map ((limitComplex l E W).map j)
```

### ArbitraryReplacement

```lean
def ArbitraryReplacement
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  ∀ (N I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v],
    ∃ b : (HomotopyCategory.quotient _ (.up ℤ)).obj ((restrict l E W).obj I) ⟶
      (HomotopyCategory.quotient _ (.up ℤ)).obj J,
      (∀ b' : (HomotopyCategory.quotient _ (.up ℤ)).obj ((restrict l E W).obj I) ⟶
          (HomotopyCategory.quotient _ (.up ℤ)).obj J,
        (HomotopyCategory.quotient _ (.up ℤ)).map ((restrict l E W).map i) ≫ b' =
          (HomotopyCategory.quotient _ (.up ℤ)).map v ↔ b' = b) ∧
      ∀ β : (restrict l E W).obj I ⟶ J,
        (HomotopyCategory.quotient _ (.up ℤ)).map β = b →
        QuasiIso β ∧ QuasiIso ((limitComplex l E W).map β) ∧
          η.app I ≫ inv (RP.map (DerivedCategory.Q.map i)) ≫
            κ.hom.app (DerivedCategory.Q.obj N) ≫ (replacementIso l E W N J v).hom =
              DerivedCategory.Q.map ((limitComplex l E W).map β)
```

### DerivedNaturality

```lean
def DerivedNaturality : Prop :=
  ∀ (N N' I I' : CochainComplex (coefficientSequenceModules l E W) ℤ)
    [I.IsKInjective] [I'.IsKInjective]
    (i : N ⟶ I) [QuasiIso i] (i' : N' ⟶ I') [QuasiIso i']
    (J J' : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    [J.IsKInjective] [J'.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v]
    (v' : (restrict l E W).obj N' ⟶ J') [QuasiIso v']
    (f : DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N')
    (t : I ⟶ I') (s : J ⟶ J')
    (β : (restrict l E W).obj I ⟶ J) (β' : (restrict l E W).obj I' ⟶ J'),
    DerivedCategory.Q.map i ≫ DerivedCategory.Q.map t = f ≫ DerivedCategory.Q.map i' →
    DerivedCategory.Q.map v ≫ DerivedCategory.Q.map s =
      restrictedMap l E W f ≫ DerivedCategory.Q.map v' →
    Nonempty (Homotopy ((restrict l E W).map i ≫ β) v) →
    Nonempty (Homotopy ((restrict l E W).map i' ≫ β') v') →
    Nonempty (Homotopy (β ≫ s) ((restrict l E W).map t ≫ β')) ∧
      (coefficientSequenceLimit l E W).map f ≫ (replacementIso l E W N' J' v').hom =
        (replacementIso l E W N J v).hom ≫
          DerivedCategory.Q.map ((limitComplex l E W).map s)
```

### ResolutionCocycle

```lean
def ResolutionCocycle : Prop :=
  ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J₀ J₁ J₂ : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    [J₀.IsKInjective] [J₁.IsKInjective] [J₂.IsKInjective]
    (v₀ : (restrict l E W).obj N ⟶ J₀) [QuasiIso v₀]
    (v₁ : (restrict l E W).obj N ⟶ J₁) [QuasiIso v₁]
    (v₂ : (restrict l E W).obj N ⟶ J₂) [QuasiIso v₂]
    (s₀₁ : J₀ ⟶ J₁) (s₁₂ : J₁ ⟶ J₂) (s₀₂ : J₀ ⟶ J₂) (s₀₀ : J₀ ⟶ J₀),
    Nonempty (Homotopy (v₀ ≫ s₀₁) v₁) →
    Nonempty (Homotopy (v₁ ≫ s₁₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₂) v₂) →
    Nonempty (Homotopy (v₀ ≫ s₀₀) v₀) →
    Nonempty (Homotopy (s₀₁ ≫ s₁₂) s₀₂) ∧ Nonempty (Homotopy s₀₀ (𝟙 J₀)) ∧
      (replacementIso l E W N J₀ v₀).hom ≫
        DerivedCategory.Q.map ((limitComplex l E W).map s₀₁) =
          (replacementIso l E W N J₁ v₁).hom ∧
      DerivedCategory.Q.map ((limitComplex l E W).map s₀₁) ≫
        DerivedCategory.Q.map ((limitComplex l E W).map s₁₂) =
          DerivedCategory.Q.map ((limitComplex l E W).map s₀₂) ∧
      DerivedCategory.Q.map ((limitComplex l E W).map s₀₀) = 𝟙 _
```

### SystemResolutionCocycle

```lean
def SystemResolutionCocycle : Prop :=
  ∀ (N I₀ I₁ I₂ : CochainComplex (coefficientSequenceModules l E W) ℤ)
    [I₀.IsKInjective] [I₁.IsKInjective] [I₂.IsKInjective]
    (i₀ : N ⟶ I₀) [QuasiIso i₀] (i₁ : N ⟶ I₁) [QuasiIso i₁]
    (i₂ : N ⟶ I₂) [QuasiIso i₂]
    (t₀₁ : I₀ ⟶ I₁) (t₁₂ : I₁ ⟶ I₂) (t₀₂ : I₀ ⟶ I₂) (t₀₀ : I₀ ⟶ I₀),
    Nonempty (Homotopy (i₀ ≫ t₀₁) i₁) → Nonempty (Homotopy (i₁ ≫ t₁₂) i₂) →
    Nonempty (Homotopy (i₀ ≫ t₀₂) i₂) → Nonempty (Homotopy (i₀ ≫ t₀₀) i₀) →
    Nonempty (Homotopy (t₀₁ ≫ t₁₂) t₀₂) ∧ Nonempty (Homotopy t₀₀ (𝟙 I₀)) ∧
      DerivedCategory.Q.map (((push l E W).mapHomologicalComplex (.up ℤ)).map t₀₁) ≫
        DerivedCategory.Q.map (((push l E W).mapHomologicalComplex (.up ℤ)).map t₁₂) =
          DerivedCategory.Q.map (((push l E W).mapHomologicalComplex (.up ℤ)).map t₀₂) ∧
      DerivedCategory.Q.map (((push l E W).mapHomologicalComplex (.up ℤ)).map t₀₀) = 𝟙 _
```

### RepresentativeShifts

```lean
def RepresentativeShifts : Prop :=
  (∀ (J J' : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : J ⟶ J') (r i : ℤ),
      ((limitComplex l E W).map (j⟦r⟧')).f i =
        ((limitComplex l E W).map j).f (i + r)) ∧
  (∀ (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r i j : ℤ),
    ((limitComplex l E W).obj (J⟦r⟧)).d i j =
      r.negOnePow • ((limitComplex l E W).obj J).d (i + r) (j + r)) ∧
  (∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (J⟦r⟧).IsKInjective ∧
      QuasiIso (((restrict l E W).commShiftIso r).hom.app N ≫ v⟦r⟧')) ∧
  ∀ (N I : CochainComplex (coefficientSequenceModules l E W) ℤ) [I.IsKInjective]
    (i : N ⟶ I) [QuasiIso i]
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v]
    (β : (restrict l E W).obj I ⟶ J),
    Nonempty (Homotopy ((restrict l E W).map i ≫ β) v) → ∀ r : ℤ,
    (I⟦r⟧).IsKInjective ∧ QuasiIso (i⟦r⟧') ∧
      Nonempty (Homotopy
        ((restrict l E W).map (i⟦r⟧') ≫
          ((restrict l E W).commShiftIso r).hom.app I ≫ β⟦r⟧')
        (((restrict l E W).commShiftIso r).hom.app N ≫ v⟦r⟧'))
```

### ReplacementShifts

```lean
def ReplacementShifts : Prop :=
  ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (J : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) [J.IsKInjective]
    (v : (restrict l E W).obj N ⟶ J) [QuasiIso v] (r : ℤ),
    (replacementIso l E W (N⟦r⟧) (J⟦r⟧)
        (((restrict l E W).commShiftIso r).hom.app N ≫ v⟦r⟧')).hom ≫
      DerivedCategory.Q.map (((limitComplex l E W).commShiftIso r).hom.app J) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app ((limitComplex l E W).obj J) =
    (coefficientSequenceLimit l E W).map ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
      ((coefficientSequenceLimit l E W).commShiftIso r).hom.app (DerivedCategory.Q.obj N) ≫
        (replacementIso l E W N J v).hom⟦r⟧'
```

## New

### Normalization

```lean
def Normalization
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  NormalizationFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) RP η κ
```

### ArbitraryReplacement

```lean
def ArbitraryReplacement
    (RP : coefficientSequenceDerived l E W ⥤ DerivedCategory (scalarReductionSource l E W))
    (η : (push l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RP) (κ : RP ≅ coefficientSequenceLimit l E W) : Prop :=
  ArbitraryReplacementFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) RP η κ
```

### DerivedNaturality

```lean
def DerivedNaturality : Prop :=
  DerivedNaturalityFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

### ResolutionCocycle

```lean
def ResolutionCocycle : Prop :=
  ResolutionCocycleFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

### SystemResolutionCocycle

```lean
def SystemResolutionCocycle : Prop :=
  SystemResolutionCocycleFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

### RepresentativeShifts

```lean
def RepresentativeShifts : Prop :=
  RepresentativeShiftsFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

### ReplacementShifts

```lean
def ReplacementShifts : Prop :=
  ReplacementShiftsFor (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W)
```

The new generic constructions are `comparisonIso` and `restrictedMapFor`. The predicates
are `NormalizationFor`, `ArbitraryReplacementFor`, `DerivedNaturalityFor`,
`ResolutionCocycleFor`, `SystemResolutionCocycleFor`, `RepresentativeShiftsFor`, and
`ReplacementShiftsFor`. Their formulas are the old formulas with `F` for coefficient
restriction, `G` for inverse limit, and their canonical termwise/localization/derived
constructions substituted for the concrete abbreviations. All have the same source and
blueprint attachment as the existing comparison node.

The existing theorem statement and its hypotheses are unchanged. Its meaning is unchanged:
none of these predicates packages a proof or adds an assumption. Targets that transitively
use them are subject to the project's ordinary independent definition review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SequenceKInjectiveComparisonShifts | T6 | Proves the unchanged comparison by specializing generic calculations. |
| Sheaf.Paper.PurSequenceComparisonTranspose | unclaimed | Reads the same two normalization clauses. |
| Sheaf.Paper.PurSequenceDerivedNormalization | unclaimed | Forced proof adaptation: explicitly unfold the same comparison factors in its final model equality. |
| Sheaf.Paper.PurSequenceProjectionHomNormalization | unclaimed | Transitive consumer of the unchanged model and theorem. |
| Sheaf.SixFunctors.BasicRealizationShiftSquare | unclaimed | Uses the unchanged direct image and comparison theorem. |

The current downstream scan lists these four consumers. Consumer compilation results and the necessary proof-only adaptation are recorded in
report.md. In `PurSequenceDerivedNormalization`, the final `simpa only` of `composition_model`
adds `replacementIso`, `comparisonIso`, `restrictionFactors`, `limitComplex`, and `coefficientConstantTowerLimit` so the old
and general comparison formulas are unfolded explicitly. All declaration signatures remain
verbatim. The original fails with the comparison type mismatch reproduced in report.md.

## Status

landed 20261025T033956-L-192086 2026-10-25 (merge of deliver/T6/Sheaf.Paper.SequenceKInjectiveComparisonShifts)
