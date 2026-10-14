# exists_chart_completed_localizations_d

## Reason

The arbitrary-alpha interface is false: replacing alpha by its negative preserves linearity
and scalar compatibility but contradicts the two generator normalizations in a nonzero chart.
The attempted correction duplicated the existing canonical joint-existence theorem word for
word and was refused at landing. Retire the false theorem and use the existing canonical
statement directly. Its existing proof depended on the false theorem, so it must become the
single named construction hole. This is duplicate consolidation, not mathematical progress.

## Old

```lean
theorem exists_chart_completed_localizations_d
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))
    (alpha : ∀ i, FormalGlueing.localize (f i)
      (FormalGlueing.restrict (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        (completedSectionModule s)) ≃ₗ[A]
      FormalGlueing.restrict (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        (FormalGlueing.extend (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
          (FormalGlueing.piece (f i) (chartSectionModule (q ≫ U.ι) (f i))))) :
    ∃ d : ∀ i, FormalGlueing.extend (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (FormalGlueing.piece (f i) (chartSectionModule (q ≫ U.ι) (f i))) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))),
      (∀ i m, d i (alpha i (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : AdicCompletion (IsLocalRing.maximalIdeal A) A) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ i (z : AdicCompletion (IsLocalRing.maximalIdeal A) A) m, d i (z • m) =
        ((ΓSpecIso (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top : (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
              ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ≤ ⊤)).op).hom z * d i m)
```

## New

The old declaration is removed. The existing canonical theorem has this unchanged signature:

```lean
theorem exists_chart_completed_localizations
    {A : Type u} [CommRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens} {Y : Scheme.{u}} {q : Y ⟶ U.toScheme}
    {E : Scheme.{u}} [IsAffine E] {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))}
    (D : CompletionGluingData A U q E s) (t : ℕ) (f : Fin t → A)
    (hf : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ U)
    (hV : ∀ i, IsAffineOpen ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i))) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let φ := algebraMap A C
    let M' := completedSectionModule s
    let M := fun i ↦ chartSectionModule (q ≫ U.ι) (f i)
    ∃ (alpha : ∀ i,
        FormalGlueing.localize (f i) (FormalGlueing.restrict φ M') ≃ₗ[A]
          FormalGlueing.restrict φ (FormalGlueing.extend φ
            (FormalGlueing.piece (f i) (M i))))
      (d : ∀ i, FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)) ≃+
        Γ(pullback q (completionSpecMap A ∣_ U),
          (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
            ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)))),
      (∀ i (z : C) (x : FormalGlueing.localize (f i) (FormalGlueing.restrict φ M')),
        alpha i ((FormalGlueing.localizedSModule φ (f i) M').smul z x) =
          z • (alpha i x : FormalGlueing.extend φ (FormalGlueing.piece (f i) (M i)))) ∧
      (∀ i m, d i (alpha i (LocalizedModule.mk m 1)) =
        (pullback q (completionSpecMap A ∣_ U)).presheaf.map (homOfLE le_top).op
          (D.toCompleted.appTop m)) ∧
      (∀ i m, d i (TensorProduct.tmul A (1 : C) m) =
        (pullback.fst q (completionSpecMap A ∣_ U)).app _ m) ∧
      (∀ i (z : C) m, d i (z • m) =
        ((ΓSpecIso (.of C)).inv ≫
          (pullback.snd q (completionSpecMap A ∣_ U) ≫
            (completionSpecMap A ⁻¹ᵁ U).ι).appTop ≫
          (pullback q (completionSpecMap A ∣_ U)).presheaf.map
            (homOfLE (le_top :
              (pullback.fst q (completionSpecMap A ∣_ U)) ⁻¹ᵁ
                ((q ≫ U.ι) ⁻¹ᵁ PrimeSpectrum.basicOpen (f i)) ≤ ⊤)).op).hom z * d i m)
```

Its named construction proof is `:= by sorry`, with the existing complete proof docstring
and node `lem-sbc-punctured-completion-chart-completed-localizations`.
The D node now points to this existing declaration instead of introducing a duplicate.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizations | unclaimed | forced: remove the call to the retired false theorem and its two obsolete proof imports; preserve signature and visibility |

The original caller cannot compile against the retired interface: its proof refers to the
removed `exists_chart_completed_localizations_d`. No other source module uses that name.
The original alpha construction is not needed once the joint construction is the canonical
outstanding proof. The canonical docstring gains the retired D node blueprint tag, as required by the node
redirection check. No target statement, definition, instance or visibility is changed.

## Status

landed 20261014T013044-L-3417373 2026-10-14 (merge of deliver/R4/Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionChartCompletedLocalizationsD)
