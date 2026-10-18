# AlgebraicGeometry.Scheme.koszulQuotientLimit

## Reason

The stage-3 preflight requires a change record for added commands such as `open`
and `variable`, although this delivery leaves the existing theorem signature,
visibility, definitions and public imports unchanged. The added
`open CochainComplex CochainComplex.HomComplex` supports the proved private cocone
helpers. The new `Cone` section declares its own universes and category variables;
that section ends before the existing public theorem. Proof elaboration options
are local to the new helpers and existing theorem. No new global instance or
notation is installed, and no existing public data definition is changed.

The item is held by Y2. The two new modules are nodes of the decomposition, not
adaptations of existing modules. This record documents the static interface flag;
it does not change a definition or a target statement.

## Old

The existing public signature, verbatim:

```lean
theorem koszulQuotientLimit (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (v : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) (n : ℕ),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulTensor X Λ r f M.complex n) (adicReductionComplex X d M n))
      (w : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulCompletionComplex X Λ r f M.complex) (adicCompletionComplex X d M))
      (c : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        intrinsicKoszulCompletion X Λ d r f hf K M.complex M.isKFlat M.realization ≅
          adicCompletionObject X d M),
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), koszulTensorUnit X Λ r f M.complex n ≫ v K M n =
        adicReductionAugmentation X d M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ) p q (p + q) rfl ≫ (v K M n).f (p + q) = 0) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), v K M (n + 1) ≫ adicReductionComplexStep X d M n =
        koszulTensorTransition X Λ r f M.complex n ≫ v K M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), w K M ≫ adicCompletionProjection X d M =
        CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
          Limits.Pi.map (v K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (p : ℤ), (w K M).f p ≫
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd
          (koszulOneSubShift X Λ r f M.complex)).v p (p + -1) rfl ≫
            (Limits.Pi.map (v K M)).f (p + -1)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), (c K M).hom = (adicLocalization X Λ).map (w K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), intrinsicKoszulCompletionUnit X Λ d r f hf K M.complex
        M.isKFlat M.realization ≫ (c K M).hom = adicCompletionMap X d M) ∧
      (∀ (K L : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L)
        (g : M.complex ⟶ N.complex)
        (τ : ∀ n : ℕ, koszulTensor X Λ r f M.complex n ⟶
          koszulTensor X Λ r f N.complex n)
        (σ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
        (a : koszulCompletionComplex X Λ r f M.complex ⟶
          koszulCompletionComplex X Λ r f N.complex)
        (b : adicCompletionComplex X d M ⟶ adicCompletionComplex X d N),
        (∀ n, τ n = HomologicalComplex.mapBifunctorMap g
          (𝟙 (koszulPowerSheaf X Λ r f n))
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ)) →
        (∀ n, adicReductionAugmentation X d M n ≫ σ n =
          g ≫ adicReductionAugmentation X d N n) →
        a ≫ CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f N.complex) =
          CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
            Limits.Pi.map τ →
        (∀ p : ℤ, a.f p ≫
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f N.complex)).v
            p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v
            p (p + -1) rfl ≫ (Limits.Pi.map τ).f (p + -1)) →
        b ≫ adicCompletionProjection X d N =
          adicCompletionProjection X d M ≫ Limits.Pi.map σ →
        (∀ p : ℤ, b.f p ≫ (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d N)).v p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl ≫
              (Limits.Pi.map σ).f (p + -1)) →
        (c K M).hom ≫ (adicLocalization X Λ).map b =
          (adicLocalization X Λ).map a ≫ (c L N).hom)
```

## New

The public signature is identical, verbatim:

```lean
theorem koszulQuotientLimit (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) :
    ∃ (v : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K) (n : ℕ),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulTensor X Λ r f M.complex n) (adicReductionComplex X d M n))
      (w : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        @Quiver.Hom (CochainComplex
          (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) inferInstance
          (koszulCompletionComplex X Λ r f M.complex) (adicCompletionComplex X d M))
      (c : ∀ (K : proEtaleDerivedCategory X Λ) (M : AdicKFlatModel X Λ K),
        intrinsicKoszulCompletion X Λ d r f hf K M.complex M.isKFlat M.realization ≅
          adicCompletionObject X d M),
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), koszulTensorUnit X Λ r f M.complex n ≫ v K M n =
        adicReductionAugmentation X d M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ) (p q : ℤ) (hq : q ≠ 0),
        HomologicalComplex.ιMapBifunctor M.complex (koszulPowerSheaf X Λ r f n)
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ) p q (p + q) rfl ≫ (v K M n).f (p + q) = 0) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (n : ℕ), v K M (n + 1) ≫ adicReductionComplexStep X d M n =
        koszulTensorTransition X Λ r f M.complex n ≫ v K M n) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), w K M ≫ adicCompletionProjection X d M =
        CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
          Limits.Pi.map (v K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (p : ℤ), (w K M).f p ≫
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl =
        (CochainComplex.mappingCocone.snd
          (koszulOneSubShift X Λ r f M.complex)).v p (p + -1) rfl ≫
            (Limits.Pi.map (v K M)).f (p + -1)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), (c K M).hom = (adicLocalization X Λ).map (w K M)) ∧
      (∀ (K : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K), intrinsicKoszulCompletionUnit X Λ d r f hf K M.complex
        M.isKFlat M.realization ≫ (c K M).hom = adicCompletionMap X d M) ∧
      (∀ (K L : proEtaleDerivedCategory X Λ)
        (M : AdicKFlatModel X Λ K) (N : AdicKFlatModel X Λ L)
        (g : M.complex ⟶ N.complex)
        (τ : ∀ n : ℕ, koszulTensor X Λ r f M.complex n ⟶
          koszulTensor X Λ r f N.complex n)
        (σ : ∀ n : ℕ, adicReductionComplex X d M n ⟶ adicReductionComplex X d N n)
        (a : koszulCompletionComplex X Λ r f M.complex ⟶
          koszulCompletionComplex X Λ r f N.complex)
        (b : adicCompletionComplex X d M ⟶ adicCompletionComplex X d N),
        (∀ n, τ n = HomologicalComplex.mapBifunctorMap g
          (𝟙 (koszulPowerSheaf X Λ r f n))
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (adicConstantRing X Λ)))
          (ComplexShape.up ℤ)) →
        (∀ n, adicReductionAugmentation X d M n ≫ σ n =
          g ≫ adicReductionAugmentation X d N n) →
        a ≫ CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f N.complex) =
          CochainComplex.mappingCocone.fst (koszulOneSubShift X Λ r f M.complex) ≫
            Limits.Pi.map τ →
        (∀ p : ℤ, a.f p ≫
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f N.complex)).v
            p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd (koszulOneSubShift X Λ r f M.complex)).v
            p (p + -1) rfl ≫ (Limits.Pi.map τ).f (p + -1)) →
        b ≫ adicCompletionProjection X d N =
          adicCompletionProjection X d M ≫ Limits.Pi.map σ →
        (∀ p : ℤ, b.f p ≫ (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d N)).v p (p + -1) rfl =
          (CochainComplex.mappingCocone.snd
            (𝟙 _ - adicReductionProductShift X d M)).v p (p + -1) rfl ≫
              (Limits.Pi.map σ).f (p + -1)) →
        (c K M).hom ≫ (adicLocalization X Λ).map b =
          (adicLocalization X Λ).map a ≫ (c L N).hom)
```

Its proof constructs the explicit product-cocone map and proves the unit and
naturality formulas from the two new intermediate statements. All new helpers in
this existing module are private and proved. The new public theorems and their
remaining holes are listed in report.md and their matching DAG nodes.

## Users

`python3 tools/downstream.py Sheaf.Paper.KoszulQuotientLimit --uses
koszulQuotientLimit` lists one downstream module and lists the item itself as the
only textual user of the declaration. Neither requires an adaptation because the
existing signature, public imports and definitions are byte-for-byte unchanged.
The group field below uses the shared queue snapshot at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.KoszulQuotientLimit | Y2 | Proof replaced; private helpers and local commands added; existing signature unchanged. |
| Sheaf.Paper.AdicCompletionReduction | unclaimed in queue snapshot | No change to its imported public declarations; no adaptation. |

## Status

landed 20261018T071243-L-1683621 2026-10-18 (merge of deliver/Y2/Sheaf.Paper.KoszulQuotientLimit)
