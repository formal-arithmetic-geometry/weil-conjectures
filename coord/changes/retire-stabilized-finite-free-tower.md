# DerivedCategory.exists_model_of_stabilized_finite_free_tower

## Reason

Retirement item `Sheaf.RingTheory.StabilizedFiniteFreeTower` is listed in
`coord/retire-items.tsv`. The adopted source library provides the same theorem as
`CochainComplex.exists_model_of_stabilized_finite_free_tower`. Their signatures
and proofs agree verbatim after the namespace rename. Retire the unused Sheaf
copy and attach node `lem-sc-stabilized-finite-free-tower` to the source theorem.
No source-library file is modified.

## Old

Module `Sheaf.RingTheory.StabilizedFiniteFreeTower`, namespace `DerivedCategory`:

```lean
theorem exists_model_of_stabilized_finite_free_tower (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A) (b : ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ) (α : ∀ k : ℕ, F k ⟶ M)
    (τ : ∀ k : ℕ, F k ⟶ F (k + 1))
    (hupper : ∀ k : ℕ, (F k).IsStrictlyLE b)
    (hfinite : ∀ k : ℕ, ∀ i : ℤ, Module.Free A ((F k).X i) ∧
      Module.Finite A ((F k).X i))
    (hcomm : ∀ k : ℕ, τ k ≫ α (k + 1) = α k)
    (hstable : ∀ k : ℕ, ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso ((τ k).f i))
    (hiso : ∀ k : ℕ, ∀ j : Fin r, ∀ i : ℤ, b + 1 - (k : ℤ) < i → QuasiIsoAt
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map (α k)) i) :
    ∃ (E : CochainComplex (ModuleCat.{u} A) ℤ), E.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free A (E.X i) ∧ Module.Finite A (E.X i)) ∧
      ∃ γ : E ⟶ M, ∀ j : Fin r, QuasiIso
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map γ)
```

## New

The Sheaf module is withdrawn through `deleted.txt`; the delivery tool writes an
empty module. The DAG attachment points to the unchanged adopted source module
`WeilConjectures.RingTheory.StabilizedFiniteFreeTower`, namespace `CochainComplex`:

```lean
theorem exists_model_of_stabilized_finite_free_tower (A : Type u) [CommRing A]
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : ℕ) (f : Fin r → A) (b : ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} A) ℤ) (α : ∀ k : ℕ, F k ⟶ M)
    (τ : ∀ k : ℕ, F k ⟶ F (k + 1))
    (hupper : ∀ k : ℕ, (F k).IsStrictlyLE b)
    (hfinite : ∀ k : ℕ, ∀ i : ℤ, Module.Free A ((F k).X i) ∧
      Module.Finite A ((F k).X i))
    (hcomm : ∀ k : ℕ, τ k ≫ α (k + 1) = α k)
    (hstable : ∀ k : ℕ, ∀ i : ℤ, b + 1 - (k : ℤ) ≤ i → IsIso ((τ k).f i))
    (hiso : ∀ k : ℕ, ∀ j : Fin r, ∀ i : ℤ, b + 1 - (k : ℤ) < i → QuasiIsoAt
      ((Functor.mapHomologicalComplex
        (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
        (ComplexShape.up ℤ)).map (α k)) i) :
    ∃ (E : CochainComplex (ModuleCat.{u} A) ℤ), E.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free A (E.X i) ∧ Module.Finite A (E.X i)) ∧
      ∃ γ : E ⟶ M, ∀ j : Fin r, QuasiIso
        ((Functor.mapHomologicalComplex
          (ModuleCat.extendScalars (algebraMap A (Localization.Away (f j))))
          (ComplexShape.up ℤ)).map γ)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.StabilizedFiniteFreeTower | R2 | Withdrawn duplicate; zero holes. |
| WeilConjectures.RingTheory.StabilizedFiniteFreeTower | unmodified | Retained theorem and proof; receives the DAG attachment. |
| WeilConjectures.RingTheory.FiniteLocalizationFreeModel | unmodified | Already imports and applies the source theorem; compiled unchanged. |

No current Lean module imports the Sheaf copy or refers to its qualified
`DerivedCategory` name. The historical Sheaf consumer listed by the retirement
inventory, `Sheaf.RingTheory.FiniteLocalizationFreeModel`, is already absent.
The only actual consumer uses the source theorem, so no consumer edit is needed.
There is no change to a target statement or definition.

## Status

landed 20261020T135420-L-1821106 2026-10-20 (merge of deliver/R2/Sheaf.RingTheory.StabilizedFiniteFreeTower)
