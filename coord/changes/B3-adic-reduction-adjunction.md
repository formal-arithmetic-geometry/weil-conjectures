# AlgebraicGeometry.Scheme.adicReductionHomEquiv and its scalar-reduction API

## Reason

The Koszul scalar comparison needs the already proved derived scalar-reduction
adjunction, while AdicCompletionReduction now proves its remaining theorem using
that comparison. Extracting the adjunction avoids an import cycle. This is a
relocation with unchanged signatures and bodies, not a mathematical definition
change. The old module publicly imports the new module, preserving its public API.
The four additional map laws are proved from this adjunction.

## Old

These declarations were in Sheaf.Paper.AdicCompletionReduction:

```lean
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ))

noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A

noncomputable def adicDerivedRestrictFactors (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    (adicDerivedRestrict X φ).obj ((adicLocalization X B).obj P) ≅
      (adicLocalization X A).obj (adicRestrict X φ P)

noncomputable def adicReductionDerivedUnit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ) :
    L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj
      (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩)

theorem adicReductionAdjunction_homEquiv_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    ∃ e : (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H),
      ∀ f, e f = adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f

theorem adicReductionAdjunction_bijective (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    Function.Bijective (fun f : adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H ↦
      adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f)

noncomputable def adicReductionHomEquiv (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H)

noncomputable def adicReductionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K') (n : ℕ) (f : K ⟶ K') :
    adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M' ⟨n + 1, Nat.succ_pos n⟩
```

## New

The signatures in Sheaf.Paper.AdicReductionAdjunction are:

```lean
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ))

noncomputable def adicDerivedRestrict (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    proEtaleDerivedCategory X B ⥤ proEtaleDerivedCategory X A

noncomputable def adicDerivedRestrictFactors (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    (P : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ) :
    (adicDerivedRestrict X φ).obj ((adicLocalization X B).obj P) ≅
      (adicLocalization X A).obj (adicRestrict X φ P)

noncomputable def adicReductionDerivedUnit (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ) :
    L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj
      (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩)

theorem adicReductionAdjunction_homEquiv_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    ∃ e : (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H),
      ∀ f, e f = adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f

theorem adicReductionAdjunction_bijective (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    Function.Bijective (fun f : adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H ↦
      adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f)

noncomputable def adicReductionHomEquiv (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H)

noncomputable def adicReductionMap (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K') (n : ℕ) (f : K ⟶ K') :
    adicReduction X d M ⟨n + 1, Nat.succ_pos n⟩ ⟶
      adicReduction X d M' ⟨n + 1, Nat.succ_pos n⟩
```

Their complete bodies are unchanged. The original module has
`public import Sheaf.Paper.AdicReductionAdjunction`. The new module adds proved
adicReductionMap_unit, adicReductionMap_comp, adicReductionMap_id and
adicReductionMap_isIso. No existing declaration changes meaning, including every
target of Challenge.lean. No second statement review is required by a semantic
change: there is none.

## Users

The downstream --uses searches for the relocated API found no external users.
The item itself uses these declarations through its new public import.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletionReduction | B3 | Publicly imports relocated API; proves its old hole. |
| Sheaf.Paper.AdicReductionAdjunction | B3 (new) | Hosts the unchanged adjunction API and proved map laws. |
| Sheaf.Paper.KoszulCompletionScalarComparison | B3 (new) | Uses the scalar-reduction API in its statement. |

## Status

landed 20261018T134652-L-2769636 2026-10-18 (merge of deliver/B3/Sheaf.Paper.AdicCompletionReduction)
