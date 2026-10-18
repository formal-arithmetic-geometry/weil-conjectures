# Sheaf.Paper.AdicCompletionReduction

## Reason

The new proof-only import of `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
provides two already proved generic adjunction helpers. That module also registers
`WeilConjectures.scalarReductionSiteSmall`, a specialized site-size instance with an
additional coefficient universe. In this module's existing signatures and proofs it causes
stuck universe constraints `t + 1 = max (t + 1) ?u`.

The five theorem commands below temporarily exclude that instance using the command-scoped
`attribute [-instance] ... in` form. The exclusion ends after each theorem command. It does
not remove an instance from the exported environment, change any existing signature or
definition, or alter target meanings. The static preflight requested this record because it
classifies top-level attribute commands conservatively as interface changes.

## Old

These signatures appeared without the scoped attribute exclusion; each is quoted verbatim:

```lean
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
```

```lean
private theorem adicDerivedRestrictFactors_naturality (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ}
    (f : P ⟶ Q) :
    (adicLocalization X A).map
        (((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) ≫ (adicDerivedRestrictFactors X φ Q).inv =
      (adicDerivedRestrictFactors X φ P).inv ≫
        (adicDerivedRestrict X φ).map ((adicLocalization X B).map f) := by
```

```lean
theorem adicReductionAdjunction_homEquiv_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    ∃ e : (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H),
      ∀ f, e f = adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f := by
```

```lean
theorem adicDerivedRestrict_reflectsIsomorphisms (X : Scheme.{t})
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∀ {Y Z : proEtaleDerivedCategory X B} (f : Y ⟶ Z),
      IsIso ((adicDerivedRestrict (X := X) (A := A) (B := B) φ).map f) → IsIso f := by
```

```lean
private theorem adicReductionAugmentation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionAugmentation X d M n ≫ adicReductionComplexMap X d M M' f n =
      f ≫ adicReductionAugmentation X d M' n := by
```

## New

The signatures are identical. Each theorem command is now wrapped as follows (the other
existing `set_option ... in` and documentation commands remain inside the same scope):

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
theorem adicRestrictScalars_exact (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)) := by
```

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem adicDerivedRestrictFactors_naturality (X : Scheme.{t}) {A B : Type t}
    [CommRing A] [CommRing B] (φ : A →+* B)
    {P Q : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X B)) ℤ}
    (f : P ⟶ Q) :
    (adicLocalization X A).map
        (((SheafOfModules.restrictScalars.{t + 1} (adicModuleMap X φ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) ≫ (adicDerivedRestrictFactors X φ Q).inv =
      (adicDerivedRestrictFactors X φ P).inv ≫
        (adicDerivedRestrict X φ).map ((adicLocalization X B).map f) := by
```

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
theorem adicReductionAdjunction_homEquiv_exists (X : Scheme.{t}) {Λ : Type t} [CommRing Λ]
    (d : CompleteCoefficientDatum Λ) {L : proEtaleDerivedCategory X Λ}
    (N : AdicKFlatModel X Λ L) (n : ℕ)
    (H : proEtaleDerivedCategory X (Λ ⧸ d.ideal ^ (n + 1))) :
    ∃ e : (adicReduction X d N ⟨n + 1, Nat.succ_pos n⟩ ⟶ H) ≃
      (L ⟶ (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).obj H),
      ∀ f, e f = adicReductionDerivedUnit X d N n ≫
        (adicDerivedRestrict X (Ideal.Quotient.mk (d.ideal ^ (n + 1)))).map f := by
```

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
theorem adicDerivedRestrict_reflectsIsomorphisms (X : Scheme.{t})
    {A B : Type t} [CommRing A] [CommRing B] (φ : A →+* B) :
    ∀ {Y Z : proEtaleDerivedCategory X B} (f : Y ⟶ Z),
      IsIso ((adicDerivedRestrict (X := X) (A := A) (B := B) φ).map f) → IsIso f := by
```

```lean
attribute [-instance] WeilConjectures.scalarReductionSiteSmall in
private theorem adicReductionAugmentation_naturality (X : Scheme.{t})
    {Λ : Type t} [CommRing Λ] (d : CompleteCoefficientDatum Λ)
    {K K' : proEtaleDerivedCategory X Λ}
    (M : AdicKFlatModel X Λ K) (M' : AdicKFlatModel X Λ K')
    (f : M.complex ⟶ M'.complex) (n : ℕ) :
    adicReductionAugmentation X d M n ≫ adicReductionComplexMap X d M M' f n =
      f ≫ adicReductionAugmentation X d M' n := by
```

## Users

`python3 tools/downstream.py Sheaf.Paper.AdicCompletionReduction --uses` with all five
declaration names reports zero downstream modules in the shared source snapshot. This is an
item opened through its parent's declared proof dependency; that parent need not import it yet.
No consumer or target adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicCompletionReduction | D4 | Five command-local instance exclusions; identical declaration signatures and definition bodies. |

## Status

landed 20261018T102313-L-4076185 2026-10-18 (merge of deliver/D4/Sheaf.Paper.AdicCompletionReduction)
