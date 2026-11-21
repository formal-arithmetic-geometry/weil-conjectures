/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LocalizingConstructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing

/-!
# Comparison of the étale and pro-étale localizing categories

Let `Λ` be a finite ring and `ν^* : D(X_ét, Λ) ⥤ D(X_proét, Λ)` the comparison functor on
unbounded derived categories, induced by the exact comparison pullback.

## Main definitions and statements

- `AlgebraicGeometry.ProEtale.preservesColimitsOfShape_mapDerivedCategory_comparisonUpperStar`:
  `ν^*` preserves direct sums, for any scheme `X` and any commutative ring `Λ`.
- `AlgebraicGeometry.ProEtale.localizingConstructibleFiniteTorComparison`: the restriction
  `Loc(Dctf(X_ét, Λ)) ⥤ Loc(Dctf(X_proét, Λ))` of `ν^*`.
- `AlgebraicGeometry.ProEtale.isEquivalence_localizingConstructibleFiniteTorComparison`: it is an
  equivalence, for a finite `ℓ`-primary ring `Λ` and a scheme `X` of finite type over a field `k`
  which is finite or algebraically closed and in which `ℓ` is invertible.

## Implementation details

The functor `ν^*` is triangulated, preserves direct sums and is fully faithful on unbounded
complexes (`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedComparison_fullyFaithful`). The
essential image of its restriction to `Loc(Dctf(X_ét, Λ))` is therefore a localizing subcategory;
it contains `Dctf(X_proét, Λ)`, whose objects are by definition of the form `ν^* G` with `G` in
`Dctf(X_ét, Λ)`, hence also `Loc(Dctf(X_proét, Λ))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

section Coproducts

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The comparison functor `ν^* : D(X_ét, Λ) ⥤ D(X_proét, Λ)` preserves direct sums, for any
scheme `X` and any commutative ring `Λ`. -/
instance preservesColimitsOfShape_mapDerivedCategory_comparisonUpperStar (J : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete J) D(ν^*(X)[ModuleCat.{u + 1} Λ]) :=
  have : PreservesColimitsOfShape (Discrete J) ν^*(X)[ModuleCat.{u + 1} Λ] :=
    (comparisonAdjunction (ModuleCat.{u + 1} Λ) X).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  inferInstance

end Coproducts

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})

/-- `ν^*` maps `Loc(Dctf(X_ét, Λ))` into `Loc(Dctf(X_proét, Λ))`. -/
theorem localizingConstructibleFiniteTor_mapDerivedCategory_comparisonUpperStar
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
      K) :
    DerivedCategory.localizingConstructibleFiniteTor Λ X (D(ν^*(X)[ModuleCat.{u + 1} Λ]).obj K) :=
  ObjectProperty.localizingClosure_le_inverseImage _ _
    (fun _ hG ↦ ObjectProperty.le_localizingClosure _ _
      (DerivedCategory.constructibleFiniteTor_mapDerivedCategory Λ hG)) K hK

/-- The comparison functor `ν^* : Loc(Dctf(X_ét, Λ)) ⥤ Loc(Dctf(X_proét, Λ))`, the restriction of
`ν^* : D(X_ét, Λ) ⥤ D(X_proét, Λ)` to the localizing closures. -/
noncomputable abbrev localizingConstructibleFiniteTorComparison :
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ)
      X).localizingClosure.FullSubcategory ⥤ DerivedCategoryLocalizingFiniteTor Λ X :=
  ObjectProperty.localizingClosureLift _ _ D(ν^*(X)[ModuleCat.{u + 1} Λ])
    (localizingConstructibleFiniteTor_mapDerivedCategory_comparisonUpperStar Λ X)

/-- `ν^* : D(X_ét, Λ) ⥤ D(X_proét, Λ)` is fully faithful on unbounded complexes, for a finite
`ℓ`-primary ring `Λ` and a scheme `X` of finite type over a field `k` which is finite or
algebraically closed and in which `ℓ` is invertible. -/
theorem nonempty_fullyFaithful_mapDerivedCategory_comparisonUpperStar (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ))) (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    Nonempty D(ν^*(X)[ModuleCat.{u + 1} Λ]).FullyFaithful := by
  let : TopologicalSpace Λ := ⊥
  have : DiscreteTopology Λ := ⟨rfl⟩
  obtain ⟨-, ⟨h⟩, -⟩ := finiteCoefficientDerivedComparison_fullyFaithful.{u, u + 1} k hk hℓ Λ hΛ X
  exact ⟨(h.ofIso (Functor.mapDerivedCategoryCompIso (comparisonUpperStar (ModuleCat.{u + 1} Λ) X)
    (finiteCoefficientRealization X Λ)).symm).ofCompFaithful⟩

/-- **Comparison of localizing categories.** For a finite `ℓ`-primary ring `Λ` and a scheme `X` of
finite type over a field `k` which is finite or algebraically closed and in which `ℓ` is
invertible, `ν^*` identifies `Loc(Dctf(X_ét, Λ))` with `Loc(Dctf(X_proét, Λ))`. -/
theorem isEquivalence_localizingConstructibleFiniteTorComparison (k : Type u) [Field k]
    (hk : Finite k ∨ IsAlgClosed k) {ℓ : ℕ} [Fact ℓ.Prime]
    (hℓ : IsUnit (algebraMap ℤ k (ℓ : ℤ))) (hΛ : ∃ n : ℕ, (ℓ : Λ) ^ n = 0)
    [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    (localizingConstructibleFiniteTorComparison Λ X).IsEquivalence := by
  obtain ⟨h⟩ := nonempty_fullyFaithful_mapDerivedCategory_comparisonUpperStar Λ X k hk hℓ hΛ
  let P := (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X).localizingClosure
  let Q := DerivedCategory.localizingConstructibleFiniteTor Λ X
  let e := ObjectProperty.localizingClosureLiftCompιIso _ _ D(ν^*(X)[ModuleCat.{u + 1} Λ])
    (localizingConstructibleFiniteTor_mapDerivedCategory_comparisonUpperStar Λ X)
  have hff : (localizingConstructibleFiniteTorComparison Λ X).FullyFaithful :=
    Functor.FullyFaithful.ofCompFaithful (G := Q.ι)
      ((P.fullyFaithfulι.comp h).ofIso e.symm)
  have := hff.full
  have := hff.faithful
  -- the essential image of `P.ι ⋙ ν^*` is localizing and contains `Dctf(X_proét, Λ)`
  have : (P.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).essImage.IsLocalizing :=
    have := (P.fullyFaithfulι.comp h).full
    have := (P.fullyFaithfulι.comp h).faithful
    { isClosedUnderColimitsOfShape_discrete := fun _ ↦ inferInstance }
  have hQ : Q ≤ (P.ι ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ])).essImage :=
    ObjectProperty.localizingClosure_le fun K hK ↦ by
      obtain ⟨⟨G, hG, ⟨e⟩⟩, a, b, hab⟩ := hK
      exact ⟨⟨G, ObjectProperty.le_localizingClosure _ _ ⟨hG, a, b,
        (DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
          ((DerivedCategory.torAmplitudeIn _ X a b).prop_of_iso e.symm hab)⟩⟩, ⟨e⟩⟩
  have : (localizingConstructibleFiniteTorComparison Λ X).EssSurj := ⟨fun K ↦ by
    obtain ⟨G, ⟨e⟩⟩ := hQ K.obj K.property
    exact ⟨G, ⟨Q.fullyFaithfulι.preimageIso e⟩⟩⟩
  exact { }

end AlgebraicGeometry.ProEtale
