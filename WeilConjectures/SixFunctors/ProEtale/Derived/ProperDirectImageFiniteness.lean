/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Derived.DirectImageFiniteness
public import WeilConjectures.SixFunctors.ProEtale.Derived.Stability

/-!
# Finiteness of proper direct images on the pro-étale site

Let `Λ` be a finite commutative ring annihilated by an integer invertible in a field `k`, and
let `f : X ⟶ Y` be a proper morphism with `Y` of finite type over `k`, whose geometric fibres
have dimension at most `e`. Then `FIN(f, Λ; 2e)` holds
(`AlgebraicGeometry.ProEtale.directImageFiniteness_of_isProper`, blueprint
`thm-weil-pbc-direct-image-finiteness-proper`).

For a constructible pro-étale sheaf `F ≅ ν^* F'`, the comparison of direct images
(`prop-weil-pbc-comparison-direct-image`) gives `Rᵠf_* ν^* F' ≅ ν^* Rᵠf_* F'`
(`AlgebraicGeometry.ProEtale.rightDerivedComparisonUpperStarObjIso`), and the étale
`Rᵠf_* F'` is constructible and vanishes for `q > 2e` by the classical finiteness theorems.

## Implementation notes

The blueprint states the theorem for noetherian `X`, `Y` of finite dimension, citing SGA 4½,
Th. finitude 1.1 and Stacks 095U for the étale input. The étale finiteness results available in
the project are stated for schemes of finite type over a field (blueprint
`thm-dg-finite-type-constructibility` and `sbc-thm-finiteness-finite-type`, nodes of the
subsection `sk-prop-sf-cbc`), so the theorem is formalised in that setting: `Y` of finite type
over a field `k` in which the order of `Λ` is invertible.

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- For `f` quasi-compact and quasi-separated and an étale sheaf `F'`, the classical pro-étale
direct image `Rᵠf_* (ν^* F')` is `ν^*` of the degree-`q` homology of the étale `Rf_* (F'[0])`:
the comparison of direct images (`prop-weil-pbc-comparison-direct-image`) applied to `F'[0]`,
followed by the exactness of `ν^*`. -/
noncomputable def rightDerivedComparisonUpperStarObjIso
    (F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ) :
    ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q).obj
        ((ν^*(X)[ModuleCat.{u + 1} Λ]).obj F') ≅
      (ν^*(Y)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
        ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F'))) :=
  have hF' : _root_.DerivedCategory.TStructure.t.plus
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F') := ⟨0, inferInstance⟩
  ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).homologyRightDerivedFunctorObjSingleFunctorIso
      _ q).symm ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      ((R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso
        (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app F').symm ≪≫
      rightDerivedLowerStarMapDerivedCategoryObjIso (ModuleCat.{u + 1} Λ) f _ hF') ≪≫
    (((ν^*(Y)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso q).app _).symm

end Comparison

variable [Finite Λ] {k : Type u} [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `thm-weil-pbc-direct-image-finiteness-proper`: Finiteness of proper direct images.

Let `Λ` be a finite ring annihilated by an integer invertible in the field `k`, let `Y` be of
finite type over `k` and let `f : X ⟶ Y` be proper, with geometric fibres of dimension at most
`e`. Then `FIN(f, Λ; 2e)` holds: for every constructible sheaf `F ≅ ν^* F'` on `X_proét`, the
sheaves `Rᵠf_* F ≅ ν^* Rᵠf_* F'` (`prop-weil-pbc-comparison-direct-image`) are constructible,
`Rᵠf_* F'` being constructible (`thm-dg-finite-type-constructibility`), and vanish for
`q > 2e`, since `Rᵠf_* F' ≅ Rᵠf_! F'` vanishes there (`sbc-thm-finiteness-finite-type`).

See the module docstring for the restriction to bases of finite type over a field. -/
theorem directImageFiniteness_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aY] [QuasiCompact aY] (e : ℕ)
    (he : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (e : WithBot ℕ∞)) :
    DirectImageFiniteness Λ f (2 * e) := by
  have : HasCompactification f := (Compactification.ofIsProper f).hasCompactification
  -- reduce to a constructible sheaf of étale origin
  suffices H : ∀ (F' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsConstructibleSheaf F' → ∀ q : ℕ,
        IsConstructibleSheaf ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F'))) ∧
        (2 * e < q → IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
          ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F')))) by
    constructor
    · rintro F ⟨F', hF', ⟨e'⟩⟩ q
      have : IsConstructibleSheaf F' := hF'
      exact (constructibleSheaf Λ Y).prop_of_iso
        ((rightDerivedComparisonUpperStarObjIso f F' q).symm ≪≫
          ((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q).mapIso e')
        (ObjectProperty.prop_map_obj _ _ (H F' this q).1)
    · rintro F ⟨F', hF', ⟨e'⟩⟩ q hq
      have : IsConstructibleSheaf F' := hF'
      exact (((ν^*(Y)[ModuleCat.{u + 1} Λ]).map_isZero ((H F' this q).2 hq)).of_iso
        (rightDerivedComparisonUpperStarObjIso f F' q)).of_iso
        (((ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerived q).mapIso e').symm
  intro F' _ q
  refine ⟨?_, fun hq ↦ ?_⟩
  · exact (Etale.boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType Λ f (f ≫ aY)
      aY rfl _ (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj F' 0)).2 q
  · exact (Etale.isZero_homology_rightDerivedLowerShriek_singleFunctor Λ f (f ≫ aY) aY rfl e he
      F' q (by lia)).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
        ((Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) f).app
          _)).symm

end AlgebraicGeometry.ProEtale
