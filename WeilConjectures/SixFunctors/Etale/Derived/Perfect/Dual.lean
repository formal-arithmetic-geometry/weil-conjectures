/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Hom

/-!
# The coefficient dual of a dualizable étale complex

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme. The
*coefficient dual* of a complex `K ∈ D(X_ét)` is `K^∨ = RHom(K, Λ_X)`. Perfectness is rendered as
dualizability; see `WeilConjectures.SixFunctors.Etale.Derived.Perfect` for the conventions.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`: `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`: the evaluation
  `K ⊗ᴸ K^∨ ⟶ Λ_X`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualIsoOfExactPairing`: `K^∨ ≅ L` for a
  left dual `L` of `K`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`
  (`sk-prop-sf-dualizable-biduality`, `prop-sf-dualizable`)
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual`
  (`sk-prop-sf-dualizable-biduality`)
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`
  (`sk-prop-sf-dualizable-biduality`, `prop-sf-dualizable-hom`)
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_derivedHom_tensor`
  (`sk-lem-sf-twist-interchange`)
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

/-- The coefficient dual `K^∨ = RHom(K, Λ_X)` of a complex of étale sheaves, where `Λ_X` is
the monoidal unit of `D(X_ét)`. -/
noncomputable def coefficientDual :
    (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ ⥤
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (RHom(X)[A]).flip.obj (𝟙_ _)

variable {A X}

/-- The *evaluation* `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X`: the counit at `Λ_X` of the adjunction
`K ⊗ᴸ - ⊣ RHom(K, -)` (`AlgebraicGeometry.Etale.derivedTensorHomAdjunction`). -/
noncomputable def coefficientEvaluation
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj K).obj ((coefficientDual A X).obj (op K)) ⟶ 𝟙_ _ :=
  (derivedTensorHomAdjunction A K).counit.app (𝟙_ _)

/-- An exact pairing in `D(X_ét)` can be swapped: if `K` and `K'` form an exact pairing, so do
`K'` and `K`. In other words, the right dual of a dualizable complex is also its left dual.

This holds because the derived tensor product of `D(X_ét)` is symmetric monoidal (with the
Koszul sign rule), and in a braided monoidal category exact pairings can be swapped
(`CategoryTheory.BraidedCategory.exactPairing_swap`). The braiding is the one given by
`DerivedCategory.nonempty_braidedCategory`. -/
theorem nonempty_exactPairing_swap
    (K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing K K'] :
    Nonempty (ExactPairing K' K) := by
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf X.smallEtaleTopology A)
  exact ⟨BraidedCategory.exactPairing_swap K K'⟩

/-- If `L` and `K` form an exact pairing in `D(X_ét)`, that is, `L` is a left dual of `K`, then
`K^∨ ≅ L`. -/
noncomputable def coefficientDualIsoOfExactPairing
    (L K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing L K] :
    (coefficientDual A X).obj (op K) ≅ L :=
  MonoidalClosed.ihomObjUnitIso L K

/-- Blueprint `sk-prop-sf-dualizable-biduality`: Biduality of a perfect complex.
This is also blueprint `prop-sf-dualizable` (Perfect complexes are dualizable).

The coefficient dual of a dualizable complex is again dualizable. The evaluation
`K ⊗ᴸ K^∨ ⟶ Λ_X` is `AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`. -/
theorem isDualizable_coefficientDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    IsDualizable ((coefficientDual A X).obj (op K)) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  exact ⟨{ rightDual := K
           exact := exactPairingCongrLeft (coefficientDualIsoOfExactPairing Kᘁ K) }⟩

/-- Blueprint `sk-prop-sf-dualizable-biduality`: Biduality of a perfect complex.

For a dualizable `K` the biduality map `K ⟶ K^∨∨` into the double coefficient dual is an
isomorphism. -/
theorem nonempty_iso_coefficientDual_coefficientDual
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K) :
    Nonempty (K ≅ (coefficientDual A X).obj (op ((coefficientDual A X).obj (op K)))) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  exact ⟨(coefficientDualIsoOfExactPairing K Kᘁ).symm ≪≫
    (coefficientDual A X).mapIso (coefficientDualIsoOfExactPairing Kᘁ K).op⟩

/-- Blueprint `sk-prop-sf-dualizable-biduality`: Biduality of a perfect complex.
This is also blueprint `prop-sf-dualizable-hom` (Internal Hom through the coefficient dual).

For a dualizable `K` and every `M` the canonical map `K^∨ ⊗ᴸ M ⟶ RHom(K, M)` is an
isomorphism. -/
theorem nonempty_iso_coefficientDual_tensor
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((coefficientDual A X).obj (op K) ⊗ M ≅ (RHom(X)[A].obj (op K)).obj M) := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_exactPairing_swap K Kᘁ
  exact ⟨whiskerRightIso (coefficientDualIsoOfExactPairing Kᘁ K) M ≪≫
    (MonoidalClosed.ihomObjIsoTensor Kᘁ K M).symm⟩

/-- Blueprint `sk-lem-sf-twist-interchange`: Internal Hom with an invertible twist.

For a dualizable `K`, an invertible twist `T` — in the `ℓ`-adic formalism a Tate twist
`Λ(m)_X` — and any `M`, the canonical map `RHom(K, M ⊗ᴸ T) ⟶ RHom(K, M) ⊗ᴸ T` is an
isomorphism. In particular `RHom(K, Λ_X(m)) ≅ K^∨(m)`. -/
theorem nonempty_iso_derivedHom_tensor
    {K T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (_hT : IsInvertible T) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op K)).obj (M ⊗ T) ≅ (RHom(X)[A].obj (op K)).obj M ⊗ T) := by
  obtain ⟨e₁⟩ := nonempty_iso_coefficientDual_tensor hK (M ⊗ T)
  obtain ⟨e₂⟩ := nonempty_iso_coefficientDual_tensor hK M
  exact ⟨e₁.symm ≪≫ (α_ _ _ _).symm ≪≫ whiskerRightIso e₂ T⟩

/-- The derived hom out of a dualizable complex is tensoring with its coefficient dual,
`RHom(K, M) ≅ K^∨ ⊗ᴸ M`, written with `AlgebraicGeometry.Etale.derivedTensor`
(`AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`). -/
theorem nonempty_iso_derivedHom_derivedTensor
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsDualizable K)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op K)).obj M ≅
      ((derivedTensor A X).obj ((coefficientDual A X).obj (op K))).obj M) :=
  (nonempty_iso_coefficientDual_tensor hK M).map Iso.symm

end Etale.DerivedCategory

end AlgebraicGeometry
