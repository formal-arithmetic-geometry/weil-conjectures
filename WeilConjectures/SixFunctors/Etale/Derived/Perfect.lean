/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# Perfect complexes of étale sheaves and their coefficient duals

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` is monoidal closed, with tensor
product `- ⊗ᴸ -` and internal hom `RHom(-, -)`. The *coefficient dual* of a complex is
`K^∨ = RHom(K, Λ_X)`.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`: `K ↦ K^∨ = RHom(K, Λ_X)`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientEvaluation`: the evaluation
  `K ⊗ᴸ K^∨ ⟶ Λ_X`.
- `AlgebraicGeometry.Etale.DerivedCategory.coefficientDualIsoOfExactPairing`: `K^∨ ≅ L` for a
  left dual `L` of `K`.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`
  (`sk-prop-sf-dualizable-biduality`, `prop-sf-dualizable`): `K^∨` is dualizable for a
  dualizable `K`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_coefficientDual`
  (`sk-prop-sf-dualizable-biduality`): biduality `K ≅ K^∨∨` for a dualizable `K`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_coefficientDual_tensor`
  (`sk-prop-sf-dualizable-biduality`, `prop-sf-dualizable-hom`): the comparison
  `K^∨ ⊗ᴸ M ≅ RHom(K, M)`.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_derivedHom_tensor`
  (`sk-lem-sf-twist-interchange`): the internal hom commutes with an invertible twist.
- `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`
  (`sk-thm-sf-internal-hom-pullback`): the internal hom with a dualizable first variable
  commutes with pullback.

## Implementation notes

In the `ℓ`-adic formalism a complex is called *perfect* when it is, locally on the small étale
site, quasi-isomorphic to a bounded complex of finite projective `Λ_X`-modules. That this
coincides with dualizability for `- ⊗ᴸ -` is a theorem about module coefficients, not a
definition, and it is not available for a general coefficient category `A`; perfectness is
therefore *rendered here as* dualizability, `CategoryTheory.IsDualizable` of
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`. A Tate twist `Λ_X(m)` is
likewise rendered as an invertible object, `CategoryTheory.IsInvertible`.

Canonical comparison maps are not constructed in this repository, so every isomorphism
assertion below is of the form `Nonempty (_ ≅ _)`; the naturality clauses of the blueprint,
and the compatibilities with finite reduction, scalar extension and shifts, are consequently
not stated. The proofs sketched in the blueprint go through the local description of a perfect
complex as a bounded complex of finite free modules, which turns the internal hom into a tensor
product.

With perfectness rendered as dualizability, the biduality statements are formal consequences of
the rigid monoidal structure: `RHom(K, -) ≅ L ⊗ᴸ -` for a left dual `L` of `K`
(`CategoryTheory.MonoidalClosed.ihomIsoTensorLeft`). They use one further input, that the right
dual of `K` is also a left dual (`nonempty_exactPairing_swap`). This follows from the symmetry
of the derived tensor product, which has not been constructed yet.

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
(`CategoryTheory.BraidedCategory.exactPairing_swap`). No braiding on `D(X_ét)` has been
constructed in this repository yet, which is why this is stated separately. -/
theorem nonempty_exactPairing_swap
    (K K' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) [ExactPairing K K'] :
    Nonempty (ExactPairing K' K) :=
  sorry

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
    (hT : IsInvertible T) (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op K)).obj (M ⊗ T) ≅ (RHom(X)[A].obj (op K)).obj M ⊗ T) :=
  sorry

/-- Blueprint `sk-thm-sf-internal-hom-pullback`: Internal Hom versus pullback for a
site-perfect first variable.

For a morphism of schemes `g : Y' ⟶ X`, a dualizable `M` and any `N` in `D(X_ét)`, the
canonical comparison

`Lg^* RHom_Λ(M, N) ⟶ RHom_Λ(Lg^* M, Lg^* N)`

is an isomorphism. -/
theorem nonempty_iso_leftDerivedUpperStar_derivedHom {Y' : Scheme.{u}} (g : Y' ⟶ X)
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hM : IsDualizable M)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((L((g)^*[A])).obj ((RHom(X)[A].obj (op M)).obj N) ≅
      (RHom(Y')[A].obj (op ((L((g)^*[A])).obj M))).obj ((L((g)^*[A])).obj N)) :=
  sorry

end Etale.DerivedCategory

end AlgebraicGeometry
