/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.CategoryTheory.Monoidal.Closed.ExceptionalDual
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralVerdier
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic

/-!
# The integral exceptional adjoint

Let `Λ` be a Noetherian domain, complete for a principal ideal `I = (ϖ)` with `Λ ⧸ I` finite of
exponent invertible on an algebraically closed field `k` (the integral stage `Λ = 𝒪_E`), and
`f : X ⟶ Y` a separated morphism of separated `k`-schemes of finite type. This file proves the
integral exceptional adjoint of blueprint `prop-coef-integral-exceptional-adjoint`
(`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`): the derived limit
`G_f L` of the exceptional inverse images of the reductions of `L ∈ Dᵇc(Y, Λ)` lies in
`Dᵇc(X, Λ)`, is `Rf^! L`, satisfies the dual formula `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L` and has the
expected reduction Tor interval.

## Proof

* The dual formula is the Yoneda argument of `CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`): biduality
  `L ≅ 𝔻_Y 𝔻_Y L` (`thm-coef-integral-verdier`), the projection formula modulo `ϖ`
  (`lem-fix-operation-reduction`), which suffices for morphisms into the derived complete
  dualizing complex, and the identification `Rf^! ω_Y ≅ ω_X` of the dualizing complexes
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_dualizing`).
* Constructibility and the Tor interval then follow, as in the blueprint, from integral
  Verdier duality applied on `Y` and on `X`, the completed pullback being a derived completion
  of `Lf^* 𝔻_Y L` and the dualizing complexes those of `prop-coef-integral-dualizing`.

## Implementation notes

Statements at `Λ` are phrased with `AlgebraicGeometry.Etale.derivedTensor` and
`AlgebraicGeometry.Etale.derivedHom`, never with `⊗` or `ihom` found by instance search: the
kernel does not compare these in reasonable time at `ModuleCat Λ` (see
`WeilConjectures.SixFunctors.Etale.Derived.TensorStructure`). The formal Yoneda argument is
therefore specialised first to a general coefficient category
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_obj_derivedHom`).

The identification `Rf^! ω_Y ≅ ω_X` rests on the composition law of the exceptional inverse
images on the torsion tower `n ↦ Λ ⧸ Iⁿ`
(`AlgebraicGeometry.Etale.nonempty_iso_quotPowFunctor_comp_rightDerivedUpperShriek_comp`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

attribute [local instance] derivedBraidedCategory

/-! ### The formal dual formula -/

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint]

/-- **The dual formula `Rf^! L ≅ RHom(N, ω_X)`.** Let `L, M, ω_Y ∈ D(Y_ét)` with an isomorphism
`L ≅ RHom(M, ω_Y)`, and assume that the projection maps
`PF_{f, K, M} : Rf_! K ⊗ᴸ M ⟶ Rf_!(K ⊗ᴸ Lf^* M)` induce bijections on morphisms into `ω_Y`.
Given `γ : Rf^! ω_Y ≅ ω_X` and `φ : Lf^* M ⟶ N` inducing bijections
`Hom(K ⊗ᴸ N, ω_X) ≃ Hom(K ⊗ᴸ Lf^* M, ω_X)`, there is an isomorphism `Rf^! L ≅ RHom(N, ω_X)`
(`CategoryTheory.Verdier.nonempty_iso_obj_of_adjunction`). -/
theorem nonempty_iso_rightDerivedUpperShriek_obj_derivedHom
    {L M ωY : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (e : L ≅ ((derivedHom A Y).obj (op M)).obj ωY)
    (hπ : ∀ K, Function.Bijective (fun a : (R(f)_![A]).obj (((derivedTensor A X).obj K).obj
        ((L((f)^*[A])).obj M)) ⟶ ωY ↦ ((projectionMap A f).app K).app M ≫ a))
    {ωX N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (γ : (R(f)^![A]).obj ωY ≅ ωX) (φ : (L((f)^*[A])).obj M ⟶ N)
    (hφ : ∀ K, Function.Bijective
      (fun a : ((derivedTensor A X).obj K).obj N ⟶ ωX ↦ ((derivedTensor A X).obj K).map φ ≫ a)) :
    Nonempty ((R(f)^![A]).obj L ≅ ((derivedHom A X).obj (op N)).obj ωX) :=
  Verdier.nonempty_iso_obj_of_adjunction (rightDerivedUpperShriekAdjunction A f)
    (derivedTensorHomAdjunction A M) e (fun K ↦ ((projectionMap A f).app K).app _)
    (fun g ↦ NatTrans.congr_app ((projectionMap A f).naturality g) _) hπ
    (derivedTensorHomAdjunction A N) γ φ hφ

end General

/-! ### Morphisms into objects orthogonal to `ϖ`-invertible objects -/

section Orthogonal

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
include hϖ

/-- The reductions modulo `ϖⁿ` of an object on which `ϖ` acts invertibly vanish: the reduction is
the cone of the multiplication by `ϖⁿ`. -/
lemma isZero_reductionModIdeal_of_smulInvertible (n : ℕ) (K : 𝐃(X, Λ))
    (hK : _root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ K) :
    IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) := by
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  let T := _root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n
  have hT : F.mapTriangle.obj T ∈ distTriang _ :=
    F.map_distinguished _ (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n)
  have hmor : (F.mapTriangle.obj T).mor₁ = ϖ ^ n • 𝟙 (F.obj T.obj₁) := by
    change F.map T.mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
      CategoryTheory.Functor.map_id]
  let u : F.obj T.obj₁ ≅ K := derivedTensorSingleUnitIso K
  have h₁ : IsIso (F.mapTriangle.obj T).mor₁ := by
    rw [hmor]
    have : ϖ ^ n • 𝟙 (F.obj T.obj₁) = u.hom ≫ (ϖ ^ n • 𝟙 K) ≫ u.inv := by
      rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul, Iso.hom_inv_id]
    rw [this]
    have := hK.pow n
    infer_instance
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).2 h₁

/-- A morphism whose reduction modulo a nonzerodivisor `ϖ` is an isomorphism induces bijections
on morphisms into every object receiving no nonzero map from an object on which `ϖ` acts
invertibly (for instance a derived complete object). -/
lemma bijective_comp_of_isIso_reductionModIdeal {S T W : 𝐃(X, Λ)} (u : S ⟶ T)
    (hu : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map u))
    (hW : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal W) :
    Function.Bijective (fun a : T ⟶ W ↦ u ≫ a) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  exact _root_.DerivedCategory.bijective_comp_of_smulInvertible hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC) hW

/-- Tensoring a morphism whose reduction modulo `ϖ` is an isomorphism with any object gives a
morphism inducing bijections on morphisms into every object receiving no nonzero map from an
object on which `ϖ` acts invertibly. -/
lemma bijective_derivedTensor_map_comp_of_isIso_reductionModIdeal {S T W : 𝐃(X, Λ)}
    (u : S ⟶ T) (hu : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map u))
    (hW : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal W)
    (K : 𝐃(X, Λ)) :
    Function.Bijective (fun a : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj T ⟶ W ↦
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map u ≫ a) := by
  obtain ⟨C, g, h, hT⟩ := distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  have hϖC : IsIso (ϖ • 𝟙 C) := isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC
  let F := (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K
  have hFC : _root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ (F.obj C) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← F.map_id, ← Functor.map_smul]
    infer_instance
  exact _root_.DerivedCategory.bijective_comp_of_smulInvertible (F.map_distinguished _ hT) hFC hW

omit hϖ in
/-- The point of a homotopy limit of a tower of objects killed by powers of `ϖ` receives no
nonzero map from an object on which `ϖ` acts invertibly. -/
lemma rightOrthogonal_smulInvertible_of_isHomotopyLimit {F : ℕᵒᵖ ⥤ 𝐃(X, Λ)}
    (hF : ∀ n : ℕ, ∃ m : ℕ, ϖ ^ m • 𝟙 (F.obj (op n)) = 0) {c : Cone F}
    (hc : IsHomotopyLimit c) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal c.pt :=
  fun Z f hZ ↦ hc.hom_ext_zero
    (fun n g ↦ (hF n).elim fun _ hm ↦ hZ.hom_eq_zero hm g)
    (fun n g ↦ (hF n).elim fun _ hm ↦ (ObjectProperty.le_shift _ 1 Z hZ).hom_eq_zero hm g) f

omit hϖ in
/-- The point of a homotopy limit of the image of the tower `n ↦ Λ ⧸ Iⁿ` under a `Λ`-linear
functor receives no nonzero map from an object on which `ϖ ∈ I` acts invertibly. -/
lemma rightOrthogonal_smulInvertible_of_isHomotopyLimit_quotPowFunctor {S : Scheme.{u}}
    {I : Ideal Λ} (hϖI : ϖ ∈ I) (G : 𝐃(S, Λ) ⥤ 𝐃(X, Λ)) [G.Linear Λ]
    {c : Cone (_root_.DerivedCategory.quotPowFunctor S.smallEtaleTopology I ⋙ G)}
    (hc : IsHomotopyLimit c) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal c.pt :=
  rightOrthogonal_smulInvertible_of_isHomotopyLimit (fun n ↦ ⟨n, by
    change ϖ ^ n • 𝟙 (G.obj _) = 0
    rw [← G.map_id, ← Functor.map_smul,
      _root_.DerivedCategory.smul_id_quotPowFunctor_obj _ hϖI n, G.map_zero]⟩) hc

end Orthogonal
