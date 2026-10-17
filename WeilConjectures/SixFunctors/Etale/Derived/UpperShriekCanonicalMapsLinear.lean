/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMapIsIso
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMapsCoherence

/-!
# The canonical tensor map from an adjunction with a linear counit

Let `f : X ⟶ Y` admit a compactification and satisfy the projection formula. Suppose that
`Rf_!` has a right adjoint of the form `N ↦ ω ⊗ᴸ Lf^* N` whose counit is *linear*: it is the
composite

`Rf_!(ω ⊗ᴸ Lf^* N) ≅ Rf_! ω ⊗ᴸ N ⟶ Λ_Y ⊗ᴸ N ≅ N`

of the inverse of the projection map and of a fixed morphism `t : Rf_! ω ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekLinearCounit`). This is the shape of the
projective-line adjunction `Rq_* ⊣ q^*(1)[2]`, whose counit is the trace (blueprint
`thm-amb-p1-adjunction`, `def-amb-p1-trace`). Then the dualizing complex is `ω_f ≅ ω` and the
canonical tensor maps `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` are isomorphisms for all `K`
(`CategoryTheory.Adjunction.isIso_projectionTensorMap_of_bijective`).

## Main definitions

- `AlgebraicGeometry.Etale.rightDerivedLowerShriekLinearCounit`

## Main statements

- `AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMapOfIsIso_of_adjunction`
- `AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_of_adjunction`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- Search the braiding through the symmetric structure, as in the definition of the derived
-- tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

section Linear

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsIso (projectionMap A f)]

/-- The **linear counit** `Rf_!(ω ⊗ᴸ Lf^* N) ≅ Rf_! ω ⊗ᴸ N ⟶ Λ_Y ⊗ᴸ N ≅ N` attached to a morphism
`t : Rf_! ω ⟶ Λ_Y`: the inverse of the projection map, followed by `t ⊗ᴸ N` and the left
unitor. -/
noncomputable def rightDerivedLowerShriekLinearCounit
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (R(f)_![A]).obj ω ⟶ 𝟙_ _) (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R(f)_![A]).obj (((derivedTensor A X).obj ω).obj ((L((f)^*[A])).obj N)) ⟶ N :=
  inv (((projectionMap A f).app ω).app N) ≫ ((derivedTensor A Y).map t).app N ≫
    (derivedTensorLeftUnitor A Y N).hom

variable [(R(f)_![A]).IsLeftAdjoint]

/-- **Smooth duality from an adjunction with a linear counit.** If `Rf_!` is left adjoint to
`N ↦ ω ⊗ᴸ Lf^* N`, with the linear counit attached to some `t : Rf_! ω ⟶ Λ_Y`, then the
canonical tensor map `θ_{f,K}` is an isomorphism for every `K`, and the transpose `ω ⟶ ω_f` of
`t` is an isomorphism. -/
theorem isIso_dualizingComplexTensorMapOfIsIso_of_adjunction
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (R(f)_![A]).obj ω ⟶ 𝟙_ _) (adj : R(f)_![A] ⊣ L((f)^*[A]) ⋙ (derivedTensor A X).obj ω)
    (hadj : ∀ N, adj.counit.app N = rightDerivedLowerShriekLinearCounit f ω t N)
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (dualizingComplexTensorMapOfIsIso f K) ∧
      IsIso ((rightDerivedUpperShriekAdjunction A f).homEquiv _ _ t) := by
  have h (P : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
      (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
      Function.Bijective fun φ : P ⟶ ω ⊗ (L((f)^*[A])).obj N ↦
        (R(f)_![A]).map φ ≫ Adjunction.linearCounit
          (fun M N ↦ ((projectionMap A f).app M).app N) ω t N := by
    have : (fun φ : P ⟶ ω ⊗ (L((f)^*[A])).obj N ↦ (R(f)_![A]).map φ ≫
        Adjunction.linearCounit (fun M N ↦ ((projectionMap A f).app M).app N) ω t N) =
        (adj.homEquiv P N).symm := by
      ext φ
      rw [Adjunction.homEquiv_counit, hadj]
      rfl
    rw [this]
    exact (adj.homEquiv P N).symm.bijective
  obtain ⟨h₁, h₂⟩ := Adjunction.isIso_projectionTensorMap_of_bijective
    (rightDerivedUpperShriekAdjunction A f) (projectionMap_app_app_naturality_left f)
    (isInvertible_leftDerivedUpperStar_obj f isInvertible_unit) ω t h K
  exact ⟨(isIso_dualizingComplexTensorMapOfIsIso_iff f K).2 h₁, h₂⟩

/-- Under the hypotheses of
`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMapOfIsIso_of_adjunction`, the dualizing
complex is `ω_f ≅ ω`. -/
theorem nonempty_dualizingComplex_iso_of_adjunction
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (R(f)_![A]).obj ω ⟶ 𝟙_ _) (adj : R(f)_![A] ⊣ L((f)^*[A]) ⋙ (derivedTensor A X).obj ω)
    (hadj : ∀ N, adj.counit.app N = rightDerivedLowerShriekLinearCounit f ω t N) :
    Nonempty (dualizingComplex A f ≅ ω) := by
  have := (isIso_dualizingComplexTensorMapOfIsIso_of_adjunction f ω t adj hadj (𝟙_ _)).2
  exact ⟨(asIso ((rightDerivedUpperShriekAdjunction A f).homEquiv _ _ t)).symm⟩


end Linear

section Proper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f]

/-- For a proper morphism `f`, the projection map of `Rf_!` is that of `Rf_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`) through the identification
`Rf_! ≅ Rf_*` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
lemma projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMap A f).app K).app L ≫
        (rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app
          (((derivedTensor A X).obj K).obj ((L((f)^*[A])).obj L)) =
      ((derivedTensor A Y).map ((rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app
          K)).app L ≫
        ((rightDerivedLowerStarProjectionMap A f).app K).app L := by
  rw [rightDerivedLowerShriekIsoRightDerivedLowerStar_hom,
    rightDerivedLowerShriekToLowerStarComp_comp_eq, projectionMap_app_app_eq]
  exact compactificationProjectionMap_comp_forgetSupports A (HasCompactification.compactification f)
    K L

variable [IsIso (projectionMap A f)]

/-- For a proper morphism `f` with an invertible projection map of `Rf_!`, the projection map
of `Rf_*` is invertible. -/
instance isIso_rightDerivedLowerStarProjectionMap_app_app_of_isProper
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso (((rightDerivedLowerStarProjectionMap A f).app K).app L) := by
  have h := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar f K L
  have : IsIso (((derivedTensor A Y).map ((rightDerivedLowerShriekIsoRightDerivedLowerStar A
      f).hom.app K)).app L ≫ ((rightDerivedLowerStarProjectionMap A f).app K).app L) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (((derivedTensor A Y).map
    ((rightDerivedLowerShriekIsoRightDerivedLowerStar A f).hom.app K)).app L) _

/-- The **linear counit** `Rf_*(ω ⊗ᴸ Lf^* N) ≅ Rf_* ω ⊗ᴸ N ⟶ Λ_Y ⊗ᴸ N ≅ N` of a proper morphism
`f` attached to a morphism `t : Rf_* ω ⟶ Λ_Y`: the inverse of the projection formula of `Rf_*`,
followed by `t ⊗ᴸ N` and the left unitor. -/
noncomputable def rightDerivedLowerStarLinearCounit
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (R((f)_*[A])).obj ω ⟶ 𝟙_ _) (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (R((f)_*[A])).obj (((derivedTensor A X).obj ω).obj ((L((f)^*[A])).obj N)) ⟶ N :=
  inv (((rightDerivedLowerStarProjectionMap A f).app ω).app N) ≫
    ((derivedTensor A Y).map t).app N ≫ (derivedTensorLeftUnitor A Y N).hom

/-- An adjunction `Rf_* ⊣ (N ↦ ω ⊗ᴸ Lf^* N)` of a proper morphism with the linear counit
attached to `t : Rf_* ω ⟶ Λ_Y` is, through `Rf_! ≅ Rf_*`, an adjunction
`Rf_! ⊣ (N ↦ ω ⊗ᴸ Lf^* N)` with the linear counit attached to `Rf_! ω ≅ Rf_* ω ⟶ Λ_Y`. -/
theorem exists_rightDerivedLowerShriek_adjunction_of_rightDerivedLowerStar
    (ω : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (R((f)_*[A])).obj ω ⟶ 𝟙_ _) (adj : R((f)_*[A]) ⊣ L((f)^*[A]) ⋙ (derivedTensor A X).obj ω)
    (hadj : ∀ N, adj.counit.app N = rightDerivedLowerStarLinearCounit f ω t N) :
    ∃ (t' : (R(f)_![A]).obj ω ⟶ 𝟙_ _) (adj' : R(f)_![A] ⊣ L((f)^*[A]) ⋙ (derivedTensor A X).obj ω),
      ∀ N, adj'.counit.app N = rightDerivedLowerShriekLinearCounit f ω t' N := by
  let e := rightDerivedLowerShriekIsoRightDerivedLowerStar A f
  refine ⟨e.hom.app ω ≫ t, adj.ofNatIsoLeft e.symm, fun N ↦ ?_⟩
  have h := projectionMap_comp_rightDerivedLowerShriekIsoRightDerivedLowerStar f ω N
  rw [← cancel_epi (((projectionMap A f).app ω).app N)]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_inv, hadj,
    rightDerivedLowerShriekLinearCounit, rightDerivedLowerStarLinearCounit, IsIso.hom_inv_id_assoc,
    reassoc_of% h, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rfl

end Proper

end Etale

end AlgebraicGeometry
