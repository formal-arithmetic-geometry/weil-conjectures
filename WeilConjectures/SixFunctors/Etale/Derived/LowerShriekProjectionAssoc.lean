/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.ProjectionMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp

/-!
# Associativity of the projection map for `Rf_!`

For `f : X ⟶ Y` with a compactification `c`, the projection map
`PF_{K, L} : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` is compatible with the associativity
of the derived tensor products: for `K` on `X` and `L, N` on `Y` the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N --PF ▷ N--> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N --PF--> Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ Lf^*N)
        | α                                                            | Rf_! α
        v                                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N) ----PF----> Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N)) --Rf_!(K ◁ δ)--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ Lf^*N))
```
commutes, where `δ` is the tensor comparison of `Lf^*`
(`AlgebraicGeometry.Etale.projectionMapOfCompactification_assoc`).

This is assembled from the associativity of the projection map of `Rg_*` for the proper part
`g` of `c` (`AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_assoc`), of the
projection isomorphism of the extension by zero `j_!` along its open part
(`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap_assoc`), and of the
monoidality of the composition isomorphism `Lg^* ⋙ Lj^* ≅ Lf^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_comp`).

It is the formal input of the compatibility of the projection formula with finite reduction
of the coefficients, blueprint `sk-prop-sf-pf-reduction`.
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

section LowerStar

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- **Associativity of the projection map of `Rp_*`.** For `M` on `X` and `L, N` on `Y`,
```
(Rp_*M ⊗ᴸ L) ⊗ᴸ N --π ▷ N--> Rp_*(M ⊗ᴸ Lp^*L) ⊗ᴸ N --π--> Rp_*((M ⊗ᴸ Lp^*L) ⊗ᴸ Lp^*N)
        | α                                                        | Rp_* α
        v                                                          v
Rp_*M ⊗ᴸ (L ⊗ᴸ N) ---π---> Rp_*(M ⊗ᴸ Lp^*(L ⊗ᴸ N)) --Rp_*(M ◁ δ)--> Rp_*(M ⊗ᴸ (Lp^*L ⊗ᴸ Lp^*N))
```
commutes, `π` being `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`. -/
lemma rightDerivedLowerStarProjectionMap_assoc
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerStarProjectionMap A p).app M).app L ▷ N ≫
        ((rightDerivedLowerStarProjectionMap A p).app (M ⊗ L((p)^*[A]).obj L)).app N ≫
          R((p)_*[A]).map (α_ M (L((p)^*[A]).obj L) (L((p)^*[A]).obj N)).hom =
      (α_ (R((p)_*[A]).obj M) L N).hom ≫
        ((rightDerivedLowerStarProjectionMap A p).app M).app (L ⊗ N) ≫
          R((p)_*[A]).map (M ◁ ((leftDerivedUpperStarTensorComparison A p).app L).app N) :=
  letI := leftDerivedUpperStarOplaxMonoidal A p
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap_assoc
    (leftDerivedUpperStarTensorComparison A p) (fun _ _ ↦ rfl) M L N

/-- The projection map of `Rp_*` is natural in its first variable. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_naturality_left
    {M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : M ⟶ M')
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    R((p)_*[A]).map φ ▷ L ≫ ((rightDerivedLowerStarProjectionMap A p).app M').app L =
      ((rightDerivedLowerStarProjectionMap A p).app M).app L ≫
        R((p)_*[A]).map (φ ▷ L((p)^*[A]).obj L) :=
  NatTrans.congr_app ((rightDerivedLowerStarProjectionMap A p).naturality φ) L

end LowerStar

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **Associativity of the projection map of `j_!`.** For an open immersion `j : U ⟶ X`, `K`
on `U` and `M, M'` on `X`, the projection map `p : j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap` satisfies
```
j_!(K ⊗ᴸ Lj^*(M ⊗ᴸ M')) --j_!(K ◁ δ)--> j_!(K ⊗ᴸ (Lj^*M ⊗ᴸ Lj^*M'))
        | p                                       | j_! α⁻¹ ≫ p ≫ p ▷ M'
        v                                         v
j_!K ⊗ᴸ (M ⊗ᴸ M') <-----------α---------- (j_!K ⊗ᴸ M) ⊗ᴸ M'
``` -/
lemma derivedOpenImmersionLowerShriekProjectionMap_assoc
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    D((j)_!open[A]).map (K ◁ ((leftDerivedUpperStarTensorComparison A j).app M).app M') ≫
        D((j)_!open[A]).map (α_ K (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).inv ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app
          (K ⊗ L((j)^*[A]).obj M)).app M' ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M ▷ M' ≫
        (α_ (D((j)_!open[A]).obj K) M M').hom =
      ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (M ⊗ M') := by
  let := leftDerivedUpperStarOplaxMonoidal A j
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ A j
  refine (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).projectionMap_assoc
    (Adjunction.projectionComparisonAssoc_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A j)
      fun Y Y' ↦ ?_) K M M'
  have : inv (δ L((j)^*[A]) Y Y') = ((leftDerivedUpperStarTensorNatIso A j).inv.app Y).app Y' :=
    IsIso.inv_eq_of_hom_inv_id (by
      change ((leftDerivedUpperStarTensorNatIso A j).hom.app Y).app Y' ≫ _ = _
      rw [← NatTrans.comp_app, Iso.hom_inv_id_app]
      rfl)
  rw [this]
  rfl

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- **Associativity of the projection isomorphism of `j_!`**, in the direction of the
blueprint's projection map `j_!K ⊗ᴸ M ⟶ j_!(K ⊗ᴸ Lj^*M)`, the inverse `q` of
`AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso`:
```
j_!K ⊗ᴸ (M ⊗ᴸ M') ------q------> j_!(K ⊗ᴸ Lj^*(M ⊗ᴸ M')) --j_!(K ◁ δ)--> j_!(K ⊗ᴸ (Lj^*M ⊗ᴸ Lj^*M'))
        | α⁻¹                                                                ^ j_! α
        v                                                                    |
(j_!K ⊗ᴸ M) ⊗ᴸ M' --q ▷ M'--> j_!(K ⊗ᴸ Lj^*M) ⊗ᴸ M' ---q---> j_!((K ⊗ᴸ Lj^*M) ⊗ᴸ Lj^*M')
``` -/
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_assoc
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app (M ⊗ M') ≫
        D((j)_!open[A]).map (K ◁ ((leftDerivedUpperStarTensorComparison A j).app M).app M') =
      (α_ (D((j)_!open[A]).obj K) M M').inv ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M ▷ M' ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app
          (K ⊗ L((j)^*[A]).obj M)).app M' ≫
        D((j)_!open[A]).map (α_ K (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).hom := by
  have hi (K M) : ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app M = 𝟙 _ := by
    rw [← derivedOpenImmersionLowerShriekProjectionIso_hom, ← NatTrans.comp_app,
      ← NatTrans.comp_app, Iso.hom_inv_id]
    rfl
  have h := derivedOpenImmersionLowerShriekProjectionMap_assoc A j K M M'
  rw [← cancel_epi (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (M ⊗ M')),
    reassoc_of% (hi K (M ⊗ M'))]
  conv_rhs => rw [← h]
  simp only [assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight_assoc, hi, id_whiskerRight,
    id_comp, reassoc_of% (hi _ M'), ← Functor.map_comp, Iso.inv_hom_id, comp_id,
    CategoryTheory.Functor.map_id]

end OpenImmersion

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

section Composition

/-- The composition isomorphism `Lg₂^* ⋙ Lg₁^* ≅ L(g₁ ≫ g₂)^*` transported along an equality
`g₁ ≫ g₂ = g₁₂` is the composition isomorphism attached to `g₁₂`. -/
lemma leftDerivedUpperStarComp_symm_trans_eqToIso {T S R : Scheme.{u}} (g₁ : T ⟶ S)
    (g₂ : S ⟶ R) (g₁₂ : T ⟶ R) (h : g₁ ≫ g₂ = g₁₂) :
    (leftDerivedUpperStarComp A g₁ g₂).symm ≪≫ eqToIso (congrArg (fun h ↦ L((h)^*[A])) h) =
      (leftDerivedUpperStarComp A g₁ g₂ g₁₂ h.symm).symm := by
  subst h
  ext
  simp

variable [Etale.UpperStarPreservesFlat A] {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`
is compatible with the tensor comparisons:
```
Li^*Lg^*(L ⊗ᴸ L') --Li^*δ--> Li^*(Lg^*L ⊗ᴸ Lg^*L') --δ--> Li^*Lg^*L ⊗ᴸ Li^*Lg^*L'
       | ≅                                                       | ≅
       v                                                         v
Lf^*(L ⊗ᴸ L') -------------------δ-------------------------> Lf^*L ⊗ᴸ Lf^*L'
``` -/
lemma leftDerivedUpperStarCompactificationIso_hom_app_tensorComparison
    (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (L ⊗ L') ≫
        ((leftDerivedUpperStarTensorComparison A f).app L).app L' =
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app L).app L') ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app L ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app L') := by
  have e : leftDerivedUpperStarCompactificationIso A c =
      (leftDerivedUpperStarComp A c.i c.g f c.comm).symm :=
    leftDerivedUpperStarComp_symm_trans_eqToIso A c.i c.g f c.comm.symm
  have h := leftDerivedUpperStarTensorComparison_comp A c.i c.g f c.comm L L'
  simp only [e, Iso.symm_hom]
  rw [← cancel_epi
    ((leftDerivedUpperStarComp A c.i c.g f c.comm).hom.app (L ⊗ L')), Iso.hom_inv_id_app_assoc,
    ← reassoc_of% h, tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
    id_tensorHom_id]
  exact (comp_id _).symm

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The projection map `PF_c` is the composite projection map of `Rg_*` and `j_!`. -/
lemma projectionMapOfCompactification_app_app_eq_compProjectionMap
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L =
      Adjunction.compProjectionMap (I := D((c.i)_!open[A])) (R := R((c.g)_*[A]))
        (leftDerivedUpperStarCompactificationIso A c)
        (fun M L ↦ ((rightDerivedLowerStarProjectionMap A c.g).app M).app L)
        (fun K M ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app M) K L :=
  rfl

/-- **Associativity of the projection map for `Rf_!`.** For a compactification `c` of
`f : X ⟶ Y`, `K` on `X` and `L, N` on `Y`, the projection map
`PF : Rf_!K ⊗ᴸ L ⟶ Rf_!(K ⊗ᴸ Lf^*L)` of
`AlgebraicGeometry.Etale.projectionMapOfCompactification` makes the square
```
(Rf_!K ⊗ᴸ L) ⊗ᴸ N --PF ▷ N--> Rf_!(K ⊗ᴸ Lf^*L) ⊗ᴸ N --PF--> Rf_!((K ⊗ᴸ Lf^*L) ⊗ᴸ Lf^*N)
        | α                                                            | Rf_! α
        v                                                              v
Rf_!K ⊗ᴸ (L ⊗ᴸ N) ----PF----> Rf_!(K ⊗ᴸ Lf^*(L ⊗ᴸ N)) --Rf_!(K ◁ δ)--> Rf_!(K ⊗ᴸ (Lf^*L ⊗ᴸ Lf^*N))
```
commute, `δ` being the tensor comparison of `Lf^*`. -/
theorem projectionMapOfCompactification_assoc
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L N : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((projectionMapOfCompactification A c).app K).app L ▷ N ≫
        ((projectionMapOfCompactification A c).app (K ⊗ L((f)^*[A]).obj L)).app N ≫
        Rf_!(c)[A].map (α_ K (L((f)^*[A]).obj L) (L((f)^*[A]).obj N)).hom =
      (α_ ((Rf_!(c)[A]).obj K) L N).hom ≫
        ((projectionMapOfCompactification A c).app K).app (L ⊗ N) ≫
        Rf_!(c)[A].map (K ◁ ((leftDerivedUpperStarTensorComparison A f).app L).app N) := by
  have h := Adjunction.compProjectionMap_assoc (I := D((c.i)_!open[A])) (R := R((c.g)_*[A]))
    (δi := fun M M' ↦ ((leftDerivedUpperStarTensorComparison A c.i).app M).app M')
    (δg := fun M M' ↦ ((leftDerivedUpperStarTensorComparison A c.g).app M).app M')
    (δf := fun M M' ↦ ((leftDerivedUpperStarTensorComparison A f).app M).app M')
    (e := leftDerivedUpperStarCompactificationIso A c)
    (πg := fun M L ↦ ((rightDerivedLowerStarProjectionMap A c.g).app M).app L)
    (q := fun K M ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app M)
    (leftDerivedUpperStarCompactificationIso_hom_app_tensorComparison A c)
    (fun φ L ↦ rightDerivedLowerStarProjectionMap_naturality_left A c.g φ L)
    (rightDerivedLowerStarProjectionMap_assoc A c.g)
    (fun φ M ↦ NatTrans.congr_app
      ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.naturality φ) M)
    (fun K _ _ φ ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).naturality φ)
    (derivedOpenImmersionLowerShriekProjectionIso_inv_assoc A c.i) K L N
  rw [projectionMapOfCompactification_app_app_eq_compProjectionMap,
    projectionMapOfCompactification_app_app_eq_compProjectionMap,
    projectionMapOfCompactification_app_app_eq_compProjectionMap]
  exact h

end Composition

end AlgebraicGeometry.Etale
