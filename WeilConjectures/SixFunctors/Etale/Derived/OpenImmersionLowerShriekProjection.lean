/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.OpenClosed.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful

/-!
# The projection formula for the extension by zero along an open immersion

Let `j : U ⟶ X` be an open immersion. For `K` in `D(U_ét)` and `M` in `D(X_ét)` there is a
canonical morphism
```
j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M
```
in `D(X_ét)`: the transpose along `j_! ⊣ j^*` of
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> Lj^*(j_!K) ⊗ᴸ Lj^*M ≅ Lj^*(j_!K ⊗ᴸ M),
```
where `η` is the unit of `j_! ⊣ j^*` and the second map is the inverse of
`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison`. It is an isomorphism, by
open–closed conservativity: its restriction to `U` is an isomorphism since the unit `η` is,
and its restriction to the closed complement of `U` is a morphism between zero objects.

## Main definitions and results

- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionMap j`: the morphism
  `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`.
- `AlgebraicGeometry.Etale.isIso_derivedOpenImmersionLowerShriekProjectionMap`: it is an
  isomorphism.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso j`: the resulting
  isomorphism of bifunctors.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

section Unit

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The unit of the derived adjunction `D(j_!) ⊣ D(j^*)` is an isomorphism: the functor
`D(j_!) ⋙ D(j^*)` is induced by the exact functor `j_! ⋙ j^*`, which is isomorphic to the
identity by `Etale.isIso_openImmersionLowerShriekAdjunction_unit`. -/
instance isIso_derivedOpenImmersionLowerShriekUpperStarAdjunction_unit :
    IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit := by
  let e : D((j)_!open[A]) ⋙ D((j)^*[A]) ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.isoWhiskerLeft _ (Etale.upperStarIsoOpenImmersionRestriction A j) ≪≫
          (asIso (Etale.openImmersionLowerShriekAdjunction A j).unit).symm) ≪≫
      Functor.mapDerivedCategoryIdIso _
  have h := (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).fullyFaithfulLOfCompIsoId e
  have := h.full
  have := h.faithful
  infer_instance

end Unit

section Zero

open DerivedCategory ZeroObject

variable {A} in
/-- The derived tensor product `K ⊗ᴸ M` vanishes when `K` does. Writing `M ≅ Qh M₀` with
`M₀` K-flat and `K ≅ Qh 0`, it is `Qh (0 ⊗ M₀) = 0`. -/
lemma isZero_derivedTensor_obj_obj_of_isZero {X : Scheme.{u}}
    {K : DerivedCategory (Sheaf X.smallEtaleTopology A)} (hK : IsZero K)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    IsZero (((-⊗ᴸ-(X)[A]).obj K).obj M) := by
  let R : (HomotopyCategory.quasiIso (Sheaf X.smallEtaleTopology A)
      (.up ℤ)).localizerMorphismKFlat.LeftResolution (Qh.objPreimage M) :=
    Classical.arbitrary _
  let eM : Qh.obj R.X₁.obj ≅ M :=
    Localization.isoOfHom Qh (HomotopyCategory.quasiIso _ (.up ℤ)) R.w R.hw ≪≫
      Qh.objObjPreimageIso M
  let Z : HomotopyCategory (Sheaf X.smallEtaleTopology A) (.up ℤ) :=
    (HomotopyCategory.quotient _ _).obj 0
  have hZ : IsZero Z := Functor.map_isZero _ (isZero_zero _)
  have hZM : IsZero (Z ⊗ R.X₁.obj) := by
    refine IsZero.of_iso ?_
      (Functor.Monoidal.μIso (HomotopyCategory.quotient _ _) 0 R.X₁.obj.as).symm
    have h :
        IsZero ((0 : CochainComplex (Sheaf X.smallEtaleTopology A) ℤ) ⊗ R.X₁.obj.as) := by
      rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, (isZero_zero _).eq_of_src (𝟙 _) 0,
        MonoidalPreadditive.zero_whiskerRight]
    exact Functor.map_isZero (HomotopyCategory.quotient _ _) h
  have := isIso_μNatTrans_Qh_app_app_of_kFlat Z R.X₁.obj R.X₁.property
  refine (Functor.map_isZero Qh hZM).of_iso ?_
  exact ((-⊗ᴸ-(X)[A]).mapIso (hK.iso (Functor.map_isZero Qh hZ))).app M ≪≫
    ((-⊗ᴸ-(X)[A]).obj _).mapIso eM.symm ≪≫
    asIso (((Functor.LaxMonoidal.μNatTrans Qh).app Z).app R.X₁.obj)

end Zero

section Map

open DerivedCategory

variable [Etale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The bifunctor `(K, M) ↦ K ⊗ᴸ Lj^*M`, of type `D(U_ét) ⥤ D(X_ét) ⥤ D(U_ét)`. -/
noncomputable abbrev derivedTensorLeftDerivedUpperStarRight :
    DerivedCategory (Sheaf U.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf U.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj L((j)^*[A])).obj (-⊗ᴸ-(U)[A])

/-- The bifunctor `(K, M) ↦ j_!K ⊗ᴸ M`, of type `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`. -/
noncomputable abbrev derivedTensorOpenImmersionLowerShriekLeft :
    DerivedCategory (Sheaf U.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤
        DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (((Functor.whiskeringLeft₂ _).obj D((j)_!open[A])).obj (𝟭 _)).obj (-⊗ᴸ-(X)[A])

/-- The morphism `K ⊗ᴸ Lj^*M ⟶ j^*(j_!K ⊗ᴸ M)` of bifunctors `D(U_ét) ⥤ D(X_ét) ⥤ D(U_ét)`
whose transpose along `j_! ⊣ j^*` is the projection map: the composite of
`η ⊗ᴸ 1 : K ⊗ᴸ Lj^*M ⟶ Lj^*(j_!K) ⊗ᴸ Lj^*M` and the inverse of the comparison
`Lj^*(j_!K ⊗ᴸ M) ⟶ Lj^*(j_!K) ⊗ᴸ Lj^*M`, followed by `Lj^* ≅ D(j^*)`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionMapAdj :
    derivedTensorLeftDerivedUpperStarRight A j ⟶
      (Functor.postcompose₂.obj D((j)^*[A])).obj
        (derivedTensorOpenImmersionLowerShriekLeft A j) :=
  (((Functor.whiskeringLeft₂ _).map
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit ≫
        Functor.whiskerLeft D((j)_!open[A])
          (leftDerivedUpperStarIsoMapDerivedCategory A j).inv)).app L((j)^*[A])).app
      (-⊗ᴸ-(U)[A]) ≫
    (((Functor.whiskeringLeft₂ _).obj D((j)_!open[A])).obj (𝟭 _)).map
      (CategoryTheory.inv (leftDerivedUpperStarTensorComparison A j)) ≫
    (((Functor.whiskeringLeft₂ _).obj D((j)_!open[A])).obj (𝟭 _)).map
      ((Functor.postcompose₂.map (leftDerivedUpperStarIsoMapDerivedCategory A j).hom).app
        (-⊗ᴸ-(X)[A]))

/-- The **projection map** `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of bifunctors
`D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, for an open immersion `j : U ⟶ X`: the transpose along
`j_! ⊣ j^*` of the composite
```
K ⊗ᴸ Lj^*M --(η ⊗ᴸ 1)--> Lj^*(j_!K) ⊗ᴸ Lj^*M ≅ Lj^*(j_!K ⊗ᴸ M),
```
the isomorphism being the inverse of `leftDerivedUpperStarTensorComparison`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionMap :
    (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorLeftDerivedUpperStarRight A j) ⟶
      derivedTensorOpenImmersionLowerShriekLeft A j :=
  (Functor.postcompose₂.obj D((j)_!open[A])).map
      (derivedOpenImmersionLowerShriekProjectionMapAdj A j) ≫
    (Functor.postcompose₂.map
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).counit).app
        (derivedTensorOpenImmersionLowerShriekLeft A j)

/-- The components of the projection map are the transposes along `j_! ⊣ j^*` of the
components of `derivedOpenImmersionLowerShriekProjectionMapAdj`. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_app_app
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M =
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).homEquiv _ _).symm
        (((derivedOpenImmersionLowerShriekProjectionMapAdj A j).app K).app M) := by
  simp [derivedOpenImmersionLowerShriekProjectionMap, Adjunction.homEquiv_counit]

end Map

section IsIso

variable [Etale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance isIso_derivedOpenImmersionLowerShriekProjectionMapAdj :
    IsIso (derivedOpenImmersionLowerShriekProjectionMapAdj A j) := by
  unfold derivedOpenImmersionLowerShriekProjectionMapAdj
  infer_instance

variable {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [hJ : X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

-- `hJ` does not appear in the statements below, and neither do `FC` and `CC` it depends on,
-- so it has to be included by hand; it is needed by the open–closed conservativity
-- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_closedComplement_map`.
include hJ

/-- The projection map `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` is an isomorphism. By open–closed
conservativity it suffices to check this after `Lj^*` and after the derived pullback to the
closed complement of `j`. After `Lj^*` it is, up to the unit of `j_! ⊣ j^*` (an
isomorphism), the transposed map `K ⊗ᴸ Lj^*M ⟶ j^*(j_!K ⊗ᴸ M)`, which is an isomorphism.
On the closed complement both sides vanish, since `j_!` does. -/
instance isIso_derivedOpenImmersionLowerShriekProjectionMap :
    IsIso (derivedOpenImmersionLowerShriekProjectionMap A j) := by
  have key (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
      (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      IsIso (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) := by
    refine isIso_of_isIso_leftDerivedUpperStar_closedComplement_map A j _ ?_ ?_
    · rw [NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory A j)]
      have : D((j)^*[A]).map
          (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M) =
          CategoryTheory.inv
              ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app _) ≫
            ((derivedOpenImmersionLowerShriekProjectionMapAdj A j).app K).app M := by
        rw [IsIso.eq_inv_comp]
        refine ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).homEquiv_unit _ _
          (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M)).symm.trans ?_
        rw [derivedOpenImmersionLowerShriekProjectionMap_app_app, Equiv.apply_symm_apply]
      rw [this]
      infer_instance
    · have hS := isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j
        (((-⊗ᴸ-(U)[A]).obj K).obj (L((j)^*[A]).obj M))
      have hT := (isZero_derivedTensor_obj_obj_of_isZero
        (isZero_leftDerivedUpperStar_closedComplement_obj_openImmersionLowerShriek A j K)
        (L((j.closedComplement)^*[A]).obj M)).of_iso
          (leftDerivedUpperStarTensorIso A j.closedComplement _ M)
      exact ⟨⟨hT.to_ _, hS.eq_of_src _ _, hT.eq_of_src _ _⟩⟩
  have (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
      IsIso ((derivedOpenImmersionLowerShriekProjectionMap A j).app K) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- The **projection formula** for an open immersion `j : U ⟶ X`: the isomorphism
`j_!(K ⊗ᴸ Lj^*M) ≅ j_!K ⊗ᴸ M` of bifunctors `D(U_ét) ⥤ D(X_ét) ⥤ D(X_ét)`, whose underlying
morphism is `derivedOpenImmersionLowerShriekProjectionMap`. -/
noncomputable def derivedOpenImmersionLowerShriekProjectionIso :
    (Functor.postcompose₂.obj D((j)_!open[A])).obj
        (derivedTensorLeftDerivedUpperStarRight A j) ≅
      derivedTensorOpenImmersionLowerShriekLeft A j :=
  asIso (derivedOpenImmersionLowerShriekProjectionMap A j)

@[simp]
lemma derivedOpenImmersionLowerShriekProjectionIso_hom :
    (derivedOpenImmersionLowerShriekProjectionIso A j).hom =
      derivedOpenImmersionLowerShriekProjectionMap A j :=
  rfl

end IsIso

end Etale

end AlgebraicGeometry
