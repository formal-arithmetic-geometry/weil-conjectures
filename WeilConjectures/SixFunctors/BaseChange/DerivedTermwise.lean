/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# The termwise construction of the derived base change map

For a commutative square of schemes `g' ≫ f = f' ≫ g` (notation as in
`WeilConjectures.SixFunctors.BaseChange.Square`) and an object `K` of `D⁺(X_ét)`, choose a
K-injective resolution `K ≅ I` and a K-injective resolution `s : g'^* I ⟶ J` on `X'`. Then
`f_* I` computes `R f_*⁺ K` and `f'_* J` computes `R f'_*⁺ (g'^* K)`, and the derived base change
map at `K` is the class of the morphism of complexes
`g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J`, the levelwise underived base change map followed by
`f'_*` of the resolution `s`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_app_eq_termwise`).

The commutative diagram behind it, which needs no K-injectivity, is
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_termwise_comm`; K-injectivity makes the
units `f_* I ⟶ R f_*⁺ I` and `f'_* J ⟶ R f'_*⁺ J` isomorphisms
(`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective`).
(blueprint: `lem-weil-pbc-derived-exchange-termwise`)
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive] [EnoughInjectives C]

/-- The unit `F(I) ⟶ R F⁺ (I)` of the bounded below right derived functor is an isomorphism on
every bounded below K-injective complex `I`: such a complex is isomorphic in the homotopy
category to a bounded below complex of injectives, on which the unit is an isomorphism. -/
lemma isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective (I : HomotopyCategory.Plus C)
    (hI : CochainComplex.IsKInjective I.1.as) :
    IsIso (F.rightDerivedFunctorPlusUnit.app I) := by
  let E := DerivedCategory.Plus.injectiveObjectEquivalence C
  let Y := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj
    (E.inverse.obj (DerivedCategory.Plus.Qh.obj I))
  let e : DerivedCategory.Plus.Qh.obj Y ≅ DerivedCategory.Plus.Qh.obj I :=
    E.counitIso.app (DerivedCategory.Plus.Qh.obj I)
  obtain ⟨a, ha⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective I Y
    inferInstance).2 e.inv
  obtain ⟨b, hb⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective Y I hI).2 e.hom
  have hab : a ≫ b = 𝟙 I := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective I I hI).1
    (by simp [ha, hb])
  have hba : b ≫ a = 𝟙 Y := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective Y Y
    inferInstance).1 (by simp [ha, hb])
  have : IsIso (F.rightDerivedFunctorPlusUnit.app Y) := by
    dsimp only [Y]
    infer_instance
  exact NatTrans.isIso_app_of_iso _ ⟨a, b, hab, hba⟩

end CategoryTheory.Functor

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

open Etale

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- **The termwise diagram of the derived base change map.** For a bounded below complex `I` on
`X`, an isomorphism `e : K ≅ I` in `D⁺(X_ét)` and a morphism `s : g'^* I ⟶ J` of bounded below
complexes on `X'`, the square
```
  g^* f_* I ──────────────────────────────→ f'_* J
     │ unit                                    │ unit
     ↓                                         ↓
  g^* R f_* K ──derivedBaseChangeMapPlus──→ R f'_* g'^* K ──→ R f'_* J
```
commutes, the top arrow being the levelwise underived base change map followed by `f'_* s`,
modulo the isomorphisms `Functor.mapDerivedCategoryPlusFactorsh`. -/
@[reassoc]
lemma Etale.derivedBaseChangeMapPlus_termwise_comm (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A))
    (e : K ≅ DerivedCategory.Plus.Qh.obj I)
    (J : HomotopyCategory.Plus (Sheaf X'.smallEtaleTopology A))
    (s : ((g')^*[A]).mapHomotopyCategoryPlus.obj I ⟶ J) :
    ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app ((f)_*[A].mapHomotopyCategoryPlus.obj I) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app I ≫
            (f')_*[A].mapHomotopyCategoryPlus.map s) ≫
        (f')_*[A].rightDerivedFunctorPlusUnit.app J =
      ((g)^*[A]).mapDerivedCategoryPlus.map ((f)_*[A].rightDerivedFunctorPlusUnit.app I ≫
          (f)_*[A].rightDerivedFunctorPlus.map e.inv) ≫
        (Etale.derivedBaseChangeMapPlus A sq).app K ≫
        (f')_*[A].rightDerivedFunctorPlus.map
          (((g')^*[A]).mapDerivedCategoryPlus.map e.hom ≫
            ((g')^*[A]).mapDerivedCategoryPlusFactorsh.hom.app I ≫
            DerivedCategory.Plus.Qh.map s) := by
  have h₁ := (Etale.derivedBaseChangeMapPlus A sq).naturality e.inv
  have h₂ := (f')_*[A].rightDerivedFunctorPlusUnit.naturality s
  dsimp at h₁ h₂
  simp only [Functor.map_comp, assoc]
  rw [reassoc_of% h₁, Etale.derivedBaseChangeMapPlus_fac_app_assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id]
  simp [h₂]

/-- **The derived base change map is computed termwise on K-injective resolutions.** Let `K` be
an object of `D⁺(X_ét)`, `e : K ≅ I` a K-injective resolution, so that `f_* I` represents
`R f_*⁺ K`, and `s : g'^* I ⟶ J` a K-injective resolution of `g'^* I` on `X'`, so that
`f'_* J` represents `R f'_*⁺ (g'^* K)`. Then the derived base change map at `K` is the class of
the morphism of complexes `g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J`, the levelwise underived base
change map followed by `f'_* s`, conjugated by these identifications.
(blueprint: `lem-weil-pbc-derived-exchange-termwise`) -/
lemma Etale.derivedBaseChangeMapPlus_app_eq_termwise (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A))
    (I : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology A))
    (e : K ≅ DerivedCategory.Plus.Qh.obj I) (hI : CochainComplex.IsKInjective I.1.as)
    (J : HomotopyCategory.Plus (Sheaf X'.smallEtaleTopology A))
    (s : ((g')^*[A]).mapHomotopyCategoryPlus.obj I ⟶ J)
    [IsIso (DerivedCategory.Plus.Qh.map s)] (hJ : CochainComplex.IsKInjective J.1.as) :
    haveI := (f)_*[A].isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective I hI
    haveI := (f')_*[A].isIso_rightDerivedFunctorPlusUnit_app_of_isKInjective J hJ
    (Etale.derivedBaseChangeMapPlus A sq).app K =
      ((g)^*[A]).mapDerivedCategoryPlus.map ((f)_*[A].rightDerivedFunctorPlus.map e.hom ≫
          inv ((f)_*[A].rightDerivedFunctorPlusUnit.app I)) ≫
        ((g)^*[A]).mapDerivedCategoryPlusFactorsh.hom.app
          ((f)_*[A].mapHomotopyCategoryPlus.obj I) ≫
        DerivedCategory.Plus.Qh.map
          ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap A sq)).app I ≫
            (f')_*[A].mapHomotopyCategoryPlus.map s) ≫
        (f')_*[A].rightDerivedFunctorPlusUnit.app J ≫
        (f')_*[A].rightDerivedFunctorPlus.map
          (inv (DerivedCategory.Plus.Qh.map s) ≫
            ((g')^*[A]).mapDerivedCategoryPlusFactorsh.inv.app I ≫
            ((g')^*[A]).mapDerivedCategoryPlus.map e.inv) := by
  symm
  rw [Etale.derivedBaseChangeMapPlus_termwise_comm_assoc A sq K I e J s,
    ← Functor.map_comp_assoc, ← Functor.map_comp]
  simp only [assoc, IsIso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc, Iso.hom_inv_id_app_assoc]
  simp only [← Functor.map_comp, Iso.hom_inv_id]
  simp

end AlgebraicGeometry
