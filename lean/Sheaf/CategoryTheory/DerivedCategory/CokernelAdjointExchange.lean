/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact comparison of derived cokernel adjunctions

The comparison is the inverse of the mate of the exact right-adjoint square.
Multiplication short exact sequences show that the target universal counit computes
on the image of a resolving object. No preservation of the resolving class is needed.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact Category.assoc _ _ _
end
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R') (e : E ⋙ G ≅ F ⋙ E')
  (β : F.mapDerivedCategory ⋙ L' ⟶ L ⋙ G.mapDerivedCategory)
  (hβ : ∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
    R'.mapDerivedCategory.map (β.app X) =
    F.mapDerivedCategory.map (ad.unit.app X) ≫
      (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X))
  (hunit : ∀ P, ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ∀ P, ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
include hβ hunit hunit' he in
private theorem mate_computes (P : CochainComplex A ℤ) :
    β.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (ε.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) =
    L'.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let E'c := E'.mapHomologicalComplex (.up ℤ)
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Gc := G.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let R'c := R'.mapHomologicalComplex (.up ℤ)
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  let ρc := NatIso.mapHomologicalComplex ρ (.up ℤ)
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hec : Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P) ≫ R'c.map (ec.hom.app P) =
        (a'.mapHomologicalComplex (.up ℤ)).unit.app (Fc.obj P) := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact he (P.X i)
  apply (ad'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, CategoryTheory.Functor.map_comp]
  apply (cancel_mono
    (R'.mapDerivedCategoryFactors.hom.app (E'c.obj (Fc.obj P)))).1
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hβ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρd.hom.naturality (ε.app P))]
  erw [R'.mapDerivedCategoryFactors.hom.naturality (ec.hom.app P)]
  erw [reassoc_of% (square_factors R F G R' ρ (Ec.obj P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  rw [hunit]
  rw [reassoc_of% (F.mapDerivedCategoryFactors.hom.naturality
    ((a.mapHomologicalComplex (.up ℤ)).unit.app P))]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  change F.mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map (Fc.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ρc.hom.app (Ec.obj P)) ≫ DerivedCategory.Q.map (R'c.map (ec.hom.app P)) = _
  rw [← CategoryTheory.Functor.map_comp]
  erw [Category.assoc, hec]
  simp only [CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  erw [← reassoc_of% (ad'.unit.naturality (F.mapDerivedCategoryFactors.hom.app P))]
  erw [hunit']
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R')
private noncomputable def adjoint_exchange : F ⋙ L' ⟶ L ⋙ G :=
  ((mateEquiv a a').symm (TwoSquare.mk R G F R' ρ.hom)).natTrans
private theorem adjoint_exchange_unit (X : A) :
    a'.unit.app (F.obj X) ≫ R'.map ((adjoint_exchange a a' F G ρ).app X) =
      F.map (a.unit.app X) ≫ ρ.hom.app (L.obj X) := by
  exact (unit_mateEquiv_symm a a' (TwoSquare.mk R G F R' ρ.hom) X).symm
variable [HasShift A ℤ] [HasShift B ℤ] [HasShift A' ℤ] [HasShift B' ℤ]
  [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
  [a.CommShift ℤ] [a'.CommShift ℤ] [F.CommShift ℤ] [G.CommShift ℤ]
  [NatTrans.CommShift ρ.hom ℤ]
private theorem adjoint_exchange_commShift :
    NatTrans.CommShift (adjoint_exchange a a' F G ρ) ℤ := by
  change NatTrans.CommShift
    ((F ⋙ L').leftUnitor.inv ≫
      CategoryTheory.Functor.whiskerRight a.unit (F ⋙ L') ≫
      ((L ⋙ R).associator F L').inv ≫
      CategoryTheory.Functor.whiskerRight (L.associator R F).hom L' ≫
      CategoryTheory.Functor.whiskerRight
        (CategoryTheory.Functor.whiskerLeft L ρ.hom) L' ≫
      CategoryTheory.Functor.whiskerRight (L.associator G R').inv L' ≫
      ((L ⋙ G).associator R' L').hom ≫
      CategoryTheory.Functor.whiskerLeft (L ⋙ G) a'.counit ≫
      (L ⋙ G).rightUnitor.hom) ℤ
  infer_instance
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  [ad.CommShift ℤ] [ad'.CommShift ℤ]
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R') (e : E ⋙ G ≅ F ⋙ E')
  (hunit : ∀ P, ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hunit' : ∀ P, ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))
  (he : ∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
    R'.map (e.hom.app X) = a'.unit.app (F.obj X))
  (H : CochainComplex A ℤ → Prop)
  (hres : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
  (hcomp : ∀ P, H P → IsIso (ε.app P) ∧
    IsIso (ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P)))
include hunit hunit' he hres hcomp in
private theorem derived_exchange :
    ∃ θ : L ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L',
      NatTrans.CommShift θ.hom ℤ ∧
      (∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
        R'.mapDerivedCategory.map (θ.inv.app X) =
        F.mapDerivedCategory.map (ad.unit.app X) ≫
          (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X)) ∧
      ∀ P : CochainComplex A ℤ,
        θ.hom.app (DerivedCategory.Q.obj P) ≫
          L'.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        G.mapDerivedCategory.map (ε.app P) ≫
          G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  classical
  let ρd := CategoryTheory.Functor.mapDerivedCategorySquareIso ρ
  have : NatTrans.CommShift ρd.hom ℤ := by
    dsimp only [ρd, CategoryTheory.Functor.mapDerivedCategorySquareIso,
      Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let β := adjoint_exchange ad ad' F.mapDerivedCategory G.mapDerivedCategory ρd
  have hβ := adjoint_exchange_unit ad ad' F.mapDerivedCategory G.mapDerivedCategory ρd
  have hb (P : CochainComplex A ℤ) := mate_computes E E' R R' a a' L L' ad ad'
    ε ε' F G ρ e β hβ hunit hunit' he P
  have hP (P : CochainComplex A ℤ) (hp : H P) :
      IsIso (β.app (DerivedCategory.Q.obj P)) := by
    obtain ⟨hε, hε'⟩ := hcomp P hp
    have : IsIso (β.app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategory.map (ε.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P)) := by
      rw [hb]
      infer_instance
    exact IsIso.of_isIso_comp_right (β.app (DerivedCategory.Q.obj P))
      (G.mapDerivedCategory.map (ε.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P))
  have hK (K : CochainComplex A ℤ) : IsIso (β.app (DerivedCategory.Q.obj K)) := by
    obtain ⟨P, p, hp, hq⟩ := hres K
    have : QuasiIso p := hq
    have := hP P hp
    have : IsIso ((F.mapDerivedCategory ⋙ L').map (DerivedCategory.Q.map p) ≫
        β.app (DerivedCategory.Q.obj K)) := by
      rw [β.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((F.mapDerivedCategory ⋙ L').map (DerivedCategory.Q.map p))
      (β.app (DerivedCategory.Q.obj K))
  have hX (X : DerivedCategory A) : IsIso (β.app X) := by
    let e := DerivedCategory.Q.objObjPreimageIso X
    have := hK (DerivedCategory.Q.objPreimage X)
    have : IsIso ((F.mapDerivedCategory ⋙ L').map e.hom ≫ β.app X) := by
      rw [β.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left ((F.mapDerivedCategory ⋙ L').map e.hom) (β.app X)
  have : IsIso β := NatIso.isIso_of_isIso_app β
  have : NatTrans.CommShift β ℤ := adjoint_exchange_commShift _ _ _ _ _
  let θ := (asIso β).symm
  refine ⟨θ, ?_, hβ, ?_⟩
  · change NatTrans.CommShift (inv β) ℤ
    exact NatTrans.CommShift.of_isIso _ _
  intro P
  apply (cancel_epi (β.app (DerivedCategory.Q.obj P))).1
  change β.app (DerivedCategory.Q.obj P) ≫
    (inv β).app (DerivedCategory.Q.obj P) ≫ _ = _
  change (asIso β).hom.app (DerivedCategory.Q.obj P) ≫
    (asIso β).inv.app (DerivedCategory.Q.obj P) ≫ _ = _
  erw [Iso.hom_inv_id_app_assoc]
  exact (hb P).symm
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian A'] (n : ℕ)
  (E : A ⥤ B) (R : B ⥤ A) (E' : A' ⥤ B') (R' : B' ⥤ A') [R'.Full] [R'.Faithful]
  (a : E ⊣ R) (a' : E' ⊣ R')
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hz' : ∀ X : A', (n • 𝟙 X) ≫ a'.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
  (hc' : ∀ X : A', IsColimit (CokernelCofork.ofπ (a'.unit.app X) (hz' X)))
  (F : A ⥤ A') [F.Additive] [PreservesFiniteColimits F] (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R')
include hc hc' in
private theorem ordinary_exchange :
    ∃ e : E ⋙ G ≅ F ⋙ E', ∀ X : A,
      F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫ R'.map (e.hom.app X) =
        a'.unit.app (F.obj X) := by
  classical
  let u (X : A) := F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X)
  let b (X : A) := (a'.homEquiv (F.obj X) (G.obj (E.obj X))).symm (u X)
  have hb (X : A) : a'.unit.app (F.obj X) ≫ R'.map (b X) = u X := by
    exact (Adjunction.homEquiv_unit a' _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hzero (X : A) : (n • 𝟙 (F.obj X)) ≫ F.map (a.unit.app X) = 0 := by
    rw [← F.map_id, ← F.map_nsmul, ← F.map_comp, hz, F.map_zero]
  have hzero' (X : A) : (n • 𝟙 (F.obj X)) ≫ u X = 0 := by
    dsimp only [u]
    rw [← Category.assoc, hzero, zero_comp]
  have hU (X : A) : IsColimit (CokernelCofork.ofπ (u X) (hzero' X)) := by
    have hFm : IsColimit (CokernelCofork.ofπ (F.map (a.unit.app X)) (hzero X)) := by
      let h := isColimitCoforkMapOfIsColimit' F (hz X) (hc X)
      exact CokernelCofork.isColimitOfIsColimitOfIff' h (n • 𝟙 (F.obj X)) (by
        intro Z k
        simp only [F.map_nsmul, F.map_id])
    exact IsColimit.ofIsoColimit hFm (Cofork.ext (ρ.app (E.obj X)) rfl)
  have hiso (X : A) : IsIso (b X) := by
    have hepi : Epi (a'.unit.app (F.obj X)) := Cofork.IsColimit.epi (hc' (F.obj X))
    let e := (hc' (F.obj X)).coconePointUniqueUpToIso (hU X)
    have he : a'.unit.app (F.obj X) ≫ e.hom = u X :=
      (hc' (F.obj X)).comp_coconePointUniqueUpToIso_hom (hU X) WalkingParallelPair.one
    have heq : R'.map (b X) = e.hom := (cancel_epi (a'.unit.app (F.obj X))).1
      ((hb X).trans he.symm)
    have : IsIso (R'.map (b X)) := by rw [heq]; infer_instance
    exact isIso_of_reflects_iso (b X) R'
  let β : F ⋙ E' ⟶ E ⋙ G :=
    { app := b
      naturality := by
        intro X Y f
        apply (a'.homEquiv (F.obj X) (G.obj (E.obj Y))).injective
        rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
        simp only [R'.map_comp, ← Category.assoc]
        erw [← a'.unit.naturality (F.map f), Category.assoc, hb, hb]
        dsimp only [u]
        simp only [Category.assoc, CategoryTheory.Functor.id_map]
        rw [← F.map_comp_assoc]
        erw [a.unit.naturality f, F.map_comp]
        simp only [Category.assoc]
        exact congrArg (fun z ↦ F.map (a.unit.app X) ≫ z)
          (ρ.hom.naturality (E.map f)) }
  let e := (NatIso.ofComponents (fun X ↦ asIso (β.app X))
    (fun f ↦ β.naturality f)).symm
  refine ⟨e, ?_⟩
  intro X
  rw [← Category.assoc]
  change u X ≫ R'.map (inv (b X)) = _
  rw [← hb, Category.assoc, ← R'.map_comp, IsIso.hom_inv_id, R'.map_id]
  erw [Category.comp_id]
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
section
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R) (L : DerivedCategory A ⥤ DerivedCategory B) (ad : L ⊣ R.mapDerivedCategory)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (H : CochainComplex A ℤ → Prop)
  (hres : ∀ K : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K),
    H P ∧ QuasiIso p)
  (hunit : ∀ P, H P → ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
include hres hunit in
private theorem unit_all (K : CochainComplex A ℤ) :
    ad.unit.app (DerivedCategory.Q.obj K) ≫ R.mapDerivedCategory.map (ε.app K) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj K) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let Q : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let τ : Q ⟶ Ec ⋙ Rc ⋙ Q :=
    CategoryTheory.Functor.whiskerLeft Q ad.unit ≫
      (CategoryTheory.Functor.associator Q L R.mapDerivedCategory).inv ≫
      CategoryTheory.Functor.whiskerRight ε R.mapDerivedCategory ≫
      (CategoryTheory.Functor.associator Ec DerivedCategory.Q R.mapDerivedCategory).hom ≫
      CategoryTheory.Functor.whiskerLeft Ec R.mapDerivedCategoryFactors.hom
  let σ : Q ⟶ Ec ⋙ Rc ⋙ Q :=
    Q.leftUnitor.inv ≫
      CategoryTheory.Functor.whiskerRight (a.mapHomologicalComplex (.up ℤ)).unit Q ≫
      (CategoryTheory.Functor.associator Ec Rc Q).hom
  have hP (P : CochainComplex A ℤ) (h : H P) : τ.app P = σ.app P := by
    simp only [τ, σ, NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
      CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.associator_inv_app,
      CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.leftUnitor_inv_app,
      Category.id_comp]
    repeat' first | erw [Category.id_comp] | erw [Category.comp_id]
    exact hunit P h
  obtain ⟨P, p, h, hp⟩ := hres K
  have : QuasiIso p := hp
  have heq : τ.app K = σ.app K := by
    apply (cancel_epi (Q.map p)).1
    rw [τ.naturality p, σ.naturality p, hP P h]
  simp only [τ, σ, NatTrans.comp_app, CategoryTheory.Functor.whiskerLeft_app,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.associator_inv_app,
    CategoryTheory.Functor.associator_hom_app, CategoryTheory.Functor.leftUnitor_inv_app,
    Category.id_comp] at heq
  repeat' first | erw [Category.id_comp] at heq | erw [Category.comp_id] at heq
  exact heq
end

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
section
variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  [Category* B] [Abelian B] [HasDerivedCategory B]
  (n : ℕ) (E : A ⥤ B) [E.Additive] (R : B ⥤ A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (a : E ⊣ R)
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
include hz in
omit [HasDerivedCategory A] [HasDerivedCategory B]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
private theorem complex_unit_zero (P : CochainComplex A ℤ) :
    (n • 𝟙 P) ≫ (a.mapHomologicalComplex (.up ℤ)).unit.app P = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, HomologicalComplex.nsmul_f_apply,
    HomologicalComplex.id_f, HomologicalComplex.zero_f,
    Adjunction.mapHomologicalComplex_unit_app_f]
  exact hz (P.X i)
include hc in
omit [HasDerivedCategory A] [HasDerivedCategory B]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R] in
private theorem complex_unit_shortExact (P : CochainComplex A ℤ)
    (hm : ∀ i : ℤ, Mono (n • 𝟙 (P.X i))) :
    (ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
      (complex_unit_zero n E R a hz P)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have := hm i
  have : Epi (a.unit.app (P.X i)) := Cofork.IsColimit.epi (hc (P.X i))
  have hs : (ShortComplex.mk (n • 𝟙 (P.X i)) (a.unit.app (P.X i))
      (hz (P.X i))).ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (hc (P.X i)) }
  convert! hs using 1

variable (L : DerivedCategory A ⥤ DerivedCategory B)
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  [R.ReflectsIsomorphisms]
include hc in
private theorem computes_n_monic (P : CochainComplex A ℤ)
    (hm : ∀ i : ℤ, Mono (n • 𝟙 (P.X i)))
    (hres : ∃ (Q : CochainComplex A ℤ) (q : Q ⟶ P),
      (∀ i : ℤ, Mono (n • 𝟙 (Q.X i))) ∧ IsIso (ε.app Q) ∧ QuasiIso q) :
    IsIso (ε.app P) := by
  obtain ⟨Q, q, hmQ, hεQ, hq⟩ := hres
  have : QuasiIso q := hq
  have : IsIso (ε.app Q) := hεQ
  let Ec := E.mapHomologicalComplex (.up ℤ)
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let SQ := ShortComplex.mk (n • 𝟙 Q) ((a.mapHomologicalComplex (.up ℤ)).unit.app Q)
    (complex_unit_zero n E R a hz Q)
  let SP := ShortComplex.mk (n • 𝟙 P) ((a.mapHomologicalComplex (.up ℤ)).unit.app P)
    (complex_unit_zero n E R a hz P)
  have hSQ : SQ.ShortExact := complex_unit_shortExact n E R a hz hc Q hmQ
  have hSP : SP.ShortExact := complex_unit_shortExact n E R a hz hc P hm
  let f : SQ ⟶ SP := ShortComplex.homMk q q (Rc.map (Ec.map q)) (by
    change q ≫ (n • 𝟙 P) = (n • 𝟙 Q) ≫ q
    simp only [Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id])
    (by exact (a.mapHomologicalComplex (.up ℤ)).unit.naturality q)
  have hR : IsIso (DerivedCategory.Q.map (Rc.map (Ec.map q))) :=
    isIso₃_of_isIso₁₂ (DerivedCategory.triangleOfSES.map hSQ hSP f)
      (DerivedCategory.triangleOfSES_distinguished hSQ)
      (DerivedCategory.triangleOfSES_distinguished hSP)
      (by change IsIso (DerivedCategory.Q.map q); infer_instance)
      (by change IsIso (DerivedCategory.Q.map q); infer_instance)
  have hE : IsIso (R.mapDerivedCategory.map (DerivedCategory.Q.map (Ec.map q))) :=
    (NatIso.isIso_map_iff R.mapDerivedCategoryFactors (Ec.map q)).2 hR
  have hRD : R.mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro i
    have : IsIso (R.map ((DerivedCategory.homologyFunctor _ i).map g)) :=
      (NatIso.isIso_map_iff (R.mapDerivedCategoryHomologyFunctorIso i) g).2
        (by rw [CategoryTheory.Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ R
  have : IsIso (DerivedCategory.Q.map (Ec.map q)) :=
    isIso_of_reflects_iso _ R.mapDerivedCategory
  have heq := ε.naturality q
  change L.map (DerivedCategory.Q.map q) ≫ ε.app P =
    ε.app Q ≫ DerivedCategory.Q.map (Ec.map q) at heq
  have : IsIso (L.map (DerivedCategory.Q.map q) ≫ ε.app P) := by
    rw [heq]
    infer_instance
  exact IsIso.of_isIso_comp_left (L.map (DerivedCategory.Q.map q)) (ε.app P)
end


section CokernelExchange
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (n : ℕ) (E : A ⥤ B) (E' : A' ⥤ B') [E.Additive] [E'.Additive]
  (R : B ⥤ A) (R' : B' ⥤ A') [R.Additive] [R'.Additive] [R'.Full] [R'.Faithful]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (a : E ⊣ R) (a' : E' ⊣ R')
  (L : DerivedCategory A ⥤ DerivedCategory B)
  (L' : DerivedCategory A' ⥤ DerivedCategory B')
  [L.CommShift ℤ] [L'.CommShift ℤ]
  (ad : L ⊣ R.mapDerivedCategory) (ad' : L' ⊣ R'.mapDerivedCategory)
  [ad.CommShift ℤ] [ad'.CommShift ℤ]
  (ε : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (ε' : DerivedCategory.Q ⋙ L' ⟶ E'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (F : A ⥤ A') (G : B ⥤ B') [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (ρ : R ⋙ F ≅ G ⋙ R')
  (hz : ∀ X : A, (n • 𝟙 X) ≫ a.unit.app X = 0)
  (hz' : ∀ X : A', (n • 𝟙 X) ≫ a'.unit.app X = 0)
  (hc : ∀ X : A, IsColimit (CokernelCofork.ofπ (a.unit.app X) (hz X)))
  (hc' : ∀ X : A', IsColimit (CokernelCofork.ofπ (a'.unit.app X) (hz' X)))
  (H : CochainComplex A ℤ → Prop) (H' : CochainComplex A' ℤ → Prop)
  (hres : ∀ K, ∃ (P : CochainComplex A ℤ) (p : P ⟶ K), H P ∧ QuasiIso p)
  (hres' : ∀ K, ∃ (P : CochainComplex A' ℤ) (p : P ⟶ K), H' P ∧ QuasiIso p)
  (hm : ∀ P, H P → ∀ i : ℤ, Mono (n • 𝟙 (P.X i)))
  (hm' : ∀ P, H' P → ∀ i : ℤ, Mono (n • 𝟙 (P.X i)))
  (hcomp : ∀ P, H P → IsIso (ε.app P))
  (hcomp' : ∀ P, H' P → IsIso (ε'.app P))
  (hu : ∀ P, H P → ad.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (ε.app P) ≫
    R.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P))
  (hu' : ∀ P, H' P → ad'.unit.app (DerivedCategory.Q.obj P) ≫
    R'.mapDerivedCategory.map (ε'.app P) ≫
    R'.mapDerivedCategoryFactors.hom.app ((E'.mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map ((a'.mapHomologicalComplex (.up ℤ)).unit.app P))

include hc hc' hres hres' hm hm' hcomp hcomp' hu hu' in
/-- Exact inverse images commute with derived cokernel adjunctions, with their mate and
universal-counit normalizations.
Source: Stacks Project, Derived Categories, derived adjunction lemma and the exact-functor
comparison, Tags 0152 and 09T5
(blueprint: lem-sfb-derived-cokernel-adjoint-exchange).
Proof: the ordinary mate is an isomorphism because both units are cokernels of n and
F preserves cokernels. Extend the derived unit formulas from resolving objects by
naturality along resolution quasi-isomorphisms. For a complex with degreewise injective n,
the multiplication sequence and a resolving quasi-isomorphism give a morphism of short
exact sequences whose first two maps are quasi-isomorphisms. The third map is therefore
a quasi-isomorphism. Exact faithful restriction reflects this property, so the universal
counit computes on this complex. In particular it computes on F of every source resolving
object. The derived mate is consequently invertible on those objects, hence everywhere
by resolutions and essential surjectivity of localization. Its inverse is the required
comparison. The adjunction mate identities give the unit formula; applying the target
adjunction to the counit comparison reduces it to the two normalized unit formulas and
the ordinary unit square. Units, counits and the exact right square commute with shifts,
so their mate and its inverse do too. -/
theorem CategoryTheory.derivedCokernelAdjointExchange :
    ∃ e : E ⋙ G ≅ F ⋙ E',
      (∀ X, F.map (a.unit.app X) ≫ ρ.hom.app (E.obj X) ≫
        R'.map (e.hom.app X) = a'.unit.app (F.obj X)) ∧
      ∃ θ : L ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ L',
        NatTrans.CommShift θ.hom ℤ ∧
        (∀ X, ad'.unit.app (F.mapDerivedCategory.obj X) ≫
          R'.mapDerivedCategory.map (θ.inv.app X) =
          F.mapDerivedCategory.map (ad.unit.app X) ≫
            (CategoryTheory.Functor.mapDerivedCategorySquareIso ρ).hom.app (L.obj X)) ∧
        ∀ P : CochainComplex A ℤ,
          θ.hom.app (DerivedCategory.Q.obj P) ≫
            L'.map (F.mapDerivedCategoryFactors.hom.app P) ≫
            ε'.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
          G.mapDerivedCategory.map (ε.app P) ≫
            G.mapDerivedCategoryFactors.hom.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app P) := by
  obtain ⟨e, he⟩ := ordinary_exchange n E R E' R' a a' hz hz' hc hc' F G ρ
  refine ⟨e, he, ?_⟩
  apply derived_exchange E E' R R' a a' L L' ad ad' ε ε' F G ρ e
    (unit_all E R a L ad ε H hres hu) (unit_all E' R' a' L' ad' ε' H' hres' hu') he H hres
  intro P hp
  refine ⟨hcomp P hp, ?_⟩
  apply computes_n_monic n E' R' a' hz' hc' L' ε'
  · intro i
    have := hm P hp i
    simpa only [CategoryTheory.Functor.mapHomologicalComplex_obj_X,
      F.map_nsmul, F.map_id] using!
      (show Mono (F.map (n • 𝟙 (P.X i))) from inferInstance)
  · obtain ⟨Q, q, hQ, hq⟩ := hres' ((F.mapHomologicalComplex (.up ℤ)).obj P)
    exact ⟨Q, q, hm' Q hQ, hcomp' Q hQ, hq⟩
end CokernelExchange
