/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q150
-/
module

public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Unit normalization of the full and bounded below right derived functors

Source: Stacks Project, Derived Categories, Tags 070K, 070I, 070J and 013K;
unit-normalized assembly of these results
(blueprint: lem-sfb-additive-derived-plus-unit-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe wA wB vA vB uA uB

open CategoryTheory

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
  [EnoughInjectives A] (F : A ⥤ B) [F.Additive]
  (h : ∀ K : CochainComplex A ℤ,
    ∃ (I : CochainComplex A ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s)

/-- The total derived pair and its canonical values, together with the unique
unit-normalized bounded below comparison, including its formulas on injective
representatives and arbitrary injective resolutions. All resolution arrows below
are homotopy classes; the quotient is full, so this includes every chain resolution.
The final equality for full derived values quantifies over every derived morphism.

Source: Stacks Project, Derived Categories, Tags 070K, 070I, 070J and 013K
(blueprint: lem-sfb-additive-derived-plus-unit-normalization).

Proof:
1. Additivity preserves the homotopy equation, shifts and the cone differential, so
   degreewise F followed by Qh is triangulated (lem-pur-homotopy-category-triangulated).
   Apply lem-weil-pbc-kinjective-total-derived to h. The recorded pair of
   def-sfb-right-derived-functor is universal and its unit is invertible on K-injectives.
   Localization inverts s, giving exactly RF(Qs) followed by the inverse unit.
2. The bounded below pair is lem-weil-pbc-right-derived-plus-injective. On a bounded
   below injective J, lem-weil-pbc-bounded-below-injectives-kinjective makes the full
   unit invertible too. Define a_J as inverse full unit followed by the included
   bounded below unit. The two unit naturality equations give naturality of a_J
   for homotopy classes between such J.
3. By lem-weil-pbc-dplus-injective-representative choose q_X : X ≅ Qh(J_X).
   Set theta_X = U(q_X) followed by a_J_X and V(q_X) inverse. For any derived
   morphism, lem-weil-pbc-kinjective-hom-derived supplies its unique homotopy lift
   between these representatives. Step 2 proves naturality of theta.
4. Apply the same Hom bijection to the transition between two representatives.
   Naturality of a_J and cancellation prove that theta_X is independent of q_X.
   Taking q_X to be the identity gives the stated formula on injective J.
5. Lift a resolution of any bounded below complex into an injective J by that Hom
   bijection. Naturality of theta and of both units, followed by cancellation of
   the invertible image of the resolution, gives the unit equation on every complex.
6. Any comparison satisfying the unit equation equals a_J on injectives. Its
   naturality along q_X forces every component, proving uniqueness. Its target is
   bounded below, so its source is too (def-weil-pbc-bounded-derived-subcategories).
   Additivity preserves the lower bound of FJ.
7. Naturality along any injective resolution s gives the displayed resolution
   formula after multiplying by V(Qh(s)) inverse. This proves independence for
   every such s, and naturality holds for all derived morphisms by step 3.
8. For full K-injective resolutions s and t and any derived u, lift
   Qh(s) inverse followed by u followed by Qh(t) to a unique homotopy class f
   (lem-weil-pbc-kinjective-hom-derived). Unit naturality gives the last equality.
   For u the identity it identifies the values from two resolutions. The lift of
   the inverse transition is inverse to f by injectivity of the Hom bijection;
   hence F(f) is invertible as well. No step assumes left exactness of F. -/
theorem additiveDerivedPlus_unit_normalization
    (Rplus : DerivedCategory.Plus A ⥤ DerivedCategory.Plus B)
    (α : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ Rplus)
    [Rplus.IsRightDerivedFunctor α (HomotopyCategory.Plus.quasiIso A)] :
    (∀ G : DerivedCategory A ⥤ DerivedCategory B,
      Function.Bijective
        (fun β : F.rightDerivedFunctorOfQuasiIsoResolutions h ⟶ G ↦
          F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h ≫
            Functor.whiskerLeft DerivedCategory.Qh β)) ∧
    (∀ (I : CochainComplex A ℤ) (_ : I.IsKInjective),
      ∃ hη : IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)),
      ∀ (K : HomotopyCategory A (ComplexShape.up ℤ))
        (s : K ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)
        (_ : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) s),
        IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Qh.map s) ≫
          @CategoryTheory.inv _ _ _ _ ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) hη) ∧
        ∀ (J : CochainComplex A ℤ) (_ : J.IsKInjective)
          (hη' : IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
            ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)))
          (L : HomotopyCategory A (ComplexShape.up ℤ))
          (t : L ⟶ (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)
          (_ : HomotopyCategory.quasiIso A (ComplexShape.up ℤ) t)
          (u : DerivedCategory.Qh.obj K ⟶ DerivedCategory.Qh.obj L)
          (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I ⟶
            (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J),
          DerivedCategory.Qh.map s ≫ DerivedCategory.Qh.map f =
            u ≫ DerivedCategory.Qh.map t →
          (F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Qh.map s) ≫
            @CategoryTheory.inv _ _ _ _ ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) hη ≫
            DerivedCategory.Qh.map ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map f) =
          (F.rightDerivedFunctorOfQuasiIsoResolutions h).map u ≫
            (F.rightDerivedFunctorOfQuasiIsoResolutions h).map (DerivedCategory.Qh.map t) ≫
            @CategoryTheory.inv _ _ _ _ ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app
              ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J)) hη') ∧
    ∃ θ : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
        Rplus ⋙ DerivedCategory.Plus.ι,
      (∀ K : HomotopyCategory.Plus A,
        (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app K.obj ≫
          θ.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (α.app K)) ∧
      (∀ θ' : DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctorOfQuasiIsoResolutions h ≅
          Rplus ⋙ DerivedCategory.Plus.ι,
        (∀ K : HomotopyCategory.Plus A,
          (F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app K.obj ≫
            θ'.hom.app (DerivedCategory.Plus.Qh.obj K) =
          DerivedCategory.Plus.ι.map (α.app K)) → θ' = θ) ∧
      (∀ X : DerivedCategory.Plus A,
        (DerivedCategory.TStructure.t (C := B)).plus
          ((F.rightDerivedFunctorOfQuasiIsoResolutions h).obj X.obj)) ∧
      (∀ J : HomotopyCategory.Plus A, (∀ n : ℤ, Injective (J.obj.as.X n)) →
        ∃ (hη : IsIso ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app J.obj))
          (_ : IsIso (α.app J)),
          θ.hom.app (DerivedCategory.Plus.Qh.obj J) =
            @CategoryTheory.inv _ _ _ _
              ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app J.obj) hη ≫
              DerivedCategory.Plus.ι.map (α.app J) ∧
          (∀ (K : HomotopyCategory.Plus A) (s : K ⟶ J)
              (_ : HomotopyCategory.Plus.quasiIso A s),
            ∃ hs : IsIso (DerivedCategory.Plus.ι.map
                (Rplus.map (DerivedCategory.Plus.Qh.map s))),
              θ.hom.app (DerivedCategory.Plus.Qh.obj K) =
                (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
                  (DerivedCategory.Qh.map s.hom) ≫
                @CategoryTheory.inv _ _ _ _
                  ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app J.obj) hη ≫
                DerivedCategory.Plus.ι.map (α.app J) ≫
                @CategoryTheory.inv _ _ _ _ (DerivedCategory.Plus.ι.map
                  (Rplus.map (DerivedCategory.Plus.Qh.map s))) hs) ∧
          (∀ (X : DerivedCategory.Plus A) (q : X ≅ DerivedCategory.Plus.Qh.obj J),
            θ.hom.app X =
              (F.rightDerivedFunctorOfQuasiIsoResolutions h).map
                (DerivedCategory.Plus.ι.map q.hom) ≫
              @CategoryTheory.inv _ _ _ _
                ((F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h).app J.obj) hη ≫
              DerivedCategory.Plus.ι.map (α.app J) ≫
              DerivedCategory.Plus.ι.map (Rplus.map q.inv))) := by
  classical
  let RF := F.rightDerivedFunctorOfQuasiIsoResolutions h
  let η := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit h
  have hηplus (J : HomotopyCategory.Plus A)
      (hJ : ∀ n : ℤ, Injective (J.obj.as.X n)) : IsIso (η.app J.obj) := by
    obtain ⟨J, hJplus⟩ := J
    obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective J
    obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hJplus
    have : ∀ n : ℤ, Injective (I.X n) := hJ
    have : CochainComplex.IsKInjective I := CochainComplex.isKInjective_of_injective I n
    exact F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
  let U : DerivedCategory.Plus A ⥤ DerivedCategory B := DerivedCategory.Plus.ι ⋙ RF
  let V : DerivedCategory.Plus A ⥤ DerivedCategory B := Rplus ⋙ DerivedCategory.Plus.ι
  let ηplus : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
      DerivedCategory.Plus.ι ⟶ DerivedCategory.Plus.Qh ⋙ U :=
    Functor.whiskerLeft (HomotopyCategory.Plus.ι A) η
  let αplus : F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
      DerivedCategory.Plus.ι ⟶ DerivedCategory.Plus.Qh ⋙ V :=
    Functor.whiskerRight α DerivedCategory.Plus.ι
  have : U.IsRightDerivedFunctor ηplus (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
      (fun J ↦ hηplus _ (fun n ↦ inferInstance))
  have : V.IsRightDerivedFunctor αplus (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
      (fun J ↦ inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map (α.app _))))
  let θ : U ≅ V := Functor.rightDerivedUnique U V ηplus αplus
    (HomotopyCategory.Plus.quasiIso A)
  have hθ (K : HomotopyCategory.Plus A) :
      η.app K.obj ≫ θ.hom.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.ι.map (α.app K) := by
    exact (U.rightDerivedNatTrans_app V ηplus αplus
      (HomotopyCategory.Plus.quasiIso A) (𝟙 _) K).trans (Category.id_comp _)
  refine ⟨F.rightDerivedFunctorOfQuasiIsoResolutions_universal h, ?_, θ, hθ, ?_, ?_, ?_⟩
  · intro I hI
    have := hI
    have := F.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso h I
    refine ⟨inferInstance, ?_⟩
    intro K s hs
    have : IsIso (DerivedCategory.Qh.map s) :=
      Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A _) s hs
    refine ⟨inferInstance, ?_⟩
    intro J hJ hη' L t ht u f hf
    have := hη'
    have hn : CategoryTheory.inv (η.app ((HomotopyCategory.quotient A (.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map f) =
        RF.map (DerivedCategory.Qh.map f) ≫
          CategoryTheory.inv (η.app ((HomotopyCategory.quotient A (.up ℤ)).obj J)) := by
      apply (cancel_mono (η.app ((HomotopyCategory.quotient A (.up ℤ)).obj J))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      have hnat := η.naturality f
      dsimp only [Functor.comp_map] at hnat
      rw [hnat]
      simp [RF]
    change RF.map (DerivedCategory.Qh.map s) ≫ _ ≫ _ = _
    rw [hn, ← Category.assoc, ← RF.map_comp, hf, RF.map_comp, Category.assoc]
  · intro θ' hθ'
    apply Iso.ext
    apply U.rightDerived_ext ηplus (HomotopyCategory.Plus.quasiIso A)
    ext K
    exact (hθ' K).trans (hθ K).symm
  · intro X
    exact (DerivedCategory.TStructure.t (C := B)).plus.prop_of_iso
      (θ.app X).symm (Rplus.obj X).property
  · intro J hJ
    have := hηplus J hJ
    have : ∀ n : ℤ, Injective (J.obj.as.X n) := hJ
    refine ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩
    · exact (IsIso.eq_inv_comp _).mpr (hθ J)
    · intro K s hs
      have : IsIso (DerivedCategory.Plus.Qh.map s) :=
        Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A) s hs
      refine ⟨inferInstance, ?_⟩
      apply (cancel_mono (DerivedCategory.Plus.ι.map
        (Rplus.map (DerivedCategory.Plus.Qh.map s)))).mp
      simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      rw [← (IsIso.eq_inv_comp _).mpr (hθ J)]
      exact (θ.hom.naturality (DerivedCategory.Plus.Qh.map s)).symm
    · intro X q
      have hform := (IsIso.eq_inv_comp _).mpr (hθ J)
      calc
        θ.hom.app X = U.map q.hom ≫ θ.hom.app _ ≫ V.map q.inv := by
          rw [← Category.assoc, θ.hom.naturality q.hom]
          simp only [Category.assoc, ← V.map_comp, q.hom_inv_id, V.map_id,
            Category.comp_id]
        _ = _ := by
          simpa only [U, V, RF, η, Functor.comp_map, Category.assoc] using
            congrArg (fun z ↦ U.map q.hom ≫ z ≫ V.map q.inv) hform

end CategoryTheory.Functor
