/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF maintenance (s2long1)
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!
# Coherence of the derived pullback compositors along commuting squares

Formal coherence for the derived pullbacks of condensed module objects: identifications built from
`leftDerivedUpperStarComp`, `leftDerivedUpperStarId` and transports along equalities of morphisms
agree. Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

-- Own sub-namespace: the reproducer files are all imported by `WeilConjectures.lean` and each
-- re-declares the same names (and a local copy of `moduleObjectDerivedPullback`, which upstream
-- lives in `AlgebraicGeometry.ProEtale.CondensedRing`), so they must not clash.
namespace AlgebraicGeometry.ProEtale.CondensedRing.Reproducer

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- Verbatim copy of upstream `WeilConjectures/AlgebraicGeometry/CondensedModuleDerivedPushpull.lean`
(slopmaster2 a980a3df2135): the total left derived functor of `f^*` on module objects.
If you also import that module, delete this definition. -/
def moduleObjectDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (upperStar Λ f).leftDerivedFunctor

/-- Transport in the first variable of the compositor.
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncPullbackComp_congr_left {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ f g).hom.app C ≫
        eqToHom (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj
          ((moduleObjectDerivedPullback Λ g).obj C)) h) =
      eqToHom (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ (f ≫ g)).obj C) h) ≫
        (leftDerivedUpperStarComp Λ f' g).hom.app C := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- Transport in the second variable of the compositor.
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncPullbackComp_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g g' : Y ⟶ Z} (h : g = g')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (leftDerivedUpperStarComp Λ f g).hom.app C ≫
        (moduleObjectDerivedPullback Λ f).map
          (eqToHom (congrArg (fun g ↦ (moduleObjectDerivedPullback Λ g).obj C) h)) =
      eqToHom (congrArg (fun g ↦ (moduleObjectDerivedPullback Λ (f ≫ g)).obj C) h) ≫
        (leftDerivedUpperStarComp Λ f g').hom.app C := by
  subst h
  simp only [eqToHom_refl, Category.id_comp, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- Cancellation of `F.map ψ.hom ≫ F.map ψ.inv` for a natural isomorphism `ψ`.
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncMapCancel {𝒯 𝒰 𝒱 : Type*} [Category 𝒯] [Category 𝒰] [Category 𝒱] (F : 𝒰 ⥤ 𝒱)
    {G H : 𝒯 ⥤ 𝒰} (ψ : G ≅ H) (K : 𝒯) {R : 𝒱} (k : F.obj (G.obj K) ⟶ R) :
    F.map (ψ.hom.app K) ≫ F.map (ψ.inv.app K) ≫ k = k := by
  simp [← Functor.map_comp_assoc]

/-- Coherence along a section square, with all categories, functors and compositors as
variables (no family of categories).
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncSectionSquareCoherenceVars {𝒟B 𝒟A 𝒟A' 𝒟B' : Type*} {iB : Category 𝒟B}
    {iA : Category 𝒟A} {iA' : Category 𝒟A'} {iB' : Category 𝒟B'}
    {La : 𝒟B ⥤ 𝒟A} {La' : 𝒟B' ⥤ 𝒟A'} {Li : 𝒟A ⥤ 𝒟B} {Li' : 𝒟A' ⥤ 𝒟B'} {Lbb : 𝒟A ⥤ 𝒟A'}
    {Lb : 𝒟B ⥤ 𝒟B'}
    {P₁ P₂ : 𝒟B ⥤ 𝒟A'} {Q₁ I' : 𝒟B' ⥤ 𝒟B'} {R₁ R₂ : 𝒟A ⥤ 𝒟B'} {S₁ I : 𝒟B ⥤ 𝒟B}
    {T₁ T₁' T₂ T₂' T₃ T₄ T₄' T₅ : 𝒟B ⥤ 𝒟B'}
    (hP : P₁ = P₂) (hQ : Q₁ = I') (hR : R₁ = R₂) (hS : S₁ = I)
    (hT₁ : T₁ = T₁') (hT₁₂ : T₁' = T₂') (hT₂ : T₂ = T₂') (hT₂₃ : T₂ = T₃) (hT₃ : T₃ = Lb)
    (hT₁₄ : T₁ = T₄) (hT₄ : T₄ = T₄') (hT₄₅ : T₄' = T₅) (hT₅ : T₅ = Lb)
    (cbba : P₁ ≅ La ⋙ Lbb) (ca'b : P₂ ≅ Lb ⋙ La') (ci'a' : Q₁ ≅ La' ⋙ Li') (e' : I' ≅ 𝟭 _)
    (ci'bb : R₁ ≅ Lbb ⋙ Li') (cbi : R₂ ≅ Li ⋙ Lb) (cia : S₁ ≅ La ⋙ Li) (e : I ≅ 𝟭 _)
    (c₁ : T₁ ≅ La ⋙ R₁) (c₁' : T₁' ≅ P₁ ⋙ Li') (c₂' : T₂' ≅ P₂ ⋙ Li') (c₂ : T₂ ≅ Lb ⋙ Q₁)
    (c₃ : T₃ ≅ Lb ⋙ I') (c₄ : T₄ ≅ La ⋙ R₂) (c₄' : T₄' ≅ S₁ ⋙ Lb) (c₅ : T₅ ≅ I ⋙ Lb)
    (C : 𝒟B)
    (A₁ : c₁.hom.app C ≫ ci'bb.hom.app (La.obj C) =
      eqToHom (Functor.congr_obj hT₁ C) ≫ c₁'.hom.app C ≫ Li'.map (cbba.hom.app C))
    (CR₁ : c₁'.hom.app C ≫ Li'.map (eqToHom (Functor.congr_obj hP C)) =
      eqToHom (Functor.congr_obj hT₁₂ C) ≫ c₂'.hom.app C)
    (A₂ : c₂.hom.app C ≫ ci'a'.hom.app (Lb.obj C) =
      eqToHom (Functor.congr_obj hT₂ C) ≫ c₂'.hom.app C ≫ Li'.map (ca'b.hom.app C))
    (CL₁ : c₂.hom.app C ≫ eqToHom (Functor.congr_obj hQ (Lb.obj C)) =
      eqToHom (Functor.congr_obj hT₂₃ C) ≫ c₃.hom.app C)
    (U₁ : c₃.hom.app C ≫ e'.hom.app (Lb.obj C) = eqToHom (Functor.congr_obj hT₃ C))
    (CL₂ : c₁.hom.app C ≫ eqToHom (Functor.congr_obj hR (La.obj C)) =
      eqToHom (Functor.congr_obj hT₁₄ C) ≫ c₄.hom.app C)
    (A₃ : c₄.hom.app C ≫ cbi.hom.app (La.obj C) =
      eqToHom (Functor.congr_obj hT₄ C) ≫ c₄'.hom.app C ≫ Lb.map (cia.hom.app C))
    (CR₂ : c₄'.hom.app C ≫ Lb.map (eqToHom (Functor.congr_obj hS C)) =
      eqToHom (Functor.congr_obj hT₄₅ C) ≫ c₅.hom.app C)
    (U₂ : c₅.hom.app C ≫ Lb.map (e.hom.app C) = eqToHom (Functor.congr_obj hT₅ C)) :
    Li'.map ((cbba.app C).symm ≪≫ eqToIso (Functor.congr_obj hP C) ≪≫ ca'b.app C).hom ≫
      ((ci'a'.app (Lb.obj C)).symm ≪≫ eqToIso (Functor.congr_obj hQ (Lb.obj C)) ≪≫
        e'.app (Lb.obj C)).hom =
    (ci'bb.symm ≪≫ eqToIso hR ≪≫ cbi).hom.app (La.obj C) ≫
      Lb.map ((cia.app C).symm ≪≫ eqToIso (Functor.congr_obj hS C) ≪≫ e.app C).hom := by
  have A₂' := (eqToHom_comp_iff _ _ _).mp A₂.symm
  rw [← cancel_epi (c₁.hom.app C ≫ ci'bb.hom.app (La.obj C))]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom,
    Functor.map_comp, NatTrans.comp_app, eqToHom_app, Category.assoc]
  rw [reassoc_of% A₁, dncMapCancel, reassoc_of% CR₁, reassoc_of% A₂', Iso.hom_inv_id_app_assoc,
    reassoc_of% CL₁, U₁, Iso.hom_inv_id_app_assoc, reassoc_of% CL₂, reassoc_of% A₃, dncMapCancel,
    reassoc_of% CR₂, U₂]
  simp

/-- OK: instantiation + hypotheses elaborate and pass the kernel (goal left as sorry). -/
theorem repro_have_ok {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((leftDerivedUpperStarComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((leftDerivedUpperStarComp Λ a' b)).app C).hom ≫
      ((((leftDerivedUpperStarComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (leftDerivedUpperStarId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((leftDerivedUpperStarComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (leftDerivedUpperStarComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((leftDerivedUpperStarComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (leftDerivedUpperStarId Λ B).app C).hom  := by
  have h := dncSectionSquareCoherenceVars
      (La := (moduleObjectDerivedPullback Λ a))
      (La' := (moduleObjectDerivedPullback Λ a'))
      (Li := (moduleObjectDerivedPullback Λ i))
      (Li' := (moduleObjectDerivedPullback Λ i'))
      (Lbb := (moduleObjectDerivedPullback Λ bb))
      (Lb := (moduleObjectDerivedPullback Λ b))
      (P₁ := (moduleObjectDerivedPullback Λ (bb ≫ a)))
      (P₂ := (moduleObjectDerivedPullback Λ (a' ≫ b)))
      (Q₁ := (moduleObjectDerivedPullback Λ (i' ≫ a')))
      (I' := (moduleObjectDerivedPullback Λ (𝟙 B')))
      (R₁ := (moduleObjectDerivedPullback Λ (i' ≫ bb)))
      (R₂ := (moduleObjectDerivedPullback Λ (b ≫ i)))
      (S₁ := (moduleObjectDerivedPullback Λ (i ≫ a)))
      (I := (moduleObjectDerivedPullback Λ (𝟙 B)))
      (T₁ := (moduleObjectDerivedPullback Λ ((i' ≫ bb) ≫ a)))
      (T₁' := (moduleObjectDerivedPullback Λ (i' ≫ (bb ≫ a))))
      (T₂' := (moduleObjectDerivedPullback Λ (i' ≫ (a' ≫ b))))
      (T₂ := (moduleObjectDerivedPullback Λ ((i' ≫ a') ≫ b)))
      (T₃ := (moduleObjectDerivedPullback Λ (𝟙 B' ≫ b)))
      (T₄ := (moduleObjectDerivedPullback Λ ((b ≫ i) ≫ a)))
      (T₄' := (moduleObjectDerivedPullback Λ (b ≫ (i ≫ a))))
      (T₅ := (moduleObjectDerivedPullback Λ (b ≫ 𝟙 B)))
      (cbba := (leftDerivedUpperStarComp Λ bb a))
      (ca'b := (leftDerivedUpperStarComp Λ a' b))
      (ci'a' := (leftDerivedUpperStarComp Λ i' a'))
      (e' := (leftDerivedUpperStarId Λ B'))
      (ci'bb := (leftDerivedUpperStarComp Λ i' bb))
      (cbi := (leftDerivedUpperStarComp Λ b i))
      (cia := (leftDerivedUpperStarComp Λ i a))
      (e := (leftDerivedUpperStarId Λ B))
      (c₁ := (leftDerivedUpperStarComp Λ (i' ≫ bb) a))
      (c₁' := (leftDerivedUpperStarComp Λ i' (bb ≫ a)))
      (c₂' := (leftDerivedUpperStarComp Λ i' (a' ≫ b)))
      (c₂ := (leftDerivedUpperStarComp Λ (i' ≫ a') b))
      (c₃ := (leftDerivedUpperStarComp Λ (𝟙 B') b))
      (c₄ := (leftDerivedUpperStarComp Λ (b ≫ i) a))
      (c₄' := (leftDerivedUpperStarComp Λ b (i ≫ a)))
      (c₅ := (leftDerivedUpperStarComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (leftDerivedUpperStarComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (leftDerivedUpperStarComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (leftDerivedUpperStarComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (leftDerivedUpperStarComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (leftDerivedUpperStarComp_id_right_app Λ b C)
  sorry

/-
The two theorems below are the original failing reproducers. They are commented out so that
this file compiles as part of the library (CI imports every file under `WeilConjectures/`):
* `repro_exact_elab_timeout`: `exact h2` hits a deterministic elaboration timeout at `whnf`;
* `repro_congr_kernel_timeout`: elaboration passes, then a (kernel) deterministic timeout.
Uncomment them to reproduce. Diagnosis: `Report1.md`. Fix with the original statements:
`ReproducerFixed.lean` (`Report2.md`). Canonical-vocabulary fix:
`ReproducerTransparentFixed.lean` (`Report4.md`).

/-- FAILS: `exact h2` -> (deterministic) timeout at `whnf` (elaborator). -/
theorem repro_exact_elab_timeout {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((leftDerivedUpperStarComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((leftDerivedUpperStarComp Λ a' b)).app C).hom ≫
      ((((leftDerivedUpperStarComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (leftDerivedUpperStarId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((leftDerivedUpperStarComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (leftDerivedUpperStarComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((leftDerivedUpperStarComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (leftDerivedUpperStarId Λ B).app C).hom  := by
  have h := dncSectionSquareCoherenceVars
      (La := (moduleObjectDerivedPullback Λ a))
      (La' := (moduleObjectDerivedPullback Λ a'))
      (Li := (moduleObjectDerivedPullback Λ i))
      (Li' := (moduleObjectDerivedPullback Λ i'))
      (Lbb := (moduleObjectDerivedPullback Λ bb))
      (Lb := (moduleObjectDerivedPullback Λ b))
      (P₁ := (moduleObjectDerivedPullback Λ (bb ≫ a)))
      (P₂ := (moduleObjectDerivedPullback Λ (a' ≫ b)))
      (Q₁ := (moduleObjectDerivedPullback Λ (i' ≫ a')))
      (I' := (moduleObjectDerivedPullback Λ (𝟙 B')))
      (R₁ := (moduleObjectDerivedPullback Λ (i' ≫ bb)))
      (R₂ := (moduleObjectDerivedPullback Λ (b ≫ i)))
      (S₁ := (moduleObjectDerivedPullback Λ (i ≫ a)))
      (I := (moduleObjectDerivedPullback Λ (𝟙 B)))
      (T₁ := (moduleObjectDerivedPullback Λ ((i' ≫ bb) ≫ a)))
      (T₁' := (moduleObjectDerivedPullback Λ (i' ≫ (bb ≫ a))))
      (T₂' := (moduleObjectDerivedPullback Λ (i' ≫ (a' ≫ b))))
      (T₂ := (moduleObjectDerivedPullback Λ ((i' ≫ a') ≫ b)))
      (T₃ := (moduleObjectDerivedPullback Λ (𝟙 B' ≫ b)))
      (T₄ := (moduleObjectDerivedPullback Λ ((b ≫ i) ≫ a)))
      (T₄' := (moduleObjectDerivedPullback Λ (b ≫ (i ≫ a))))
      (T₅ := (moduleObjectDerivedPullback Λ (b ≫ 𝟙 B)))
      (cbba := (leftDerivedUpperStarComp Λ bb a))
      (ca'b := (leftDerivedUpperStarComp Λ a' b))
      (ci'a' := (leftDerivedUpperStarComp Λ i' a'))
      (e' := (leftDerivedUpperStarId Λ B'))
      (ci'bb := (leftDerivedUpperStarComp Λ i' bb))
      (cbi := (leftDerivedUpperStarComp Λ b i))
      (cia := (leftDerivedUpperStarComp Λ i a))
      (e := (leftDerivedUpperStarId Λ B))
      (c₁ := (leftDerivedUpperStarComp Λ (i' ≫ bb) a))
      (c₁' := (leftDerivedUpperStarComp Λ i' (bb ≫ a)))
      (c₂' := (leftDerivedUpperStarComp Λ i' (a' ≫ b)))
      (c₂ := (leftDerivedUpperStarComp Λ (i' ≫ a') b))
      (c₃ := (leftDerivedUpperStarComp Λ (𝟙 B') b))
      (c₄ := (leftDerivedUpperStarComp Λ (b ≫ i) a))
      (c₄' := (leftDerivedUpperStarComp Λ b (i ≫ a)))
      (c₅ := (leftDerivedUpperStarComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (leftDerivedUpperStarComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (leftDerivedUpperStarComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (leftDerivedUpperStarComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (leftDerivedUpperStarComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (leftDerivedUpperStarComp_id_right_app Λ b C)
  exact h2

/-- FAILS: elaborator passes, then (kernel) deterministic timeout. -/
theorem repro_congr_kernel_timeout {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((leftDerivedUpperStarComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((leftDerivedUpperStarComp Λ a' b)).app C).hom ≫
      ((((leftDerivedUpperStarComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (leftDerivedUpperStarId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((leftDerivedUpperStarComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (leftDerivedUpperStarComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((leftDerivedUpperStarComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (leftDerivedUpperStarId Λ B).app C).hom  := by
  have h := dncSectionSquareCoherenceVars
      (La := (moduleObjectDerivedPullback Λ a))
      (La' := (moduleObjectDerivedPullback Λ a'))
      (Li := (moduleObjectDerivedPullback Λ i))
      (Li' := (moduleObjectDerivedPullback Λ i'))
      (Lbb := (moduleObjectDerivedPullback Λ bb))
      (Lb := (moduleObjectDerivedPullback Λ b))
      (P₁ := (moduleObjectDerivedPullback Λ (bb ≫ a)))
      (P₂ := (moduleObjectDerivedPullback Λ (a' ≫ b)))
      (Q₁ := (moduleObjectDerivedPullback Λ (i' ≫ a')))
      (I' := (moduleObjectDerivedPullback Λ (𝟙 B')))
      (R₁ := (moduleObjectDerivedPullback Λ (i' ≫ bb)))
      (R₂ := (moduleObjectDerivedPullback Λ (b ≫ i)))
      (S₁ := (moduleObjectDerivedPullback Λ (i ≫ a)))
      (I := (moduleObjectDerivedPullback Λ (𝟙 B)))
      (T₁ := (moduleObjectDerivedPullback Λ ((i' ≫ bb) ≫ a)))
      (T₁' := (moduleObjectDerivedPullback Λ (i' ≫ (bb ≫ a))))
      (T₂' := (moduleObjectDerivedPullback Λ (i' ≫ (a' ≫ b))))
      (T₂ := (moduleObjectDerivedPullback Λ ((i' ≫ a') ≫ b)))
      (T₃ := (moduleObjectDerivedPullback Λ (𝟙 B' ≫ b)))
      (T₄ := (moduleObjectDerivedPullback Λ ((b ≫ i) ≫ a)))
      (T₄' := (moduleObjectDerivedPullback Λ (b ≫ (i ≫ a))))
      (T₅ := (moduleObjectDerivedPullback Λ (b ≫ 𝟙 B)))
      (cbba := (leftDerivedUpperStarComp Λ bb a))
      (ca'b := (leftDerivedUpperStarComp Λ a' b))
      (ci'a' := (leftDerivedUpperStarComp Λ i' a'))
      (e' := (leftDerivedUpperStarId Λ B'))
      (ci'bb := (leftDerivedUpperStarComp Λ i' bb))
      (cbi := (leftDerivedUpperStarComp Λ b i))
      (cia := (leftDerivedUpperStarComp Λ i a))
      (e := (leftDerivedUpperStarId Λ B))
      (c₁ := (leftDerivedUpperStarComp Λ (i' ≫ bb) a))
      (c₁' := (leftDerivedUpperStarComp Λ i' (bb ≫ a)))
      (c₂' := (leftDerivedUpperStarComp Λ i' (a' ≫ b)))
      (c₂ := (leftDerivedUpperStarComp Λ (i' ≫ a') b))
      (c₃ := (leftDerivedUpperStarComp Λ (𝟙 B') b))
      (c₄ := (leftDerivedUpperStarComp Λ (b ≫ i) a))
      (c₄' := (leftDerivedUpperStarComp Λ b (i ≫ a)))
      (c₅ := (leftDerivedUpperStarComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (leftDerivedUpperStarComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (leftDerivedUpperStarComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (leftDerivedUpperStarComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (leftDerivedUpperStarComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (leftDerivedUpperStarComp_id_right_app Λ b C)
  refine Eq.trans ?_ (Eq.trans h2 ?_)
  · congr 1
  · congr 1


-/

end AlgebraicGeometry.ProEtale.CondensedRing.Reproducer
