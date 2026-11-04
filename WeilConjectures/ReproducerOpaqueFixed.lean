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
`moduleObjectDerivedPullbackComp`, `moduleObjectDerivedPullbackId` and transports along equalities
of morphisms agree. Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change).

## Fixed version of `Reproducer.lean` (opaque-wrapper fix)

In `Reproducer.lean`, `exact h2` timed out in elaboration and `congr 1` timed out in the kernel.
The cause was mixing two spellings of the same functor: the wrapper
`moduleObjectDerivedPullback Λ f`, and the bare `(upperStar Λ f).leftDerivedFunctor`
(`L((f)^*⟦Λ⟧)`) in which the upstream compositors `leftDerivedUpperStarComp`/`Id` are typed.
Lean then had to compare composite isomorphisms written in the two spellings underneath
`NatTrans.app`/`Functor.map`. Those are projections with `abbrev` hints, so instead of comparing
arguments Lean unfolded them deep into the derived-category machinery
(see `Report1.md`–`Report3.md`).

The fix: make the wrapper opaque and use one vocabulary only. Everything below is stated with the
wrapper and the wrapper-typed compositors `moduleObjectDerivedPullbackComp`/`Id`, and the original
proofs (`exact h2`, `congr 1`) go through unchanged. Compared with `Reproducer.lean`, the
statements of `dncPullbackComp_congr_left/right` and of the three `repro_*` theorems use
`moduleObjectDerivedPullbackComp/Id` in place of `leftDerivedUpperStarComp/Id`.

Here the opacity is simulated with `attribute [irreducible]`, because the wrapper is a local copy.
That is equivalent for this file: after the attribute nothing needs to unfold it.
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
namespace AlgebraicGeometry.ProEtale.CondensedRing.ReproducerOpaqueFixed

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-! ### Upstream part

Everything in this section belongs in
`WeilConjectures/AlgebraicGeometry/CondensedModuleDerivedPushpull.lean` and is only copied here.
Changes needed in that file:

1. Mark `moduleObjectDerivedPullback` as `@[no_expose]` (instead of the local
   `attribute [irreducible]` at the end of this section).
2. Add `moduleObjectDerivedPullback_eq`. It must be proved by a tactic (`delta …; rfl`), not by
   the term `rfl`: in a `module`, an exported `:= rfl` theorem is checked against the public view,
   where a `@[no_expose]` body cannot be unfolded.
3. Add `moduleObjectDerivedPullbackComp` and `moduleObjectDerivedPullbackId`, typed in the wrapper
   vocabulary. Both must themselves be `@[no_expose]`, since their bodies only typecheck by
   unfolding the wrapper.
4. Add `moduleObjectDerivedPullbackComp_assoc_app`, `…_id_left_app` and `…_id_right_app`, proved
   directly by the upstream `leftDerivedUpperStarComp_*_app` lemmas (cheap, because they are proved
   where the body is visible).
5. Do not add lemmas equating `(moduleObjectDerivedPullbackComp Λ f g).hom.app K` with
   `(leftDerivedUpperStarComp Λ f g).hom.app K`: once the wrapper is opaque their two sides have
   different types, so such a statement does not even typecheck in the public view. When a passage
   between the vocabularies is really needed, go through `moduleObjectDerivedPullback_eq` (`rw` /
   `eqToHom`).
6. Downstream files that `unfold`/`delta` `moduleObjectDerivedPullback`, or that combine it with
   `leftDerivedUpperStarComp`/`Id` (for example `ScalarPullbackSquareCoherence.lean`,
   `InternalScalarPullbackNormalizationData.lean`, `FreeParameterScalarMaps.lean`,
   `InternalCanonicalTensorPullRouteModel.lean`, `InternalPullNormalizationExistence.lean`), will
   no longer compile. They must switch to the `moduleObjectDerivedPullbackComp/Id` vocabulary or
   use `moduleObjectDerivedPullback_eq` explicitly. Not done here.

Once this is upstream, delete this whole section and import `CondensedModuleDerivedPushpull`.
-/

/-- The total left derived functor of `f^*` on module objects. Copy of upstream
`WeilConjectures/AlgebraicGeometry/CondensedModuleDerivedPushpull.lean`; upstream it should be
`@[no_expose]` (change 1). -/
def moduleObjectDerivedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (upperStar Λ f).leftDerivedFunctor

/-- The wrapper agrees with the bare derived pullback (change 2). -/
theorem moduleObjectDerivedPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    moduleObjectDerivedPullback Λ f = (upperStar Λ f).leftDerivedFunctor := by
  delta moduleObjectDerivedPullback; rfl

/-- The composition isomorphism, stated in the `moduleObjectDerivedPullback` vocabulary.
Upstream: `@[no_expose]` (change 3). -/
def moduleObjectDerivedPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleObjectDerivedPullback Λ (f ≫ g) ≅
      moduleObjectDerivedPullback Λ g ⋙ moduleObjectDerivedPullback Λ f :=
  leftDerivedUpperStarComp Λ f g

/-- The identity isomorphism, stated in the `moduleObjectDerivedPullback` vocabulary.
Upstream: `@[no_expose]` (change 3). -/
def moduleObjectDerivedPullbackId (X : Scheme.{u}) :
    moduleObjectDerivedPullback Λ (𝟙 X) ≅ 𝟭 _ :=
  leftDerivedUpperStarId Λ X

/-- Associativity of `moduleObjectDerivedPullbackComp` (change 4). -/
theorem moduleObjectDerivedPullbackComp_assoc_app {W X Y Z : Scheme.{u}} (f : W ⟶ X)
    (g : X ⟶ Y) (h : Y ⟶ Z)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (moduleObjectDerivedPullbackComp Λ (f ≫ g) h).hom.app K ≫
        (moduleObjectDerivedPullbackComp Λ f g).hom.app
          ((moduleObjectDerivedPullback Λ h).obj K) =
      eqToHom (by rw [Category.assoc]) ≫
        (moduleObjectDerivedPullbackComp Λ f (g ≫ h)).hom.app K ≫
          (moduleObjectDerivedPullback Λ f).map
            ((moduleObjectDerivedPullbackComp Λ g h).hom.app K) :=
  leftDerivedUpperStarComp_assoc_app Λ f g h K

/-- Left unit law for `moduleObjectDerivedPullbackComp` (change 4). -/
theorem moduleObjectDerivedPullbackComp_id_left_app {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (moduleObjectDerivedPullbackComp Λ (𝟙 X) g).hom.app K ≫
        (moduleObjectDerivedPullbackId Λ X).hom.app ((moduleObjectDerivedPullback Λ g).obj K) =
      eqToHom (by rw [Category.id_comp]; rfl) :=
  leftDerivedUpperStarComp_id_left_app Λ g K

/-- Right unit law for `moduleObjectDerivedPullbackComp` (change 4). -/
theorem moduleObjectDerivedPullbackComp_id_right_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    (moduleObjectDerivedPullbackComp Λ f (𝟙 Y)).hom.app K ≫
        (moduleObjectDerivedPullback Λ f).map ((moduleObjectDerivedPullbackId Λ Y).hom.app K) =
      eqToHom (by rw [Category.comp_id]; rfl) :=
  leftDerivedUpperStarComp_id_right_app Λ f K

-- Local stand-in for upstream `@[no_expose]` (change 1): from here on the wrapper is opaque.
attribute [irreducible] moduleObjectDerivedPullback

/-! ### Coherence (consumer part, wrapper vocabulary only) -/

/-- Transport in the first variable of the compositor.
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncPullbackComp_congr_left {X Y Z : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (g : Y ⟶ Z)
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (moduleObjectDerivedPullbackComp Λ f g).hom.app C ≫
        eqToHom (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj
          ((moduleObjectDerivedPullback Λ g).obj C)) h) =
      eqToHom (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ (f ≫ g)).obj C) h) ≫
        (moduleObjectDerivedPullbackComp Λ f' g).hom.app C := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- Transport in the second variable of the compositor.
Source: sk-thm-dnc, proof step 12 (blueprint: dnc-over-kappa-base-change). -/
theorem dncPullbackComp_congr_right {X Y Z : Scheme.{u}} (f : X ⟶ Y) {g g' : Y ⟶ Z} (h : g = g')
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z))) :
    (moduleObjectDerivedPullbackComp Λ f g).hom.app C ≫
        (moduleObjectDerivedPullback Λ f).map
          (eqToHom (congrArg (fun g ↦ (moduleObjectDerivedPullback Λ g).obj C) h)) =
      eqToHom (congrArg (fun g ↦ (moduleObjectDerivedPullback Λ (f ≫ g)).obj C) h) ≫
        (moduleObjectDerivedPullbackComp Λ f g').hom.app C := by
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

/-- Control: the instantiation and hypotheses elaborate and pass the kernel (goal left as `sorry`,
as in `Reproducer.lean`). -/
theorem repro_have_ok {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((moduleObjectDerivedPullbackComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((moduleObjectDerivedPullbackComp Λ a' b)).app C).hom ≫
      ((((moduleObjectDerivedPullbackComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (moduleObjectDerivedPullbackId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((moduleObjectDerivedPullbackComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (moduleObjectDerivedPullbackComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((moduleObjectDerivedPullbackComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (moduleObjectDerivedPullbackId Λ B).app C).hom  := by
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
      (cbba := (moduleObjectDerivedPullbackComp Λ bb a))
      (ca'b := (moduleObjectDerivedPullbackComp Λ a' b))
      (ci'a' := (moduleObjectDerivedPullbackComp Λ i' a'))
      (e' := (moduleObjectDerivedPullbackId Λ B'))
      (ci'bb := (moduleObjectDerivedPullbackComp Λ i' bb))
      (cbi := (moduleObjectDerivedPullbackComp Λ b i))
      (cia := (moduleObjectDerivedPullbackComp Λ i a))
      (e := (moduleObjectDerivedPullbackId Λ B))
      (c₁ := (moduleObjectDerivedPullbackComp Λ (i' ≫ bb) a))
      (c₁' := (moduleObjectDerivedPullbackComp Λ i' (bb ≫ a)))
      (c₂' := (moduleObjectDerivedPullbackComp Λ i' (a' ≫ b)))
      (c₂ := (moduleObjectDerivedPullbackComp Λ (i' ≫ a') b))
      (c₃ := (moduleObjectDerivedPullbackComp Λ (𝟙 B') b))
      (c₄ := (moduleObjectDerivedPullbackComp Λ (b ≫ i) a))
      (c₄' := (moduleObjectDerivedPullbackComp Λ b (i ≫ a)))
      (c₅ := (moduleObjectDerivedPullbackComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (moduleObjectDerivedPullbackComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (moduleObjectDerivedPullbackComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (moduleObjectDerivedPullbackComp_id_right_app Λ b C)
  sorry

/-- Formerly an elaboration timeout at `exact h2`; fine in the single wrapper vocabulary. -/
theorem repro_exact_elab_timeout {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((moduleObjectDerivedPullbackComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((moduleObjectDerivedPullbackComp Λ a' b)).app C).hom ≫
      ((((moduleObjectDerivedPullbackComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (moduleObjectDerivedPullbackId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((moduleObjectDerivedPullbackComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (moduleObjectDerivedPullbackComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((moduleObjectDerivedPullbackComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (moduleObjectDerivedPullbackId Λ B).app C).hom  := by
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
      (cbba := (moduleObjectDerivedPullbackComp Λ bb a))
      (ca'b := (moduleObjectDerivedPullbackComp Λ a' b))
      (ci'a' := (moduleObjectDerivedPullbackComp Λ i' a'))
      (e' := (moduleObjectDerivedPullbackId Λ B'))
      (ci'bb := (moduleObjectDerivedPullbackComp Λ i' bb))
      (cbi := (moduleObjectDerivedPullbackComp Λ b i))
      (cia := (moduleObjectDerivedPullbackComp Λ i a))
      (e := (moduleObjectDerivedPullbackId Λ B))
      (c₁ := (moduleObjectDerivedPullbackComp Λ (i' ≫ bb) a))
      (c₁' := (moduleObjectDerivedPullbackComp Λ i' (bb ≫ a)))
      (c₂' := (moduleObjectDerivedPullbackComp Λ i' (a' ≫ b)))
      (c₂ := (moduleObjectDerivedPullbackComp Λ (i' ≫ a') b))
      (c₃ := (moduleObjectDerivedPullbackComp Λ (𝟙 B') b))
      (c₄ := (moduleObjectDerivedPullbackComp Λ (b ≫ i) a))
      (c₄' := (moduleObjectDerivedPullbackComp Λ b (i ≫ a)))
      (c₅ := (moduleObjectDerivedPullbackComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (moduleObjectDerivedPullbackComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (moduleObjectDerivedPullbackComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (moduleObjectDerivedPullbackComp_id_right_app Λ b C)
  exact h2

/-- Formerly a kernel timeout after `congr 1`; fine in the single wrapper vocabulary. -/
theorem repro_congr_kernel_timeout {A B A' B' : Scheme.{u}} (a : A ⟶ B) (a' : A' ⟶ B')
    (i : B ⟶ A) (i' : B' ⟶ A') (bb : A' ⟶ A) (b : B' ⟶ B) (h₁ : i ≫ a = 𝟙 B)
    (h₁' : i' ≫ a' = 𝟙 B') (h₂ : bb ≫ a = a' ≫ b) (h₃ : i' ≫ bb = b ≫ i) (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1}) (condensedRingObj Λ B))) :
    (moduleObjectDerivedPullback Λ i').map
        ((((moduleObjectDerivedPullbackComp Λ bb a)).app C).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₂) ≪≫ ((moduleObjectDerivedPullbackComp Λ a' b)).app C).hom ≫
      ((((moduleObjectDerivedPullbackComp Λ i' a')).app ((moduleObjectDerivedPullback Λ b).obj C)).symm ≪≫
          eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj ((moduleObjectDerivedPullback Λ b).obj C)) h₁') ≪≫
          (moduleObjectDerivedPullbackId Λ B').app ((moduleObjectDerivedPullback Λ b).obj C)).hom =
    ((moduleObjectDerivedPullbackComp Λ i' bb).symm ≪≫ eqToIso (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) ≪≫
          (moduleObjectDerivedPullbackComp Λ b i)).hom.app ((moduleObjectDerivedPullback Λ a).obj C) ≫
      (moduleObjectDerivedPullback Λ b).map
        ((((moduleObjectDerivedPullbackComp Λ i a)).app C).symm ≪≫ eqToIso (congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj C) h₁) ≪≫
          (moduleObjectDerivedPullbackId Λ B).app C).hom  := by
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
      (cbba := (moduleObjectDerivedPullbackComp Λ bb a))
      (ca'b := (moduleObjectDerivedPullbackComp Λ a' b))
      (ci'a' := (moduleObjectDerivedPullbackComp Λ i' a'))
      (e' := (moduleObjectDerivedPullbackId Λ B'))
      (ci'bb := (moduleObjectDerivedPullbackComp Λ i' bb))
      (cbi := (moduleObjectDerivedPullbackComp Λ b i))
      (cia := (moduleObjectDerivedPullbackComp Λ i a))
      (e := (moduleObjectDerivedPullbackId Λ B))
      (c₁ := (moduleObjectDerivedPullbackComp Λ (i' ≫ bb) a))
      (c₁' := (moduleObjectDerivedPullbackComp Λ i' (bb ≫ a)))
      (c₂' := (moduleObjectDerivedPullbackComp Λ i' (a' ≫ b)))
      (c₂ := (moduleObjectDerivedPullbackComp Λ (i' ≫ a') b))
      (c₃ := (moduleObjectDerivedPullbackComp Λ (𝟙 B') b))
      (c₄ := (moduleObjectDerivedPullbackComp Λ (b ≫ i) a))
      (c₄' := (moduleObjectDerivedPullbackComp Λ b (i ≫ a)))
      (c₅ := (moduleObjectDerivedPullbackComp Λ b (𝟙 B)))
      (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' bb a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (i' ≫ g)) h₂) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc i' a' b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ b)) h₁') (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.id_comp b)) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ (f ≫ a)) h₃) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.assoc b i a)) (congrArg (fun g ↦ moduleObjectDerivedPullback Λ (b ≫ g)) h₁) (congrArg (fun f ↦ moduleObjectDerivedPullback Λ f) (Category.comp_id b))
      C
  have h2 := h (moduleObjectDerivedPullbackComp_assoc_app Λ i' bb a C)
    (dncPullbackComp_congr_right Λ i' h₂ C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ i' a' b C)
    (dncPullbackComp_congr_left Λ h₁' b C)
    (moduleObjectDerivedPullbackComp_id_left_app Λ b C)
    (dncPullbackComp_congr_left Λ h₃ a C)
    (moduleObjectDerivedPullbackComp_assoc_app Λ b i a C)
    (dncPullbackComp_congr_right Λ b h₁ C)
    (moduleObjectDerivedPullbackComp_id_right_app Λ b C)
  refine Eq.trans ?_ (Eq.trans h2 ?_)
  · congr 1
  · congr 1


end AlgebraicGeometry.ProEtale.CondensedRing.ReproducerOpaqueFixed
