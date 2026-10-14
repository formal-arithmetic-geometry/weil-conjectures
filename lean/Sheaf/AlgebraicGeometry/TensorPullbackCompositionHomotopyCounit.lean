/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex

/-! # Localized homotopy counit pasting
Source: Stacks Project, Tags 0096, 0097 and 079W.
(blueprint: lem-sc-tensor-pullback-composition-homotopy-counit).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem homotopy_comp_counit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [Limits.HasBinaryBiproducts C] [Limits.HasBinaryBiproducts D]
    [Limits.HasBinaryBiproducts E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
    {L : C ⥤ E} {R : E ⥤ C}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [L.Additive] [R.Additive]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a : L ⊣ R)
    (c : L₁ ⋙ L₂ ≅ L) (e : R ⟶ R₂ ⋙ R₁)
    (h : ∀ V, c.hom.app (R.obj V) ≫ a.counit.app V =
      (L₁ ⋙ L₂).map (e.app V) ≫
        L₂.map (a₁.counit.app (R₂.obj V)) ≫ a₂.counit.app V)
    (K : HomotopyCategory E (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso c (.up ℤ)).hom.app
        ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      (a.mapHomotopyCategory (.up ℤ)).counit.app K =
    ((L₁ ⋙ L₂).mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e (.up ℤ)).app K) ≫
      (L₂.mapHomotopyCategory (.up ℤ)).map
        ((a₁.mapHomotopyCategory (.up ℤ)).counit.app
          ((R₂.mapHomotopyCategory (.up ℤ)).obj K)) ≫
      (a₂.mapHomotopyCategory (.up ℤ)).counit.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  let Q := HomotopyCategory.quotient E (.up ℤ)
  change Q.map ((Functor.mapHomologicalComplexCompIso c (.up ℤ)).hom.app
      ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) =
    Q.map (((L₁ ⋙ L₂).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex e (.up ℤ)).app P)) ≫
    Q.map ((L₂.mapHomologicalComplex (.up ℤ)).map
      ((a₁.mapHomologicalComplex (.up ℤ)).counit.app
        ((R₂.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      Q.map ((a₂.mapHomologicalComplex (.up ℤ)).counit.app P)
  erw [← Q.map_comp, ← Q.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f,
    Functor.comp_obj, Functor.id_obj]
  with_unfolding_all exact h (P.X n)

set_option backward.isDefEq.lazyWhnfCore false in
set_option maxHeartbeats 800000 in
-- Comparing the strict direct-image composite requires unfolding scheme module instances.
/-- The inverse mate of direct-image composition pastes the underived counits.
Source: Stacks Project, Tags 0096 and 0097, and the degreewise homotopy adjunction
of lem-weil-pbc-termwise-adjunction-homotopy.
Proof: Apply conjugateEquiv_counit_symm to a(fg), a(g).comp a(f), and the inverse
of pushforwardComp. Its components are identities on sections, so their images
under tensor pullback are identities. The formula comp_counit_app then gives
pullback of the g-counit followed by the f-counit. Choose a complex representing
K. Apply the module equation in each degree; the mapped composition isomorphism
and the counits of mapHomologicalComplex have these components. Extensionality
gives equality of complex maps. Apply the homotopy quotient, combine the images
using map_comp, and use mapHomotopyCategory_counit_app_quotient to obtain the
stated equation. Every K has a complex representative. Identity maps, zero
complexes and empty schemes obey the same adjunction identities; no flatness
or boundedness hypothesis is required. -/
private theorem tensorPullbackComposition_underived_homotopy_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [(Scheme.Modules.tensorPullback f).Additive]
    [(Scheme.Modules.tensorPullback g).Additive]
    [(Scheme.Modules.tensorPullback (f ≫ g)).Additive]
    (K : HomotopyCategory X.Modules (.up ℤ)) :
    let a {A B : Scheme.{u}} (s : A ⟶ B) :
        Scheme.Modules.tensorPullback s ⊣ Scheme.Modules.pushforward s :=
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
    let c : Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
        Scheme.Modules.tensorPullback (f ≫ g) :=
      (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
      (Scheme.Modules.pushforwardComp f g).symm
    (Functor.mapHomotopyCategoryCompIso c (.up ℤ)).hom.app
        (((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      ((a (f ≫ g)).mapHomotopyCategory (.up ℤ)).counit.app K =
    ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ)).map
        (((a g).mapHomotopyCategory (.up ℤ)).counit.app
          (((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj K)) ≫
      ((a f).mapHomotopyCategory (.up ℤ)).counit.app K := by
  classical
  intro a c
  have ho : ∀ V, c.hom.app ((Scheme.Modules.pushforward (f ≫ g)).obj V) ≫
      (a (f ≫ g)).counit.app V =
      (Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f).map
        ((Scheme.Modules.pushforwardComp f g).inv.app V) ≫
        (Scheme.Modules.tensorPullback f).map
          ((a g).counit.app ((Scheme.Modules.pushforward f).obj V)) ≫
        (a f).counit.app V := by
    intro V
    exact (conjugateEquiv_counit_symm (a (f ≫ g)) ((a g).comp (a f))
      (Scheme.Modules.pushforwardComp f g).inv V).symm
  have hc := homotopy_comp_counit (a g) (a f) (a (f ≫ g)) c
    (Scheme.Modules.pushforwardComp f g).inv ho K
  have hi : (NatTrans.mapHomotopyCategory
      (Scheme.Modules.pushforwardComp f g).inv (.up ℤ)).app K = 𝟙 _ := by
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ = 𝟙 _
    have ht : (NatTrans.mapHomologicalComplex
        (Scheme.Modules.pushforwardComp f g).inv (.up ℤ)).app K.as = 𝟙 _ := by
      ext n U
      simp
      rfl
    erw [ht]
    exact CategoryTheory.Functor.map_id _ _
  erw [hi, CategoryTheory.Functor.map_id, Category.id_comp] at hc
  exact hc


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem localized_paste
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (Q : C ⥤ C') (Q' : D ⥤ D') (P : C ⥤ D) (L : C' ⥤ D')
    (ε : Q ⋙ L ⟶ P ⋙ Q') {M A : C} {B T : D} {N : C'}
    (d : N ⟶ Q.obj M) (e : M ⟶ A) (c : P.obj M ⟶ B) (t : B ⟶ T)
    (b : P.obj A ⟶ T) (h : c ≫ t = P.map e ≫ b) :
    (L.map d ≫ ε.app M ≫ Q'.map c) ≫ Q'.map t =
      L.map (d ≫ Q.map e) ≫ ε.app A ≫ Q'.map b := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← Q'.map_comp, h, Q'.map_comp, ← Category.assoc (ε.app M)]
  have hn : ε.app M ≫ Q'.map (P.map e) = L.map (Q.map e) ≫ ε.app A :=
    (ε.naturality e).symm
  rw [hn]
  simp only [Category.assoc]

attribute [local irreducible] Scheme.Modules.tensorPullback derivedPullback

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.lazyWhnfCore false in
set_option maxHeartbeats 800000 in
-- The mapped adjunctions use both module-category presentations.
/-- Localizing the underived inverse-mate identity and applying naturality pastes counits.
Source: Stacks Project, Tags 0096, 0097 and 079W.
(blueprint: lem-sc-tensor-pullback-composition-homotopy-counit).
Proof: At every module apply conjugateEquiv_counit_symm to afg and ag.comp af
and pushforwardComp.inv. The inverse comparison is the identity on sections,
so its pullback is an identity. The composite adjunction counit is pullback
of the g-counit followed by the f-counit. Apply this degreewise on a complex
representing K and pass to the homotopy quotient. Apply Qh to the resulting
identity and use its preservation of composition. Naturality of epsilonF
at the g-counit moves its localized image into derivedPullback f. Its
functoriality combines that image with epsilon(g), giving the concrete apex
construction equation. The counits here are the already recorded choices.
No composite derived adjunction, derived unit or derived comparison is used.
Identities, zero complexes and empty schemes
satisfy the same equations; there is no cancellation or flatness assumption. -/
theorem tensorPullbackComposition_localized_homotopy_counit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    let epsilon {A B : Scheme.{u}} (s : A ⟶ B) :
        DerivedCategory.Qh ⋙ derivedPullback.{u, w} s ⟶
          (Scheme.Modules.tensorPullback s).mapHomotopyCategory (.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
      (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
    let a {A B : Scheme.{u}} (s : A ⟶ B) :
        Scheme.Modules.tensorPullback s ⊣ Scheme.Modules.pushforward s :=
      Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
    let b {A B : Scheme.{u}} (s : A ⟶ B) :
        (Scheme.Modules.tensorPullback s).mapHomotopyCategory (.up ℤ) ⊣
          (Scheme.Modules.pushforward s).mapHomotopyCategory (.up ℤ) :=
      (a s).mapHomotopyCategory (ComplexShape.up ℤ)
    let c : Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
        Scheme.Modules.tensorPullback (f ≫ g) :=
      (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
      (Scheme.Modules.pushforwardComp f g).symm
    let M := ((Scheme.Modules.pushforward (f ≫ g)).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj K
    ((derivedPullback f).map ((epsilon g).app M) ≫
      (epsilon f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((Functor.mapHomotopyCategoryCompIso c (ComplexShape.up ℤ)).hom.app M)) ≫
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
        ((b (f ≫ g)).counit.app K) = derivedCompositionCounitApex f g K := by
    classical
    have : ∀ {A B : Scheme.{u}} (s : A ⟶ B),
        (Scheme.Modules.tensorPullback s).Additive :=
      fun s ↦ (Classical.choose exists_derivedPullbackComposition.{u, w}) s
    intro ε a b c M
    let H := ((Scheme.Modules.pushforward f).mapHomotopyCategory (.up ℤ)).obj K
    have hc := tensorPullbackComposition_underived_homotopy_counit f g K
    have hp := localized_paste
      (C := HomotopyCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ))
      (D := HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ))
      (C' := schemeDerivedCategory Y) (D' := schemeDerivedCategory X)
      DerivedCategory.Qh DerivedCategory.Qh
      ((Scheme.Modules.tensorPullback f).mapHomotopyCategory (.up ℤ))
      (derivedPullback f) (ε f) ((ε g).app M)
      ((b g).counit.app H)
      ((Functor.mapHomotopyCategoryCompIso c (.up ℤ)).hom.app M)
      ((b (f ≫ g)).counit.app K) ((b f).counit.app K) hc
    have ha := derivedCompositionCounitApex_eq f g K
    exact hp.trans ha.symm

end AlgebraicGeometry
