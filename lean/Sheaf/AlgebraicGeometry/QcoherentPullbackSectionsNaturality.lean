/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.QcoherentPullbackSections
import all WeilConjectures.AlgebraicGeometry.EtaleTensorSections

/-! # Restriction compatibility of structural tensor-section pullback

Source: Stacks Project, Tags 03DR, 0095 and 0096.
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
attribute [local irreducible] tensorPullback tensorPullbackObj
  tensorSectionsComp tensorSectionsUnit etaleTensorSectionsRestriction
  compOfAdjunction sectionsUnitOfAdjunction restrictionOfAdjunction
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private def tensorRestriction {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    (c : A ⟶ C) (h : a ≫ b = c) (F : C.Modules) :
    Γ((tensorPullback b).obj F, ⊤) ⟶ Γ((tensorPullback c).obj F, ⊤) :=
  restrictionOfAdjunction (@tensorPullback)
    (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b c h F

attribute [local irreducible] tensorRestriction

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem unit_to_abstract {A B : Scheme.{u}} (a : A ⟶ B) (F : B.Modules) :
    tensorSectionsUnit a F = sectionsUnitOfAdjunction a (tensorPullback a)
      (Classical.choose (exists_tensorPullbackAdjunction a)) F := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      unfold tensorSectionsUnit sectionsUnitOfAdjunction
      rfl

private theorem comp_to_abstract {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) :
    tensorSectionsComp a b = compOfAdjunction (@tensorPullback)
      (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b := by
  unfold tensorSectionsComp compOfAdjunction
  rfl

private theorem tensorRestriction_comp
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : B ⟶ D) (e : A ⟶ D) (p : b ≫ c = d) (q : a ≫ d = e)
    (r : (a ≫ b) ≫ c = e) (F : D.Modules) :
    tensorRestriction (a ≫ b) c e r F =
      tensorRestriction b c d p F ≫ tensorRestriction a d e q F := by
  unfold tensorRestriction
  exact restrictionOfAdjunction_comp (@tensorPullback)
    (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
    a b c d e p q r F

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionOfAdjunction_comp_inv
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (F : D.Modules) :
    restrictionOfAdjunction L adj a (b ≫ c) ((a ≫ b) ≫ c) (Category.assoc a b c).symm F ≫
        ((compOfAdjunction L adj (a ≫ b) c).inv.app F).app ⊤ =
      ((compOfAdjunction L adj b c).inv.app F).app ⊤ ≫
        restrictionOfAdjunction L adj a b (a ≫ b) rfl ((L c).obj F) := by
  apply (cancel_epi (((compOfAdjunction L adj b c).hom.app F).app ⊤)).mp
  apply (cancel_mono (((compOfAdjunction L adj (a ≫ b) c).hom.app F).app ⊤)).mp
  simp only [Category.assoc, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app,
    Category.comp_id]
  simp only [← Category.assoc, ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app,
    Category.id_comp]
  unfold restrictionOfAdjunction
  change _ ≫ (sectionsUnitOfAdjunction a (L a) (adj a) ((L (b ≫ c)).obj F) ≫
      ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) =
    sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj ((L c).obj F)) ≫
      ((compOfAdjunction L adj a b).hom.app ((L c).obj F)).app ⊤ ≫
      ((compOfAdjunction L adj (a ≫ b) c).hom.app F).app ⊤
  have hn := sectionsUnit_naturality a (L a) (adj a)
    ((compOfAdjunction L adj b c).hom.app F)
  have ha := congrArg (fun f ↦ f.app ⊤)
    (compOfAdjunction_assoc L adj a b c F)
  simp only [Hom.comp_app] at ha
  calc
    _ = (_ ≫ sectionsUnitOfAdjunction a (L a) (adj a) ((L (b ≫ c)).obj F)) ≫
        ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤ :=
      (Category.assoc _ _ _).symm
    _ = (sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj ((L c).obj F)) ≫
        ((L a).map ((compOfAdjunction L adj b c).hom.app F)).app ⊤) ≫
        ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤ :=
      congrArg (fun t ↦ t ≫ ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) hn
    _ = sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj ((L c).obj F)) ≫
        (((L a).map ((compOfAdjunction L adj b c).hom.app F)).app ⊤ ≫
          ((compOfAdjunction L adj a (b ≫ c)).hom.app F).app ⊤) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun t ↦ sectionsUnitOfAdjunction a (L a) (adj a)
      ((L b).obj ((L c).obj F)) ≫ t) ha.symm

private theorem tensorRestriction_comp_inv
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (F : D.Modules) :
    tensorRestriction a (b ≫ c) ((a ≫ b) ≫ c) (Category.assoc a b c).symm F ≫
        ((tensorSectionsComp (a ≫ b) c).inv.app F).app ⊤ =
      ((tensorSectionsComp b c).inv.app F).app ⊤ ≫
        tensorRestriction a b (a ≫ b) rfl ((tensorPullback c).obj F) := by
  unfold tensorRestriction
  simp only [comp_to_abstract]
  exact restrictionOfAdjunction_comp_inv (@tensorPullback)
    (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b c F

private theorem restrictionOfAdjunction_naturality
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) {F G : C.Modules} (φ : F ⟶ G) :
    restrictionOfAdjunction L adj a b c h F ≫ ((L c).map φ).app ⊤ =
      ((L b).map φ).app ⊤ ≫ restrictionOfAdjunction L adj a b c h G := by
  subst c
  unfold restrictionOfAdjunction
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  have hc := congrArg (fun ψ ↦ ψ.app ⊤) ((compOfAdjunction L adj a b).hom.naturality φ)
  change (((L a).map ((L b).map φ)).app ⊤ ≫
    ((compOfAdjunction L adj a b).hom.app G).app ⊤) =
      ((compOfAdjunction L adj a b).hom.app F).app ⊤ ≫
        ((L (a ≫ b)).map φ).app ⊤ at hc
  rw [Category.assoc, ← hc, ← Category.assoc,
    ← sectionsUnit_naturality a (L a) (adj a), Category.assoc]

private theorem tensorRestriction_naturality {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C) (h : a ≫ b = c)
    {F G : C.Modules} (φ : F ⟶ G) :
    tensorRestriction a b c h F ≫ ((tensorPullback c).map φ).app ⊤ =
      ((tensorPullback b).map φ).app ⊤ ≫ tensorRestriction a b c h G := by
  unfold tensorRestriction
  exact restrictionOfAdjunction_naturality (@tensorPullback)
    (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f)) a b c h φ

private theorem tensorRestriction_comp_inv_eq
    {A B C D : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (d : A ⟶ C)
    (h : a ≫ b = d) (c : C ⟶ D) (F : D.Modules) :
    tensorRestriction a (b ≫ c) (d ≫ c)
        ((Category.assoc a b c).symm.trans (congrArg (fun f ↦ f ≫ c) h)) F ≫
        ((tensorSectionsComp d c).inv.app F).app ⊤ =
      ((tensorSectionsComp b c).inv.app F).app ⊤ ≫
        tensorRestriction a b d h ((tensorPullback c).obj F) := by
  subst d
  exact tensorRestriction_comp_inv a b c F

private theorem tensorRestriction_congr {A B C : Scheme.{u}}
    {a a' : A ⟶ B} (b : B ⟶ C) (c : A ⟶ C) (h : a = a')
    (h₁ : a ≫ b = c) (h₂ : a' ≫ b = c) (F : C.Modules) :
    tensorRestriction a b c h₁ F = tensorRestriction a' b c h₂ F := by
  subst a'
  rfl

private theorem qcoherentPullbackSection_eq {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    qcoherentPullbackSection g F G ψ U V p h =
      tensorRestriction p U.hom (V.hom ≫ g) h F ≫
        ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
        ((tensorPullback V.hom).map ψ).app ⊤ := by
  unfold qcoherentPullbackSection
  rw [sectionMapCopy_eq]
  unfold tensorRestriction restrictionOfAdjunction
  rw [← unit_to_abstract, ← comp_to_abstract]
  change tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
      ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
      ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
      ((tensorPullback V.hom).map ψ).app ⊤ =
    (tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
      ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
      (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤) ≫
      ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
      ((tensorPullback V.hom).map ψ).app ⊤
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etaleTensorSectionsRestriction_eq {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    etaleTensorSectionsRestriction F a = tensorRestriction a.left U.hom V.hom a.w F := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      unfold etaleTensorSectionsRestriction tensorRestriction restrictionOfAdjunction
      rw [← unit_to_abstract, ← comp_to_abstract]
      rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] qcoherentPullbackSection

/-- Structural pullback commutes with restrictions in a commuting diagram of squares.
Source: Stacks Project, Tag 03DR, functoriality of associated quasi-coherent sections.
(blueprint: lem-weil-pbc-qcoherent-pullback-section-square-naturality)

Proof: Write each structural map as the pullback unit followed by the comparison
of composite tensor pullbacks. The left-adjoint composition isomorphisms are mates
of the pushforward composition isomorphisms, so their associativity follows from
adjunction coherence. Thus the two successive restriction maps compose to the
restriction for the composite scheme map. Commute the inverse composition
comparison across restriction using this associativity equation, and commute the
coefficient morphism using unit naturality. The two resulting composites agree
because the diagram of schemes commutes. No flatness or acyclicity is used. -/
theorem qcoherentPullbackSection_square_naturality {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    {U₁ U₂ : X.Etale} {V₁ V₂ : Y.Etale}
    (p₁ : V₁.left ⟶ U₁.left) (p₂ : V₂.left ⟶ U₂.left)
    (h₁ : p₁ ≫ U₁.hom = V₁.hom ≫ g) (h₂ : p₂ ≫ U₂.hom = V₂.hom ≫ g)
    (a : U₂ ⟶ U₁) (b : V₂ ⟶ V₁) (h : b.left ≫ p₁ = p₂ ≫ a.left) :
    etaleTensorSectionsRestriction F a ≫ qcoherentPullbackSection g F G ψ U₂ V₂ p₂ h₂ =
      qcoherentPullbackSection g F G ψ U₁ V₁ p₁ h₁ ≫
        etaleTensorSectionsRestriction G b := by
  let t := ((Category.assoc b.left V₁.hom g).symm.trans
    (congrArg (fun f ↦ f ≫ g) (MorphismProperty.Over.w b)))
  have htop : tensorRestriction a.left U₁.hom U₂.hom (MorphismProperty.Over.w a) F ≫
      tensorRestriction p₂ U₂.hom (V₂.hom ≫ g) h₂ F =
      tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫
        tensorRestriction b.left (V₁.hom ≫ g) (V₂.hom ≫ g) t F := by
    have rtop : (p₂ ≫ a.left) ≫ U₁.hom = V₂.hom ≫ g :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun f ↦ p₂ ≫ f) (MorphismProperty.Over.w a)).trans h₂)
    have rbot : (b.left ≫ p₁) ≫ U₁.hom = V₂.hom ≫ g :=
      (Category.assoc _ _ _).trans ((congrArg (fun f ↦ b.left ≫ f) h₁).trans t)
    exact (tensorRestriction_comp p₂ a.left U₁.hom U₂.hom (V₂.hom ≫ g)
      (MorphismProperty.Over.w a) h₂ rtop F).symm.trans
      ((tensorRestriction_congr U₁.hom (V₂.hom ≫ g) h.symm rtop rbot F).trans
        (tensorRestriction_comp b.left p₁ U₁.hom (V₁.hom ≫ g) (V₂.hom ≫ g)
          h₁ t rbot F))
  have hcomp := tensorRestriction_comp_inv_eq b.left V₁.hom V₂.hom
    (MorphismProperty.Over.w b) g F
  have hcoeff := tensorRestriction_naturality b.left V₁.hom V₂.hom
    (MorphismProperty.Over.w b) ψ
  rw [etaleTensorSectionsRestriction_eq, etaleTensorSectionsRestriction_eq,
    qcoherentPullbackSection_eq, qcoherentPullbackSection_eq]
  calc
    _ = (tensorRestriction a.left U₁.hom U₂.hom (MorphismProperty.Over.w a) F ≫
        tensorRestriction p₂ U₂.hom (V₂.hom ≫ g) h₂ F) ≫
        (((tensorSectionsComp V₂.hom g).inv.app F).app ⊤ ≫
          ((tensorPullback V₂.hom).map ψ).app ⊤) := (Category.assoc _ _ _).symm
    _ = tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫
        tensorRestriction b.left (V₁.hom ≫ g) (V₂.hom ≫ g) t F ≫
        ((tensorSectionsComp V₂.hom g).inv.app F).app ⊤ ≫
        ((tensorPullback V₂.hom).map ψ).app ⊤ := by
      exact (congrArg (fun f ↦ f ≫ (((tensorSectionsComp V₂.hom g).inv.app F).app ⊤ ≫
        ((tensorPullback V₂.hom).map ψ).app ⊤)) htop).trans (Category.assoc _ _ _)
    _ = tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫
        ((tensorSectionsComp V₁.hom g).inv.app F).app ⊤ ≫
        tensorRestriction b.left V₁.hom V₂.hom (MorphismProperty.Over.w b)
          ((tensorPullback g).obj F) ≫
        ((tensorPullback V₂.hom).map ψ).app ⊤ := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫ f ≫
          ((tensorPullback V₂.hom).map ψ).app ⊤) hcomp
    _ = tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫
        ((tensorSectionsComp V₁.hom g).inv.app F).app ⊤ ≫
        ((tensorPullback V₁.hom).map ψ).app ⊤ ≫
        tensorRestriction b.left V₁.hom V₂.hom (MorphismProperty.Over.w b) G := by
      exact congrArg (fun f ↦ tensorRestriction p₁ U₁.hom (V₁.hom ≫ g) h₁ F ≫
        ((tensorSectionsComp V₁.hom g).inv.app F).app ⊤ ≫ f) hcoeff
    _ = _ := by simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem sectionsUnit_restriction
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) (F : C.Modules) :
    sectionsUnitOfAdjunction b (L b) (adj b) F ≫
        restrictionOfAdjunction L adj a b c h F =
      sectionsUnitOfAdjunction c (L c) (adj c) F := by
  subst c
  unfold restrictionOfAdjunction
  simp only [eqToHom_refl, Hom.id_app, Category.comp_id]
  exact sectionsUnit_comp L adj a b F

private theorem sectionsUnit_comp_inv
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (F : C.Modules) :
    sectionsUnitOfAdjunction (a ≫ b) (L (a ≫ b)) (adj (a ≫ b)) F ≫
        ((compOfAdjunction L adj a b).inv.app F).app ⊤ =
      sectionsUnitOfAdjunction b (L b) (adj b) F ≫
        sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) := by
  rw [← sectionsUnit_comp L adj a b F]
  simp only [Category.assoc, ← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app]
  change sectionsUnitOfAdjunction b (L b) (adj b) F ≫
      (sectionsUnitOfAdjunction a (L a) (adj a) ((L b).obj F) ≫
        (𝟙 _ : Γ((L a).obj ((L b).obj F), ⊤) ⟶ _)) = _
  rw [Category.comp_id]

private theorem sectionsUnit_square
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {X Y A B : Scheme.{u}} (g : Y ⟶ X) (a : A ⟶ X) (b : B ⟶ Y)
    (p : B ⟶ A) (h : p ≫ a = b ≫ g)
    (F : X.Modules) (G : Y.Modules) (ψ : (L g).obj F ⟶ G) :
    sectionsUnitOfAdjunction a (L a) (adj a) F ≫
      (restrictionOfAdjunction L adj p a (b ≫ g) h F ≫
        ((compOfAdjunction L adj b g).inv.app F).app ⊤ ≫ ((L b).map ψ).app ⊤) =
      sectionsUnitOfAdjunction g (L g) (adj g) F ≫ ψ.app ⊤ ≫
        sectionsUnitOfAdjunction b (L b) (adj b) G := by
  rw [← Category.assoc, sectionsUnit_restriction L adj p a (b ≫ g) h F,
    ← Category.assoc, sectionsUnit_comp_inv L adj b g F]
  rw [Category.assoc, ← sectionsUnit_naturality b (L b) (adj b) ψ]

/-- Structural pullback commutes with the global-section unit.
Source: Stacks Project, Tags 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-section-square-naturality)

Proof: Combine the source unit with the structural restriction using the
unit equation of the adjunction composition comparison. The square equation
identifies this with the unit for V followed by g. Cancel its composition
comparison with its inverse and apply unit naturality to the coefficient map.
This argument applies to arbitrary modules and empty schemes. -/
theorem qcoherentPullbackSection_global_unit {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    tensorSectionsUnit U.hom F ≫ qcoherentPullbackSection g F G ψ U V p h =
      tensorSectionsUnit g F ≫ ψ.app ⊤ ≫ tensorSectionsUnit V.hom G := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      rw [qcoherentPullbackSection_eq]
      simp only [tensorRestriction, unit_to_abstract, comp_to_abstract]
      exact sectionsUnit_square (@tensorPullback)
        (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
        g U.hom V.hom p h F G ψ

/-- Pullback of global sections commutes with etale restriction.
Source: Stacks Project, Tag 03DR.
(blueprint: lem-weil-pbc-qcoherent-pullback-section-square-naturality)

Proof: The unit equation of the adjunction composition comparison combines
the two successive units. Transport through the triangle equation of the
etale morphism leaves the unit at its source. Empty schemes are included. -/
theorem tensorSectionsUnit_restriction {X : Scheme.{u}} (F : X.Modules)
    {U V : X.Etale} (a : V ⟶ U) :
    tensorSectionsUnit U.hom F ≫ etaleTensorSectionsRestriction F a =
      tensorSectionsUnit V.hom F := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      rw [etaleTensorSectionsRestriction_eq]
      simp only [unit_to_abstract]
      unfold tensorRestriction
      exact sectionsUnit_restriction (@tensorPullback)
        (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
        a.left U.hom V.hom (MorphismProperty.Over.w a) F

private theorem square_coefficient_naturality
    (L : ∀ {A B : Scheme.{u}}, (A ⟶ B) → B.Modules ⥤ A.Modules)
    (adj : ∀ {A B : Scheme.{u}} (f : A ⟶ B), L f ⊣ pushforward f)
    {X Y A B : Scheme.{u}} (g : Y ⟶ X) (a : A ⟶ X) (b : B ⟶ Y)
    (p : B ⟶ A) (h : p ≫ a = b ≫ g)
    {F F' : X.Modules} {G G' : Y.Modules}
    (ψ : (L g).obj F ⟶ G) (ψ' : (L g).obj F' ⟶ G')
    (f : F ⟶ F') (k : G ⟶ G') (hab : (L g).map f ≫ ψ' = ψ ≫ k) :
    ((L a).map f).app ⊤ ≫
        (restrictionOfAdjunction L adj p a (b ≫ g) h F' ≫
          ((compOfAdjunction L adj b g).inv.app F').app ⊤ ≫ ((L b).map ψ').app ⊤) =
      (restrictionOfAdjunction L adj p a (b ≫ g) h F ≫
        ((compOfAdjunction L adj b g).inv.app F).app ⊤ ≫ ((L b).map ψ).app ⊤) ≫
          ((L b).map k).app ⊤ := by
  have hr := restrictionOfAdjunction_naturality L adj p a (b ≫ g) h f
  have hc := congrArg (fun t ↦ t.app ⊤) ((compOfAdjunction L adj b g).inv.naturality f)
  change ((L (b ≫ g)).map f).app ⊤ ≫
      ((compOfAdjunction L adj b g).inv.app F').app ⊤ =
    ((compOfAdjunction L adj b g).inv.app F).app ⊤ ≫
      ((L b).map ((L g).map f)).app ⊤ at hc
  have ht := congrArg (fun t ↦ ((L b).map t).app ⊤) hab
  simp only [(L b).map_comp, Hom.comp_app] at ht
  calc
    _ = restrictionOfAdjunction L adj p a (b ≫ g) h F ≫
        ((L (b ≫ g)).map f).app ⊤ ≫
        ((compOfAdjunction L adj b g).inv.app F').app ⊤ ≫
        ((L b).map ψ').app ⊤ := by
      rw [← Category.assoc, ← hr]
      simp only [Category.assoc]
    _ = restrictionOfAdjunction L adj p a (b ≫ g) h F ≫
        ((compOfAdjunction L adj b g).inv.app F).app ⊤ ≫
        ((L b).map ((L g).map f)).app ⊤ ≫ ((L b).map ψ').app ⊤ := by
      rw [← Category.assoc _ _ (((L b).map ψ').app ⊤), hc]
      simp only [Category.assoc]
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t ↦ restrictionOfAdjunction L adj p a (b ≫ g) h F ≫
          ((compOfAdjunction L adj b g).inv.app F).app ⊤ ≫ t) ht

/-- Structural section pullback is natural in a commuting coefficient square.
Source: Stacks Project, Tags 03DR and 01FD.
(blueprint: lem-weil-pbc-qcoherent-pullback-section-square-naturality)

Proof: Naturality of the section unit moves the coefficient map through the
structural restriction. Naturality of the composition comparison moves it
through its inverse, and functoriality moves the resulting commuting coefficient
square through pullback to V. These equalities hold for arbitrary modules. -/
theorem qcoherentPullbackSection_coefficient_naturality {X Y : Scheme.{u}}
    (g : Y ⟶ X) {F F' : X.Modules} {G G' : Y.Modules}
    (ψ : (tensorPullback g).obj F ⟶ G)
    (ψ' : (tensorPullback g).obj F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
    (hab : (tensorPullback g).map a ≫ ψ' = ψ ≫ b)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    ((tensorPullback U.hom).map a).app ⊤ ≫
        qcoherentPullbackSection g F' G' ψ' U V p h =
      qcoherentPullbackSection g F G ψ U V p h ≫
        ((tensorPullback V.hom).map b).app ⊤ := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      rw [qcoherentPullbackSection_eq, qcoherentPullbackSection_eq]
      unfold tensorRestriction
      simp only [comp_to_abstract]
      exact square_coefficient_naturality (@tensorPullback)
        (fun {_ _} f ↦ Classical.choose (exists_tensorPullbackAdjunction f))
        g U.hom V.hom p h ψ ψ' a b hab

end
end AlgebraicGeometry.Scheme.Modules
