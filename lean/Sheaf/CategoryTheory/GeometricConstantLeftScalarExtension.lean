/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension
public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Mathlib.Algebra.Category.Grp.LeftExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Geometric inverse image and left scalar extension

Source: Stacks Project, Modules on Sites, Tag 03CZ; Sites, Tag 00YV;
Categories, Tag 001P (blueprint: lem-sfb-geometric-constant-left-scalar-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantLeftScalarExtension
open ConstantLeftModuleInverseImage
attribute [local instance] comp_preservesFiniteLimits

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Rebundle a fixed-ring presheaf as modules over the constant ring presheaf.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def presheafModules (R : Type u) [Ring R] :
    (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤
      PresheafOfModules.{u} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj P :=
    { obj := P.obj
      map := fun f ↦ P.map f
      map_id := fun X ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_id X)
      map_comp := fun f g ↦ by ext x; exact congrArg (fun f ↦ f x) (P.map_comp f g) }
  map f :=
    { app := f.app
      naturality := fun g ↦ by ext x; exact congrArg (fun f ↦ f x) (f.naturality g) }

/-- Restriction along the constant-ring sheafification unit, keeping the original sections.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def sections (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}] :
    Modules J R ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} R) where
  obj M :=
    { obj := fun T ↦ (ModuleCat.restrictScalars
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T).hom).obj
          (M.val.obj T)
      map := fun f ↦ ((PresheafOfModules.restrictScalars
        (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).obj M.val).map f
      map_id := fun T ↦ by
        ext x
        exact congrArg (fun f ↦ f x)
          (((PresheafOfModules.restrictScalars
            (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).obj M.val).map_id T)
      map_comp := fun f g ↦ by ext x; exact
        ((PresheafOfModules.restrictScalars
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).obj M.val).map_comp_apply f g x }
  map f :=
    { app := fun T ↦ (ModuleCat.restrictScalars
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T).hom).map
          (f.val.app T)
      naturality := fun _ _ g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }

/-- Sheafify a fixed-ring module presheaf over the sheafified constant ring.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def sheafification (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}] :
    (Cᵒᵖ ⥤ ModuleCat.{u} R) ⥤ Modules J R :=
  presheafModules R ⋙ PresheafOfModules.sheafification
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))

/-- The constant module sheaf, with its actual sheafification data.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def constant (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}] :
    ModuleCat.{u} R ⥤ Modules J R :=
  Functor.const Cᵒᵖ ⋙ sheafification J R

/-- Sectionwise balanced scalar extension before sheafification, using the recorded
arbitrary-ring left adjoint. Source: Stacks, 03CZ
(blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def tensorPresheaf {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    Modules J R ⥤ (Cᵒᵖ ⥤ ModuleCat.{u} S) :=
  sections J R ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.ringExtendScalars.{u, u} a)

/-- Sheafification of sectionwise left scalar extension, now on modules over the
constant ring sheaf. Source: Stacks, 03CZ
(blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def extension {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    Modules J R ⥤ Modules J S :=
  tensorPresheaf J a ⋙ sheafification J S

/-- The sheafified pure tensor of a constant scalar and an original local section.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def tensorSection {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S)
    (M : Modules J R) (T : Cᵒᵖ) (s : S) (m : M.val.obj T) :
    ((extension J a).obj M).val.obj T :=
  (toSheafify J (((presheafModules S).obj
    ((tensorPresheaf J a).obj M)).presheaf)).app T
      (ModuleCat.ringExtensionTmul a (((sections J R).obj M).obj T) s m)

/-- A constant local section of the constant module sheaf.
Source: Stacks, 03CZ (blueprint: lem-sfb-geometric-constant-left-scalar-extension). -/
def constantSection {R : Type u} [Ring R] [HasWeakSheafify J RingCat.{u}]
    (Q : ModuleCat.{u} R) (T : Cᵒᵖ) (q : Q) : ((constant J R).obj Q).val.obj T :=
  (toSheafify J (((presheafModules R).obj
    ((Functor.const Cᵒᵖ).obj Q)).presheaf)).app T q

private def sheafHomEquiv (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}]
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (M : Modules J R) :
    ((sheafification J R).obj P ⟶ M) ≃ (P ⟶ (sections J R).obj M) :=
  (PresheafOfModules.sheafificationHomEquiv
    (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).trans
    { toFun := fun f ↦
        { app := f.app
          naturality := fun _ _ g ↦ by
            ext x
            exact PresheafOfModules.naturality_apply f g x }
      invFun := fun f ↦
        { app := f.app
          naturality := fun g ↦ by
            ext x
            exact congrArg (fun h ↦ h x) (f.naturality g) }
      left_inv := fun f ↦ rfl
      right_inv := fun f ↦ rfl }

private def sheafAdj (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}] :
    sheafification J R ⊣ sections J R :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sheafHomEquiv J R
      homEquiv_naturality_left_symm := by
        intro P Q M f g
        have h := (PresheafOfModules.sheafificationAdjunction
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))))
            |>.homEquiv_naturality_left_symm ((presheafModules R).map f)
            { app := g.app
              naturality := fun h ↦ by
                ext x
                exact congrArg (fun k ↦ k x) (g.naturality h) }
        simp only [PresheafOfModules.sheafificationAdjunction,
          Adjunction.mkOfHomEquiv_homEquiv] at h
        dsimp only [sheafHomEquiv, Equiv.symm_trans_apply, Equiv.coe_fn_symm_mk,
          sheafification, Functor.comp_map, Functor.comp_obj, presheafModules] at h ⊢
        convert h using 1
        congr 1
      homEquiv_naturality_right := by
        intro P M N f g
        ext T x
        rfl }

private def sectionsHomEquiv (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}]
    (M N : Modules J R) :
    (M ⟶ N) ≃ ((sections J R).obj M ⟶ (sections J R).obj N) :=
  (Equiv.refl (M ⟶ N)).trans
    { toFun := (sections J R).map
      invFun := fun f ↦
        { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
            (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))) N.isSheaf).symm
            { app := f.app
              naturality := fun h ↦ by
                ext x
                exact congrArg (fun k ↦ k x) (f.naturality h) } }
      left_inv := by
        intro f
        apply SheafOfModules.hom_ext
        exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))) N.isSheaf)
            |>.symm_apply_apply f.val
      right_inv := by intro f; ext T x; rfl }

private def sectionsFullyFaithful (R : Type u) [Ring R]
    [HasWeakSheafify J RingCat.{u}] : (sections J R).FullyFaithful where
  preimage := (sectionsHomEquiv J R _ _).symm
  map_preimage := (sectionsHomEquiv J R _ _).apply_symm_apply
  preimage_map := (sectionsHomEquiv J R _ _).symm_apply_apply

private def restriction {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) : Modules J S ⥤ Modules J R :=
  SheafOfModules.restrictScalars ((constantSheaf J RingCat.{u}).map (RingCat.ofHom a))

private theorem coefficient_naturality {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (T : Cᵒᵖ) (r : R) :
    (((constantSheaf J RingCat.{u}).map (RingCat.ofHom a)).hom.app T)
        ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T (a r) := by
  exact (congrArg (fun f ↦ (f.app T).hom r)
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map (RingCat.ofHom a)))).symm

private def restrictionSectionsIso {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    restriction J a ⋙ sections J R ≅
      sections J S ⋙ (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars a) :=
  NatIso.ofComponents (fun M ↦ NatIso.ofComponents (fun T ↦
    { hom := ModuleCat.ofHom
        (X := ((sections J R).obj ((restriction J a).obj M)).obj T)
        (Y := (ModuleCat.restrictScalars a).obj (((sections J S).obj M).obj T))
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ by
            change (((constantSheaf J RingCat).map (RingCat.ofHom a)).hom.app T
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r)) •
                (show M.val.obj T from x) =
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T (a r)) •
                (show M.val.obj T from x)
            rw [coefficient_naturality] }
      inv := ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars a).obj (((sections J S).obj M).obj T))
        (Y := ((sections J R).obj ((restriction J a).obj M)).obj T)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun r x ↦ by
            change
              ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T (a r)) •
                (show M.val.obj T from x) =
              (((constantSheaf J RingCat).map (RingCat.ofHom a)).hom.app T
                ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r)) •
                  (show M.val.obj T from x)
            rw [coefficient_naturality] } }) (by intros; ext x; rfl))
    (by intros; ext T x; rfl)

private def presheafExtensionAdj {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.ringExtendScalars a) ⋙
        sheafification J S ⊣
      sections J S ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.restrictScalars a) :=
  ((ModuleCat.ringExtendScalarsAdj a).whiskerRight (C := Cᵒᵖ)).comp (sheafAdj J S)

private def extensionAdj {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) : extension J a ⊣ restriction J a :=
  (presheafExtensionAdj J a).restrictFullyFaithful (sectionsFullyFaithful J R)
    (Functor.FullyFaithful.id _) (Functor.rightUnitor (extension J a)).symm
    (restrictionSectionsIso J a).symm

private def sheafificationExtensionIso {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    (Functor.whiskeringRight Cᵒᵖ _ _).obj (ModuleCat.ringExtendScalars a) ⋙
        sheafification J S ≅ sheafification J R ⋙ extension J a :=
  (presheafExtensionAdj J a).leftAdjointUniq
    (((sheafAdj J R).comp (extensionAdj J a)).ofNatIsoRight
      (restrictionSectionsIso J a))

private theorem extensionAdj_unit_apply {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (M : Modules J R)
    (T : Cᵒᵖ) (x : M.val.obj T) :
    ((extensionAdj J a).unit.app M).val.app T x = tensorSection J a M T 1 x := by
  have h := (presheafExtensionAdj J a).map_restrictFullyFaithful_unit_app
    (sectionsFullyFaithful J R) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor (extension J a)).symm (restrictionSectionsIso J a).symm M
  have hx := congrArg (fun f ↦ f.app T x) h
  change ((extensionAdj J a).unit.app M).val.app T x =
    ((presheafExtensionAdj J a).unit.app ((sections J R).obj M)).app T x at hx
  rw [show presheafExtensionAdj J a =
    ((ModuleCat.ringExtendScalarsAdj a).whiskerRight (C := Cᵒᵖ)).comp (sheafAdj J S)
    from rfl, Adjunction.comp_unit_app] at hx
  change ((extensionAdj J a).unit.app M).val.app T x =
    (toSheafify J ((presheafModules S).obj ((tensorPresheaf J a).obj M)).presheaf).app T
      ((ModuleCat.ringExtendScalarsAdj a).unit.app (((sections J R).obj M).obj T) x) at hx
  simpa only [tensorSection, ModuleCat.ringExtensionTmul, one_smul] using hx

private theorem sheafificationExtensionIso_apply_one {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (P : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (T : Cᵒᵖ) (x : P.obj T) :
    ((sheafificationExtensionIso J a).hom.app P).val.app T
        ((toSheafify J ((presheafModules S).obj
          (((Functor.whiskeringRight Cᵒᵖ _ _).obj
            (ModuleCat.ringExtendScalars a)).obj P)).presheaf).app T
              (ModuleCat.ringExtensionTmul a (P.obj T) 1 x)) =
      tensorSection J a ((sheafification J R).obj P) T 1
        ((toSheafify J ((presheafModules R).obj P).presheaf).app T x) := by
  have h := (presheafExtensionAdj J a).unit_leftAdjointUniq_hom_app
    (((sheafAdj J R).comp (extensionAdj J a)).ofNatIsoRight
      (restrictionSectionsIso J a)) P
  have hx := congrArg (fun f ↦ f.app T x) h
  simp only [presheafExtensionAdj, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app] at hx
  change ((sheafificationExtensionIso J a).hom.app P).val.app T
      ((toSheafify J ((presheafModules S).obj
        (P ⋙ ModuleCat.ringExtendScalars a)).presheaf).app T
          ((ModuleCat.ringExtendScalarsAdj a).unit.app (P.obj T) x)) =
    ((extensionAdj J a).unit.app ((sheafification J R).obj P)).val.app T
      ((toSheafify J ((presheafModules R).obj P).presheaf).app T x) at hx
  simpa only [ModuleCat.ringExtensionTmul, one_smul, extensionAdj_unit_apply,
    Functor.whiskeringRight] using hx

private def constantExtensionPresheafIso {R S : Type u} [Ring R] [Ring S]
    (a : R →+* S) :
    ModuleCat.ringExtendScalars.{u,u} a ⋙ Functor.const Cᵒᵖ ≅
      Functor.const Cᵒᵖ ⋙ (Functor.whiskeringRight Cᵒᵖ _ _).obj
        (ModuleCat.ringExtendScalars a) :=
  NatIso.ofComponents (fun Q ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _)
    (by intros; simp)) (by intros; ext T; rfl)

private def constantExtensionIso {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    ModuleCat.ringExtendScalars.{u,u} a ⋙ constant J S ≅
      constant J R ⋙ extension J a :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantExtensionPresheafIso (C := C) a) (sheafification J S) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (sheafificationExtensionIso J a) ≪≫
    (Functor.associator _ _ _).symm

private theorem sheafification_map_unit (R : Type u) [Ring R]
    [HasWeakSheafify J RingCat.{u}] {P Q : Cᵒᵖ ⥤ ModuleCat.{u} R} (f : P ⟶ Q)
    (T : Cᵒᵖ) (x : P.obj T) :
    ((sheafification J R).map f).val.app T
        ((toSheafify J ((presheafModules R).obj P).presheaf).app T x) =
      (toSheafify J ((presheafModules R).obj Q).presheaf).app T (f.app T x) := by
  have h := congrArg (fun g ↦ g.app T x) ((sheafAdj J R).unit.naturality f)
  exact h.symm

private theorem sheafification_unit_smul (R : Type u) [Ring R]
    [HasWeakSheafify J RingCat.{u}] (P : Cᵒᵖ ⥤ ModuleCat.{u} R)
    (T : Cᵒᵖ) (r : R) (x : P.obj T) :
    (toSheafify J ((presheafModules R).obj P).presheaf).app T (r • x) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) •
        (show ((sheafification J R).obj P).val.obj T from
          (toSheafify J ((presheafModules R).obj P).presheaf).app T x) := by
  exact (((sheafAdj J R).unit.app P).app T).hom.map_smul r x

private theorem constantSection_smul {R : Type u} [Ring R]
    [HasWeakSheafify J RingCat.{u}] (Q : ModuleCat.{u} R)
    (T : Cᵒᵖ) (r : R) (q : Q) :
    constantSection J Q T (r • q) =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) •
        constantSection J Q T q :=
  sheafification_unit_smul J R ((Functor.const Cᵒᵖ).obj Q) T r q

private theorem tensorSection_smul_one {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (M : Modules J R)
    (T : Cᵒᵖ) (s : S) (x : M.val.obj T) :
    tensorSection J a M T s x =
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T s) •
        tensorSection J a M T 1 x := by
  simpa only [tensorSection, ModuleCat.ringExtensionTmul, one_smul] using
    sheafification_unit_smul J S ((tensorPresheaf J a).obj M) T s
      ((ModuleCat.ringExtendScalarsAdj a).unit.app (((sections J R).obj M).obj T) x)

private theorem constantExtensionIso_apply_one {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (Q : ModuleCat.{u} R)
    (T : Cᵒᵖ) (q : Q) :
    ((constantExtensionIso J a).hom.app Q).val.app T
        (constantSection J ((ModuleCat.ringExtendScalars a).obj Q) T
          (ModuleCat.ringExtensionTmul a Q 1 q)) =
      tensorSection J a ((constant J R).obj Q) T 1 (constantSection J Q T q) := by
  change ((sheafificationExtensionIso J a).hom.app ((Functor.const Cᵒᵖ).obj Q)).val.app T
    (((sheafification J S).map
      ((constantExtensionPresheafIso (C := C) a).hom.app Q)).val.app T
        ((toSheafify J ((presheafModules S).obj
          ((Functor.const Cᵒᵖ).obj ((ModuleCat.ringExtendScalars a).obj Q))).presheaf).app T
            (ModuleCat.ringExtensionTmul a Q 1 q))) = _
  have h := sheafification_map_unit J S
    ((constantExtensionPresheafIso (C := C) a).hom.app Q) T
      (ModuleCat.ringExtensionTmul a Q 1 q)
  exact (congrArg
    (fun x ↦ ((sheafificationExtensionIso J a).hom.app ((Functor.const Cᵒᵖ).obj Q)).val.app T x)
    h).trans (sheafificationExtensionIso_apply_one J a ((Functor.const Cᵒᵖ).obj Q) T q)

private def scalarMap (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J R) (r : R) : (V J R).obj M ⟶ (V J R).obj M where
  hom :=
    { app := fun T ↦ AddCommGrpCat.ofHom
        { toFun := fun x ↦
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality := by
        intro T T' f
        ext x
        change M.val.obj T at x
        change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T' r) •
            M.val.map f x = M.val.map f
              (((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r) • x)
        rw [M.val.map_smul]
        congr 1
        exact congrArg (fun g ↦ g r)
          ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).naturality f) }

private def scalarSet (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}]
    (M : Modules J R) (r : R) : (W J R).obj M ⟶ (W J R).obj M :=
  (U J).map (scalarMap J R M r)

section Geometric
variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (R : Type u) [Ring R] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (G : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ G) (hL : PreservesFiniteLimits L)
    (d : ConstantLeftModuleInverseImageData.{u, w} J K R L G adj hL)

private theorem inverse_scalar (M : Modules J R) (r : R) :
    scalarSet K R (d.moduleFunctor.obj M) r ≫ d.moduleSetIso.hom.app M =
      d.moduleSetIso.hom.app M ≫ L.map (scalarSet J R M r) := by
  have h := d.scalar_compatibility M r (scalarMap J R M r)
    (scalarMap K R (d.moduleFunctor.obj M) r) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  change (U K).map (scalarMap K R (d.moduleFunctor.obj M) r) ≫ _ = _
  rw [← d.moduleSetIso_compatibility]
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc, scalarSet] using
    congrArg ((U K).map (d.underlyingIso.hom.app M) ≫ ·)
      (d.abelianSetIso.hom.naturality (scalarMap J R M r))

private def directSetIso : d.moduleDirect ⋙ W J R ≅ W K R ⋙ G :=
  Functor.isoWhiskerRight d.directUnderlyingIso (U J) ≪≫
    Functor.isoWhiskerLeft (V K R) d.abelianDirectSetIso

private theorem module_unit_set (M : Modules J R) :
    (W J R).map (d.moduleAdj.unit.app M) ≫ (directSetIso J K R L G adj hL d).hom.app
      (d.moduleFunctor.obj M) ≫ G.map (d.moduleSetIso.hom.app M) =
      adj.unit.app ((W J R).obj M) := by
  dsimp only [Functor.comp_obj]
  have hn := d.abelianDirectSetIso.hom.naturality (d.underlyingIso.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← d.moduleSetIso_compatibility, Functor.map_comp]
  change (U J).map ((V J R).map (d.moduleAdj.unit.app M)) ≫
      (U J).map (d.directUnderlyingIso.hom.app (d.moduleFunctor.obj M)) ≫
      d.abelianDirectSetIso.hom.app ((V K R).obj (d.moduleFunctor.obj M)) ≫
      G.map ((U K).map (d.underlyingIso.hom.app M)) ≫
      G.map (d.abelianSetIso.hom.app ((V J R).obj M)) = _
  rw [← Category.assoc (d.abelianDirectSetIso.hom.app _), ← hn]
  simp only [Category.assoc] at hn ⊢
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc] at *
  rw [d.unit_compatibility]
  exact d.abelian_unit ((V J R).obj M)

private theorem module_hom_set (M : Modules J R) (N : Modules K R)
    (f : d.moduleFunctor.obj M ⟶ N) :
    (W J R).map (d.moduleAdj.homEquiv M N f) ≫
      (directSetIso J K R L G adj hL d).hom.app N =
    adj.homEquiv ((W J R).obj M) ((W K R).obj N)
      (d.moduleSetIso.inv.app M ≫ (W K R).map f) := by
  dsimp only [Functor.comp_obj]
  have hn := (directSetIso J K R L G adj hL d).hom.naturality f
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  change (W J R).map (d.moduleDirect.map f) ≫
      (directSetIso J K R L G adj hL d).hom.app N =
    (directSetIso J K R L G adj hL d).hom.app (d.moduleFunctor.obj M) ≫
      G.map ((W K R).map f) at hn
  rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, hn]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := module_unit_set J K R L G adj hL d M
  have h' := congrArg (· ≫ G.map (d.moduleSetIso.inv.app M)) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at h'
  change (W J R).map (d.moduleAdj.unit.app M) ≫
      (directSetIso J K R L G adj hL d).hom.app (d.moduleFunctor.obj M) ≫
      G.map (𝟙 ((W K R).obj (d.moduleFunctor.obj M))) = _ at h'
  dsimp only [Functor.comp_obj, Functor.id_obj] at h'
  simp only [G.map_id, Category.comp_id] at h'
  rw [← Category.assoc, h', Category.assoc]

private theorem module_counit_set (N : Modules K R) :
    d.moduleSetIso.inv.app (d.moduleDirect.obj N) ≫
      (W K R).map (d.moduleAdj.counit.app N) =
    L.map ((directSetIso J K R L G adj hL d).hom.app N) ≫
      adj.counit.app ((W K R).obj N) := by
  apply (adj.homEquiv ((W J R).obj (d.moduleDirect.obj N)) ((W K R).obj N)).injective
  have h := module_hom_set J K R L G adj hL d
    (d.moduleDirect.obj N) N (d.moduleAdj.counit.app N)
  have hc : d.moduleAdj.homEquiv (d.moduleDirect.obj N) N
      (d.moduleAdj.counit.app N) = 𝟙 _ := by
    rw [← d.moduleAdj.homEquiv_symm_id]
    exact Equiv.apply_symm_apply _ _
  rw [hc, Functor.map_id, Category.id_comp] at h
  rw [← h]
  exact ((adj.homEquiv _ _).apply_symm_apply
    ((directSetIso J K R L G adj hL d).hom.app N)).symm

private theorem direct_scalar (N : Modules K R) (r : R) :
    scalarSet J R (d.moduleDirect.obj N) r ≫
      (directSetIso J K R L G adj hL d).hom.app N =
    (directSetIso J K R L G adj hL d).hom.app N ≫ G.map (scalarSet K R N r) := by
  have hlin : scalarSet K R (d.moduleFunctor.obj (d.moduleDirect.obj N)) r ≫
      (W K R).map (d.moduleAdj.counit.app N) =
    (W K R).map (d.moduleAdj.counit.app N) ≫ scalarSet K R N r := by
    ext T x
    exact ((d.moduleAdj.counit.app N).val.app T).hom.map_smul _ x
  have hs := inverse_scalar J K R L G adj hL d (d.moduleDirect.obj N) r
  have hc := module_counit_set J K R L G adj hL d N
  have h : L.map (scalarSet J R (d.moduleDirect.obj N) r) ≫
      (L.map ((directSetIso J K R L G adj hL d).hom.app N) ≫
        adj.counit.app ((W K R).obj N)) =
    (L.map ((directSetIso J K R L G adj hL d).hom.app N) ≫
        adj.counit.app ((W K R).obj N)) ≫ scalarSet K R N r := by
    rw [← hc]
    have hs' := congrArg (d.moduleSetIso.inv.app (d.moduleDirect.obj N) ≫ ·) hs
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] at hs'
    rw [← hs']
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [hlin]
  change L.map (scalarSet J R (d.moduleDirect.obj N) r) ≫
      (adj.homEquiv _ _).symm ((directSetIso J K R L G adj hL d).hom.app N) =
    (adj.homEquiv _ _).symm ((directSetIso J K R L G adj hL d).hom.app N) ≫
      scalarSet K R N r at h
  have h' := congrArg (adj.homEquiv ((W J R).obj (d.moduleDirect.obj N))
    ((W K R).obj N)) h
  change adj.homEquiv ((W J R).obj (d.moduleDirect.obj N)) ((W K R).obj N)
      (L.map (scalarSet J R (d.moduleDirect.obj N) r) ≫
        (adj.homEquiv ((W J R).obj (d.moduleDirect.obj N)) ((W K R).obj N)).symm
          ((directSetIso J K R L G adj hL d).hom.app N)) = _ at h'
  change adj.homEquiv _ _
      (L.map (scalarSet J R (d.moduleDirect.obj N) r) ≫
        (adj.homEquiv ((W J R).obj (d.moduleDirect.obj N)) ((W K R).obj N)).symm
          ((directSetIso J K R L G adj hL d).hom.app N)) =
    adj.homEquiv _ _
      ((adj.homEquiv ((W J R).obj (d.moduleDirect.obj N)) ((W K R).obj N)).symm
        ((directSetIso J K R L G adj hL d).hom.app N) ≫ scalarSet K R N r) at h'
  rw [adj.homEquiv_naturality_left] at h'
  simpa only [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] using h'

end Geometric


private def restrictionSetsIso {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) :
    restriction J a ⋙ W J R ≅ W J S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

private def tensorMap {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (M : Modules J R) (s : S) :
    (W J R).obj M ⟶ (W J S).obj ((extension J a).obj M) :=
  (W J R).map ((extensionAdj J a).unit.app M) ≫
    (restrictionSetsIso J a).hom.app ((extension J a).obj M) ≫
      scalarSet J S ((extension J a).obj M) s

private theorem tensorMap_apply {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (M : Modules J R) (s : S)
    (T : Cᵒᵖ) (x : M.val.obj T) :
    (tensorMap J a M s).hom.app T x = tensorSection J a M T s x := by
  change ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T s) •
    (show ((extension J a).obj M).val.obj T from
      ((extensionAdj J a).unit.app M).val.app T x) = _
  rw [extensionAdj_unit_apply, ← tensorSection_smul_one]

private def linearHomOfConstantScalars
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarMap J Λ M r ≫ f = f ≫ scalarMap J Λ N r) : M ⟶ N := by
  let α := toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of Λ))
  let g : (PresheafOfModules.restrictScalars α).obj M.val ⟶
      (PresheafOfModules.restrictScalars α).obj N.val :=
    PresheafOfModules.homMk f.hom (by
      intro T r x
      exact congrArg (fun k ↦ k.hom.app T x) (hf r))
  exact ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
    α N.isSheaf).symm g⟩


private def abelianLift
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) : F ⟶ G := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact (H.preimage (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G)
    (ObjectProperty.homMk α)).hom

private theorem abelianLift_forget
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    (F G : A ⥤ AddCommGrpCat.{u}) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ forget AddCommGrpCat ⟶ G ⋙ forget AddCommGrpCat) :
    Functor.whiskerRight (abelianLift F G α) (forget AddCommGrpCat) = α := by
  let H := (AddCommGrpCat.leftExactFunctorForgetEquivalence A).functor
  exact congrArg (fun f ↦ f.hom) (H.map_preimage
    (X := LeftExactFunctor.of F) (Y := LeftExactFunctor.of G) (ObjectProperty.homMk α))

private theorem linearHomOfConstantScalars_forget
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify J RingCat.{u}]
    {M N : Modules J Λ} (f : (V J Λ).obj M ⟶ (V J Λ).obj N)
    (hf : ∀ r : Λ,
      scalarMap J Λ M r ≫ f = f ≫ scalarMap J Λ N r) :
    (V J Λ).map (linearHomOfConstantScalars J Λ f hf) = f := by
  rfl

private theorem moduleNatTrans
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify K RingCat.{u}]
    (F G : A ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (α : F ⋙ W K Λ ⟶ G ⋙ W K Λ)
    (hα : ∀ (M : A) (r : Λ),
      (U K).map (scalarMap K Λ (F.obj M) r) ≫ α.app M =
        α.app M ≫ (U K).map (scalarMap K Λ (G.obj M) r)) :
    ∃ a : F ⟶ G, Functor.whiskerRight a (W K Λ) = α := by
  have : PreservesFiniteLimits (V K Λ) := inferInstance
  have : PreservesFiniteLimits (sheafToPresheaf K AddCommGrpCat.{u}) := inferInstance
  have (T : Dᵒᵖ) :
      PreservesFiniteLimits ((evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  have (T : Dᵒᵖ) : PreservesFiniteLimits
      (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
        (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T) := inferInstance
  let b := fun T : Dᵒᵖ ↦ abelianLift
    (F ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    (G ⋙ V K Λ ⋙ sheafToPresheaf K AddCommGrpCat.{u} ⋙
      (evaluation Dᵒᵖ AddCommGrpCat.{u}).obj T)
    { app := fun N ↦ (α.app N).hom.app T
      naturality := by
        intro M N f
        exact congrArg (fun k ↦ k.hom.app T) (α.naturality f) }
  have hb (T : Dᵒᵖ) (M : A) :
      (forget AddCommGrpCat).map ((b T).app M) = (α.app M).hom.app T := by
    dsimp only [b]
    exact congr_app (abelianLift_forget _ _ _) M
  let a : F ⋙ V K Λ ⟶ G ⋙ V K Λ :=
    { app := fun M ↦
        { hom :=
            { app := fun T ↦ (b T).app M
              naturality := by
                intro T S f
                apply (forget AddCommGrpCat).map_injective
                change (forget AddCommGrpCat).map (((F ⋙ V K Λ).obj M).obj.map f) ≫
                    (forget AddCommGrpCat).map ((b S).app M) =
                  (forget AddCommGrpCat).map ((b T).app M) ≫
                    (forget AddCommGrpCat).map (((G ⋙ V K Λ).obj M).obj.map f)
                rw [hb, hb]
                exact (α.app M).hom.naturality f } }
      naturality := by
        intro M N f
        ext T x
        exact congrArg (fun k ↦ k.hom x) ((b T).naturality f) }
  have ha (M : A) : (U K).map (a.app M) = α.app M := by
    ext T x
    exact congrArg (fun k ↦ k x) (hb T M)
  refine ⟨
    { app := fun M ↦ linearHomOfConstantScalars K Λ (a.app M) (fun r ↦ ?_)
      naturality := ?_ }, ?_⟩
  · apply (U K).map_injective
    simpa only [Functor.map_comp, ha] using hα M r
  · intro M N f
    apply (V K Λ).map_injective
    simpa only [Functor.map_comp, Functor.comp_map, linearHomOfConstantScalars_forget]
      using a.naturality f
  · ext M T x
    exact congrArg (fun k ↦ k.hom.app T x) (ha M)

private theorem moduleIsoOfScalars
    {A : Type*} [Category.{u} A] [Preadditive A] [HasFiniteBiproducts A]
    {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    (Λ : Type u) [Ring Λ] [HasWeakSheafify K RingCat.{u}]
    (F G : A ⥤ Modules K Λ)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (e : F ⋙ W K Λ ≅ G ⋙ W K Λ)
    (he : ∀ (M : A) (r : Λ),
      (U K).map (scalarMap K Λ (F.obj M) r) ≫ e.hom.app M =
        e.hom.app M ≫ (U K).map (scalarMap K Λ (G.obj M) r)) :
    ∃ i : F ≅ G, Functor.whiskerRight i.hom (W K Λ) = e.hom := by
  obtain ⟨a, ha⟩ := moduleNatTrans K Λ F G e.hom he
  have : IsIso (Functor.whiskerRight a (W K Λ)) := by rw [ha]; infer_instance
  have : IsIso (((Functor.whiskeringRight _ _ _).obj (W K Λ)).map a) := by
    change IsIso (Functor.whiskerRight a (W K Λ))
    infer_instance
  have : IsIso a := isIso_of_reflects_iso a ((Functor.whiskeringRight _ _ _).obj (W K Λ))
  exact ⟨asIso a, ha⟩


private theorem restriction_scalar {R S : Type u} [Ring R] [Ring S]
    [HasWeakSheafify J RingCat.{u}] (a : R →+* S) (N : Modules J S) (r : R) :
    scalarSet J R ((restriction J a).obj N) r ≫ (restrictionSetsIso J a).hom.app N =
      (restrictionSetsIso J a).hom.app N ≫ scalarSet J S N (a r) := by
  ext T x
  change (((constantSheaf J RingCat).map (RingCat.ofHom a)).hom.app T
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app T r)) •
      (show N.val.obj T from x) =
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of S))).app T (a r)) •
      (show N.val.obj T from x)
  rw [coefficient_naturality]

section GeometricComparison
variable {D : Type u} [SmallCategory D] (K : GrothendieckTopology D)
    {R S : Type u} [Ring R] [Ring S] [HasWeakSheafify J RingCat.{u}]
    [HasWeakSheafify K RingCat.{u}] (a : R →+* S)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (G : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ G) (hL : PreservesFiniteLimits L)
    (dR : ConstantLeftModuleInverseImageData.{u, w} J K R L G adj hL)
    (dS : ConstantLeftModuleInverseImageData.{u, w} J K S L G adj hL)

private def scalarDirectSetsLeft :
    (dS.moduleDirect ⋙ restriction J a) ⋙ W J R ≅ W K S ⋙ G :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft dS.moduleDirect (restrictionSetsIso J a) ≪≫
    directSetIso J K S L G adj hL dS

private def scalarDirectSetsRight :
    (restriction K a ⋙ dR.moduleDirect) ⋙ W J R ≅ W K S ⋙ G :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (restriction K a) (directSetIso J K R L G adj hL dR) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictionSetsIso K a) G

private theorem scalarDirectSetsLeft_scalar (N : Modules K S) (r : R) :
    scalarSet J R ((restriction J a).obj (dS.moduleDirect.obj N)) r ≫
        (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N =
      (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N ≫
        G.map (scalarSet K S N (a r)) := by
  change scalarSet J R ((restriction J a).obj (dS.moduleDirect.obj N)) r ≫
      ((restrictionSetsIso J a).hom.app (dS.moduleDirect.obj N) ≫
        (directSetIso J K S L G adj hL dS).hom.app N) = _
  rw [← Category.assoc, restriction_scalar, Category.assoc,
    direct_scalar J K S L G adj hL dS]
  rfl

private theorem scalarDirectSetsRight_scalar (N : Modules K S) (r : R) :
    scalarSet J R (dR.moduleDirect.obj ((restriction K a).obj N)) r ≫
        (scalarDirectSetsRight J K a L G adj hL dR).hom.app N =
      (scalarDirectSetsRight J K a L G adj hL dR).hom.app N ≫
        G.map (scalarSet K S N (a r)) := by
  change scalarSet J R (dR.moduleDirect.obj ((restriction K a).obj N)) r ≫
      ((directSetIso J K R L G adj hL dR).hom.app ((restriction K a).obj N) ≫
        G.map ((restrictionSetsIso K a).hom.app N)) = _
  rw [← Category.assoc, direct_scalar J K R L G adj hL dR, Category.assoc,
    ← Functor.map_comp, restriction_scalar, Functor.map_comp]
  rfl

private theorem scalarDirectComparison :
    ∃ rho : dS.moduleDirect ⋙ restriction J a ≅ restriction K a ⋙ dR.moduleDirect,
      Functor.whiskerRight rho.hom (W J R) =
        ((scalarDirectSetsLeft J K a L G adj hL dS) ≪≫
          (scalarDirectSetsRight J K a L G adj hL dR).symm).hom := by
  have : PreservesLimits dS.moduleDirect := dS.moduleAdj.rightAdjoint_preservesLimits
  have : PreservesLimits dR.moduleDirect := dR.moduleAdj.rightAdjoint_preservesLimits
  have : PreservesLimits (restriction J a) := (extensionAdj J a).rightAdjoint_preservesLimits
  have : PreservesLimits (restriction K a) := (extensionAdj K a).rightAdjoint_preservesLimits
  let : HasFiniteBiproducts (Modules K S) := .of_hasFiniteProducts
  let e := scalarDirectSetsLeft J K a L G adj hL dS ≪≫
    (scalarDirectSetsRight J K a L G adj hL dR).symm
  apply moduleIsoOfScalars J R _ _ e
  intro N r
  let l := scalarDirectSetsLeft J K a L G adj hL dS
  let er := scalarDirectSetsRight J K a L G adj hL dR
  change scalarSet J R _ _ ≫ (l.hom.app N ≫ er.inv.app N) =
    (l.hom.app N ≫ er.inv.app N) ≫ scalarSet J R _ _
  apply (cancel_mono (er.hom.app N)).mp
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc]
  rw [show scalarSet J R (dR.moduleDirect.obj ((restriction K a).obj N)) r ≫
      er.hom.app N = er.hom.app N ≫ G.map (scalarSet K S N (a r)) from
    scalarDirectSetsRight_scalar J K a L G adj hL dR N r]
  simp only [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  exact scalarDirectSetsLeft_scalar J K a L G adj hL dS N r

private def geometricExtensionIso
    (rho : dS.moduleDirect ⋙ restriction J a ≅ restriction K a ⋙ dR.moduleDirect) :
    extension J a ⋙ dS.moduleFunctor ≅ dR.moduleFunctor ⋙ extension K a :=
  ((extensionAdj J a).comp dS.moduleAdj).leftAdjointUniq
    ((dR.moduleAdj.comp (extensionAdj K a)).ofNatIsoRight rho.symm)

private theorem scalarSet_one {E : Type u} [SmallCategory E]
    (H : GrothendieckTopology E) (A : Type u) [Ring A]
    [HasWeakSheafify H RingCat.{u}] (M : Modules H A) :
    scalarSet H A M 1 = 𝟙 _ := by
  ext T x
  change M.val.obj T at x
  change ((toSheafify H ((Functor.const Eᵒᵖ).obj (RingCat.of A))).app T 1) • x = x
  rw [map_one, one_smul]

private theorem tensorMap_one {E : Type u} [SmallCategory E]
    (H : GrothendieckTopology E) {A B : Type u} [Ring A] [Ring B]
    [HasWeakSheafify H RingCat.{u}] (b : A →+* B) (M : Modules H A) :
    tensorMap H b M 1 = (W H A).map ((extensionAdj H b).unit.app M) ≫
      (restrictionSetsIso H b).hom.app ((extension H b).obj M) := by
  simp only [tensorMap, scalarSet_one, Category.comp_id]

private theorem extension_hom_set {E : Type u} [SmallCategory E]
    (H : GrothendieckTopology E) {A B : Type u} [Ring A] [Ring B]
    [HasWeakSheafify H RingCat.{u}] (b : A →+* B)
    (M : Modules H A) (N : Modules H B) (f : (extension H b).obj M ⟶ N) :
    (W H A).map ((extensionAdj H b).homEquiv M N f) ≫
        (restrictionSetsIso H b).hom.app N =
      tensorMap H b M 1 ≫ (W H B).map f := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, tensorMap_one, Category.assoc]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg ((W H A).map ((extensionAdj H b).unit.app M) ≫ ·)
      ((restrictionSetsIso H b).hom.naturality f)

private theorem compositeLeft_hom_set
    (M : Modules J R) (N : Modules K S)
    (f : dS.moduleFunctor.obj ((extension J a).obj M) ⟶ N) :
    (W J R).map (((extensionAdj J a).comp dS.moduleAdj).homEquiv M N f) ≫
        (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N =
      adj.homEquiv ((W J R).obj M) ((W K S).obj N)
        (L.map (tensorMap J a M 1) ≫ dS.moduleSetIso.inv.app ((extension J a).obj M) ≫
          (W K S).map f) := by
  rw [Adjunction.comp_homEquiv]
  change (W J R).map ((extensionAdj J a).homEquiv _ _
      (dS.moduleAdj.homEquiv _ _ f)) ≫
      ((restrictionSetsIso J a).hom.app (dS.moduleDirect.obj N) ≫
        (directSetIso J K S L G adj hL dS).hom.app N) = _
  rw [← Category.assoc, extension_hom_set, Category.assoc, module_hom_set]
  exact (adj.homEquiv_naturality_left (tensorMap J a M 1) _).symm

private theorem compositeRight_hom_set
    (M : Modules J R) (N : Modules K S)
    (f : (extension K a).obj (dR.moduleFunctor.obj M) ⟶ N) :
    (W J R).map ((dR.moduleAdj.comp (extensionAdj K a)).homEquiv M N f) ≫
        (scalarDirectSetsRight J K a L G adj hL dR).hom.app N =
      adj.homEquiv ((W J R).obj M) ((W K S).obj N)
        (dR.moduleSetIso.inv.app M ≫ tensorMap K a (dR.moduleFunctor.obj M) 1 ≫
          (W K S).map f) := by
  rw [Adjunction.comp_homEquiv]
  change (W J R).map (dR.moduleAdj.homEquiv _ _
      ((extensionAdj K a).homEquiv _ _ f)) ≫
      ((directSetIso J K R L G adj hL dR).hom.app ((restriction K a).obj N) ≫
        G.map ((restrictionSetsIso K a).hom.app N)) = _
  rw [← Category.assoc, module_hom_set, ← adj.homEquiv_naturality_right]
  congr 1
  rw [Category.assoc, extension_hom_set]

private theorem geometricExtensionIso_one
    (rho : dS.moduleDirect ⋙ restriction J a ≅ restriction K a ⋙ dR.moduleDirect)
    (hrho : Functor.whiskerRight rho.hom (W J R) =
      ((scalarDirectSetsLeft J K a L G adj hL dS) ≪≫
        (scalarDirectSetsRight J K a L G adj hL dR).symm).hom)
    (M : Modules J R) :
    L.map (tensorMap J a M 1) ≫ dS.moduleSetIso.inv.app ((extension J a).obj M) ≫
        (W K S).map ((geometricExtensionIso J K a L G adj hL dR dS rho).hom.app M) =
      dR.moduleSetIso.inv.app M ≫ tensorMap K a (dR.moduleFunctor.obj M) 1 := by
  let c := geometricExtensionIso J K a L G adj hL dR dS rho
  let N := (extension K a).obj (dR.moduleFunctor.obj M)
  have h := ((extensionAdj J a).comp dS.moduleAdj).homEquiv_leftAdjointUniq_hom_app
    ((dR.moduleAdj.comp (extensionAdj K a)).ofNatIsoRight rho.symm) M
  change ((extensionAdj J a).comp dS.moduleAdj).homEquiv M N (c.hom.app M) = _ at h
  rw [← Adjunction.homEquiv_id, Adjunction.homEquiv_ofNatIsoRight_apply] at h
  have hm := congrArg (fun f ↦ (W J R).map f ≫
    (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N) h
  rw [compositeLeft_hom_set, Functor.map_comp] at hm
  have hr : (W J R).map (rho.inv.app N) ≫
      (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N =
    (scalarDirectSetsRight J K a L G adj hL dR).hom.app N := by
    have hh := congr_app hrho N
    change (W J R).map (rho.hom.app N) =
      (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N ≫
        (scalarDirectSetsRight J K a L G adj hL dR).inv.app N at hh
    apply (cancel_epi ((W J R).map (rho.hom.app N))).mp
    rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp, hh, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change adj.homEquiv _ _ _ =
    (W J R).map ((dR.moduleAdj.comp (extensionAdj K a)).homEquiv M N (𝟙 N)) ≫
      (W J R).map (rho.inv.app N) ≫
      (scalarDirectSetsLeft J K a L G adj hL dS).hom.app N at hm
  rw [hr, compositeRight_hom_set] at hm
  have hh := (adj.homEquiv _ _).injective hm
  ext T x
  exact congrArg (fun k ↦ k.hom.app T x) hh

private theorem scalarSet_naturality {E : Type u} [SmallCategory E]
    (H : GrothendieckTopology E) (A : Type u) [Ring A]
    [HasWeakSheafify H RingCat.{u}] {M N : Modules H A} (f : M ⟶ N) (r : A) :
    scalarSet H A M r ≫ (W H A).map f =
      (W H A).map f ≫ scalarSet H A N r := by
  ext T x
  exact (f.val.app T).hom.map_smul _ x

private theorem tensorMap_scalar {E : Type u} [SmallCategory E]
    (H : GrothendieckTopology E) {A B : Type u} [Ring A] [Ring B]
    [HasWeakSheafify H RingCat.{u}] (b : A →+* B) (M : Modules H A) (s : B) :
    tensorMap H b M s = tensorMap H b M 1 ≫
      scalarSet H B ((extension H b).obj M) s := by
  rw [tensorMap_one]
  rfl

private theorem geometricExtensionIso_tensor
    (rho : dS.moduleDirect ⋙ restriction J a ≅ restriction K a ⋙ dR.moduleDirect)
    (hrho : Functor.whiskerRight rho.hom (W J R) =
      ((scalarDirectSetsLeft J K a L G adj hL dS) ≪≫
        (scalarDirectSetsRight J K a L G adj hL dR).symm).hom)
    (M : Modules J R) (s : S) :
    L.map (tensorMap J a M s) ≫ dS.moduleSetIso.inv.app ((extension J a).obj M) ≫
        (W K S).map ((geometricExtensionIso J K a L G adj hL dR dS rho).hom.app M) =
      dR.moduleSetIso.inv.app M ≫ tensorMap K a (dR.moduleFunctor.obj M) s := by
  have hs : L.map (scalarSet J S ((extension J a).obj M) s) ≫
      dS.moduleSetIso.inv.app ((extension J a).obj M) =
    dS.moduleSetIso.inv.app ((extension J a).obj M) ≫
      scalarSet K S (dS.moduleFunctor.obj ((extension J a).obj M)) s := by
    apply (cancel_epi (dS.moduleSetIso.hom.app ((extension J a).obj M))).mp
    rw [← Category.assoc, ← inverse_scalar J K S L G adj hL dS]
    simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
    ext T x
    rfl
  rw [tensorMap_scalar J a M s, Functor.map_comp, Category.assoc, ← Category.assoc
    (L.map (scalarSet J S ((extension J a).obj M) s)), hs]
  rw [Category.assoc, scalarSet_naturality]
  have hh := congrArg (· ≫ scalarSet K S ((extension K a).obj
      (dR.moduleFunctor.obj M)) s)
    (geometricExtensionIso_one J K a L G adj hL dR dS rho hrho M)
  rw [tensorMap_scalar K a (dR.moduleFunctor.obj M) s]
  simp only [Category.assoc] at hh ⊢
  ext T x
  exact congrArg (fun k ↦ k.hom.app T x) hh

end GeometricComparison

end CategoryTheory.ConstantLeftScalarExtension

namespace CategoryTheory
open ConstantLeftModuleInverseImage ConstantLeftScalarExtension

/-- Geometric inverse image commutes with sheafified extension of left scalars.
The section maps `t` and `t'` are specified on every section by `tensorSection`;
the last equality transports these maps by the given geometric inverse image.
Thus it is the pure-tensor equation, interpreted through the normalized underlying
set-sheaf comparisons, and hence also through the adjunction-unit images of sections.

Source: Stacks, 03CZ, 00YV, and 001P
(blueprint: lem-sfb-geometric-constant-left-scalar-extension).

Proof, node steps 1--4: sectionwise scalar extension is left adjoint to scalar
restriction by the formulas v ↦ (m ↦ v(1 tensor m)) and
w ↦ (s tensor m ↦ s w(m)). The balancing equation uses the given ring map,
without commutativity. Sheafification gives the same adjunction on sheaves.
The normalized module lifts have the original underlying abelian adjunction unit;
the triangle identity then identifies their counits as well. Taking adjuncts of
scalar-linearity of the counit identifies the right-adjoint scalar endomorphism
with the direct image of the original scalar endomorphism. Thus restriction
commutes with geometric direct image by the identity on underlying abelian
sheaves. Composing these two scalar adjunctions with the geometric module
adjunctions gives natural Hom bijections between the displayed composites.
Co-Yoneda (lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection) gives the natural
isomorphism. Tracking the identity through the five bijections gives its equation
at 1 tensor m: both scalar adjunctions evaluate at 1 tensor -, and the geometric
triangle identities cancel their units and counits. S-linearity and normalization
on constant scalars give the same equation for every s tensor m. These are
identities of sheaf maps, so no pointwise formula for the inverse image is assumed.
Uses def-pod-ring-scalar-extension, def-weil-pbc-sheafification,
lem-pe-constant-left-module-transport, and lem-pe-constant-left-module-inverse-image. -/
theorem geometric_constant_left_scalar_extension
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {R S : Type u} [Ring R] [Ring S] (a : R →+* S)
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (G : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ G) (hL : PreservesFiniteLimits L)
    (dR : ConstantLeftModuleInverseImageData.{u, w} J K R L G adj hL)
    (dS : ConstantLeftModuleInverseImageData.{u, w} J K S L G adj hL) :
    ∃ c : extension J a ⋙ dS.moduleFunctor ≅ dR.moduleFunctor ⋙ extension K a,
      ∀ (M : Modules J R) (s : S),
        ∃ (t : (W J R).obj M ⟶ (W J S).obj ((extension J a).obj M))
          (t' : (W K R).obj (dR.moduleFunctor.obj M) ⟶
            (W K S).obj ((extension K a).obj (dR.moduleFunctor.obj M))),
          (∀ (T : Cᵒᵖ) (m : M.val.obj T),
            t.hom.app T m = tensorSection J a M T s m) ∧
          (∀ (T : Dᵒᵖ) (m : (dR.moduleFunctor.obj M).val.obj T),
            t'.hom.app T m = tensorSection K a (dR.moduleFunctor.obj M) T s m) ∧
          L.map t ≫ dS.moduleSetIso.inv.app ((extension J a).obj M) ≫
            (W K S).map (c.hom.app M) = dR.moduleSetIso.inv.app M ≫ t' := by
  obtain ⟨rho, hrho⟩ := scalarDirectComparison J K a L G adj hL dR dS
  refine ⟨geometricExtensionIso J K a L G adj hL dR dS rho, ?_⟩
  intro M s
  refine ⟨tensorMap J a M s, tensorMap K a (dR.moduleFunctor.obj M) s,
    tensorMap_apply J a M s, tensorMap_apply K a (dR.moduleFunctor.obj M) s, ?_⟩
  exact geometricExtensionIso_tensor J K a L G adj hL dR dS rho hrho M s

/-- Constant left modules commute with extension of scalars, naturally in the module,
with the specified pure-tensor formula for the sheafification units.

Source: Stacks, 03CZ and 001P
(blueprint: lem-sfb-geometric-constant-left-scalar-extension).

Proof, node steps 5--6: for an S-module sheaf N, the scalar adjunction identifies
maps from E of the constant sheaf Q with maps from that constant sheaf to Res N.
The sheafification universal property identifies the latter with presheaf maps
from the constant presheaf Q. The presheaf scalar adjunction identifies these
with maps from the constant presheaf S tensor_R Q to N, and sheafification
identifies these with maps from its constant sheaf. Co-Yoneda gives the displayed
isomorphism, and uniqueness makes it natural in Q. Following the identity of
E(constant Q) through the bijections sends s tensor q to s times the scalar-unit
image of the constant section q, precisely the displayed formula. No terminal
object of the site, flatness, finiteness or nonzero-coefficient assumption occurs.
Uses def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification,
def-pod-ring-scalar-extension, and
lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection. -/
theorem constant_left_scalar_extension
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    {R S : Type u} [Ring R] [Ring S] (a : R →+* S)
    [HasWeakSheafify J RingCat.{u}] :
    ∃ e : ModuleCat.ringExtendScalars.{u, u} a ⋙ constant J S ≅
        constant J R ⋙ extension J a,
      ∀ (Q : ModuleCat.{u} R) (T : Cᵒᵖ) (s : S) (q : Q),
        (e.hom.app Q).val.app T
          (constantSection J ((ModuleCat.ringExtendScalars.{u, u} a).obj Q) T
            (ModuleCat.ringExtensionTmul a Q s q)) =
          tensorSection J a ((constant J R).obj Q) T s (constantSection J Q T q) := by
  refine ⟨constantExtensionIso J a, ?_⟩
  intro Q T s q
  have h := constantExtensionIso_apply_one J a Q T q
  change ((constantExtensionIso J a).hom.app Q).val.app T
    (constantSection J ((ModuleCat.ringExtendScalars a).obj Q) T
      (s • (show (ModuleCat.ringExtendScalars a).obj Q from
        ((ModuleCat.ringExtendScalarsAdj a).unit.app Q) q))) = _
  rw [constantSection_smul]
  rw [(((constantExtensionIso J a).hom.app Q).val.app T).hom.map_smul]
  have h' : ((constantExtensionIso J a).hom.app Q).val.app T
      (constantSection J ((ModuleCat.ringExtendScalars a).obj Q) T
        (((ModuleCat.ringExtendScalarsAdj a).unit.app Q) q)) =
    tensorSection J a ((constant J R).obj Q) T 1 (constantSection J Q T q) := by
    simpa only [ModuleCat.ringExtensionTmul, one_smul] using h
  rw [h', ← tensorSection_smul_one]

end CategoryTheory
