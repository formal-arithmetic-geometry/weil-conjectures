/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Geometric stalks of étale sum extension

Source: Stacks Project, Tag 03S5, `proposition-describe-jshriek`, and Tag 0710,
`lemma-stalk-j-shriek` (blueprint: lem-amb-etale-sum-stalks).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

namespace AlgebraicGeometry

namespace Etale.SumStalks

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
  (A : Type (u + 1)) [CommRing A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)

private local instance moduleLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}

private abbrev base : U.Etale ⥤ X.Etale := MorphismProperty.Over.map ⊤ (inferInstance : Etale f)

private noncomputable abbrev sum (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ModuleCat.{u + 1} A :=
  ModuleCat.of A (⨁ (z : Over.mk x ⟶ Over.mk f),
    ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F)

private noncomputable abbrev presheaf (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A :=
  (base f).op.lan.obj F

-- The Kan-extension and stalk universal properties detect equality on section germs.
private lemma hom_ext (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    {T : ModuleCat.{u + 1} A}
    {g h : ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ⟶ T}
    (he : ∀ (W : U.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)),
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber (A := ModuleCat.{u + 1} A)
          ((base f).obj W) v (presheaf f A F) ≫ g =
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber (A := ModuleCat.{u + 1} A)
          ((base f).obj W) v (presheaf f A F) ≫ h) : g = h := by
  apply ((Scheme.pointSmallEtale x).skyscraperPresheafHomEquiv (A := ModuleCat.{u + 1} A)).injective
  apply Functor.hom_ext_of_isLeftKanExtension _ ((base f).op.lanUnit.app F)
  apply NatTrans.ext
  funext W
  apply Pi.hom_ext
  intro v
  simpa using he W.unop v

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forgetPoint (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W) :=
  Over.homMk w.left (by
    change w.left ≫ (W.hom ≫ f) = x
    have hw : w.left ≫ W.hom = z.left := Over.w w
    rw [← Category.assoc, hw]
    exact Over.w z)

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forwardFamily
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (W : U.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    F.obj (op W) ⟶ sum f A x F :=
  (Scheme.pointSmallEtale (v.left ≫ W.hom)).toPresheafFiber W
    (Over.homMk v.left) F ≫
      ModuleCat.ofHom (DirectSum.lof A _
        (fun z : Over.mk x ⟶ Over.mk f ↦
          ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F)
        (v ≫ Over.homMk W.hom))

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forwardFamily_eq (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    forwardFamily f A x F W (forgetPoint f x z W w) =
      (Scheme.pointSmallEtale z.left).toPresheafFiber W w F ≫
        ModuleCat.ofHom (DirectSum.lof A _
          (fun z : Over.mk x ⟶ Over.mk f ↦
            ((Scheme.pointSmallEtale z.left).presheafFiber
              (A := ModuleCat.{u + 1} A)).obj F) z) := by
  obtain ⟨z', hz, rfl⟩ := Over.homMk_surjective z
  obtain ⟨w', hw, rfl⟩ := Over.homMk_surjective w
  change (Spec (.of Ω) ⟶ U) at z'
  change (Spec (.of Ω) ⟶ W.left) at w'
  change w' ≫ W.hom = z' at hw
  subst z'
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def forwardTransformation
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    F ⟶ (base f).op ⋙ (Scheme.pointSmallEtale x).skyscraperPresheaf
      (A := ModuleCat.{u + 1} A) (sum f A x F) where
  app W := Pi.lift (fun v ↦ forwardFamily f A x F W.unop v)
  naturality {W W'} g := by
    apply Pi.hom_ext
    intro v
    simp only [Category.assoc, Pi.lift_π]
    change F.map g ≫ forwardFamily f A x F W'.unop v =
      (Pi.lift fun v ↦ forwardFamily f A x F W.unop v) ≫
        Pi.map' ((Scheme.pointSmallEtale x).fiber.map ((base f).map g.unop))
          (fun _ ↦ 𝟙 _) ≫ Pi.π _ v
    rw [Pi.map'_comp_π, ← Category.assoc, Pi.lift_π, Category.comp_id]
    let z : Over.mk x ⟶ Over.mk f := v ≫ Over.homMk W'.unop.hom
    let w' : (Scheme.pointSmallEtale z.left).fiber.obj W'.unop := Over.homMk v.left
    let w := w' ≫ (Scheme.Etale.forget U).map g.unop
    have hv' : forgetPoint f x z W'.unop w' = v := by apply Over.OverMorphism.ext; rfl
    have hv : forgetPoint f x z W.unop w =
        (Scheme.pointSmallEtale x).fiber.map ((base f).map g.unop) v := by
      apply Over.OverMorphism.ext
      rfl
    rw [← hv, ← hv', forwardFamily_eq, forwardFamily_eq, ← Category.assoc]
    congr 1
    exact (Scheme.pointSmallEtale z.left).toPresheafFiber_w g.unop w' F

-- Descend the germ assignment first through the Kan extension and then through the stalk.
private noncomputable def forward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ⟶ sum f A x F :=
  (Scheme.pointSmallEtale x).skyscraperPresheafHomEquiv.symm
    ((presheaf f A F).descOfIsLeftKanExtension ((base f).op.lanUnit.app F) _
      (forwardTransformation f A x F))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forward_germ (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (W : U.Etale) (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W) v
          (presheaf f A F) ≫ forward f A x F = forwardFamily f A x F W v := by
  unfold forward
  rw [← GrothendieckTopology.Point.skyscraperPresheafHomEquiv_app_π,
    Equiv.apply_symm_apply, ← Category.assoc]
  have h := (presheaf f A F).descOfIsLeftKanExtension_fac_app
    ((base f).op.lanUnit.app F) _ (forwardTransformation f A x F) (op W)
  exact (congrArg (· ≫ Pi.π _ v) h).trans (Pi.lift_π _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def backwardSummand
    (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) (z : Over.mk x ⟶ Over.mk f) :
    ((Scheme.pointSmallEtale z.left).presheafFiber (A := ModuleCat.{u + 1} A)).obj F ⟶
      ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
        (presheaf f A F) :=
  (Scheme.pointSmallEtale z.left).presheafFiberDesc
    (fun W w ↦ ((base f).op.lanUnit.app F).app (op W) ≫
      (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W)
        (forgetPoint f x z W w) (presheaf f A F)) (by
    intro W W' g w
    rw [← Category.assoc, NatTrans.naturality, Category.assoc]
    congr 1
    exact (Scheme.pointSmallEtale x).toPresheafFiber_w
      ((base f).map g) (forgetPoint f x z W w) (presheaf f A F))

private lemma backwardSummand_germ (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) (W : U.Etale)
    (w : (Scheme.pointSmallEtale z.left).fiber.obj W) :
    (Scheme.pointSmallEtale z.left).toPresheafFiber W w F ≫ backwardSummand f A x F z =
      ((base f).op.lanUnit.app F).app (op W) ≫
        (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W)
          (forgetPoint f x z W w) (presheaf f A F) := by
  exact (Scheme.pointSmallEtale z.left).toPresheafFiber_presheafFiberDesc _ _ _ _

open Classical in
private noncomputable def backward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    sum f A x F ⟶
      ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
        (presheaf f A F) :=
  ModuleCat.ofHom (DirectSum.toModule A _ _
    (fun z ↦ (backwardSummand f A x F z).hom))

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma backward_lof (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A)
    (z : Over.mk x ⟶ Over.mk f) :
    ModuleCat.ofHom (DirectSum.lof A _
      (fun z : Over.mk x ⟶ Over.mk f ↦
        ((Scheme.pointSmallEtale z.left).presheafFiber
          (A := ModuleCat.{u + 1} A)).obj F) z) ≫ backward f A x F =
      backwardSummand f A x F z := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  simp only [backward, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply]
  exact DirectSum.toModule_lof A
    (M := fun z : Over.mk x ⟶ Over.mk f ↦
      ((Scheme.pointSmallEtale z.left).presheafFiber
        (A := ModuleCat.{u + 1} A)).obj F)
    (φ := fun z ↦ (backwardSummand f A x F z).hom) z s

open Classical in
private lemma backward_forward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    backward f A x F ≫ forward f A x F = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply DirectSum.linearMap_ext
  intro z
  have hh : backwardSummand f A x F z ≫ forward f A x F =
      ModuleCat.ofHom (DirectSum.lof A _
        (fun z : Over.mk x ⟶ Over.mk f ↦
          ((Scheme.pointSmallEtale z.left).presheafFiber
            (A := ModuleCat.{u + 1} A)).obj F) z) := by
    apply (Scheme.pointSmallEtale z.left).presheafFiber_hom_ext
    intro W w
    rw [← Category.assoc, backwardSummand_germ, Category.assoc, forward_germ,
      forwardFamily_eq]
  have hcat := congrArg (fun h ↦ h ≫ forward f A x F) (backward_lof f A x F z)
  rw [Category.assoc, hh] at hcat
  exact congrArg ModuleCat.Hom.hom hcat

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma forward_backward (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    forward f A x F ≫ backward f A x F = 𝟙 _ := by
  apply hom_ext f A x F
  intro W v
  calc
    _ = (forwardFamily f A x F W v) ≫ backward f A x F := by
      simpa only [Category.assoc] using
        congrArg (· ≫ backward f A x F) (forward_germ f A x F W v)
    _ = _ := by
      dsimp only [forwardFamily]
      rw [Category.assoc, backward_lof]
      have hh := backwardSummand_germ f A x F
        (v ≫ Over.homMk W.hom) W (Over.homMk v.left)
      have hv : forgetPoint f x (v ≫ Over.homMk W.hom) W (Over.homMk v.left) = v := by
        apply Over.OverMorphism.ext
        rfl
      rw [hv] at hh
      exact hh.trans (by simp only [Category.comp_id])

private noncomputable def presheafIso (F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A) :
    ((Scheme.pointSmallEtale x).presheafFiber (A := ModuleCat.{u + 1} A)).obj
      (presheaf f A F) ≅ sum f A x F where
  hom := forward f A x F
  inv := backward f A x F
  hom_inv_id := forward_backward f A x F
  inv_hom_id := backward_forward f A x F

private noncomputable def sumMap {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) : sum f A x F ⟶ sum f A x G :=
  ModuleCat.ofHom (DirectSum.lmap (fun z : Over.mk x ⟶ Over.mk f ↦
    (((Scheme.pointSmallEtale z.left).presheafFiber
      (A := ModuleCat.{u + 1} A)).map α).hom))

private lemma sumMap_lof {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) (z : Over.mk x ⟶ Over.mk f) :
    ModuleCat.ofHom (DirectSum.lof A _
      (fun z : Over.mk x ⟶ Over.mk f ↦
        ((Scheme.pointSmallEtale z.left).presheafFiber
          (A := ModuleCat.{u + 1} A)).obj F) z) ≫ sumMap f A x α =
    ((Scheme.pointSmallEtale z.left).presheafFiber
      (A := ModuleCat.{u + 1} A)).map α ≫
      ModuleCat.ofHom (DirectSum.lof A _
        (fun z : Over.mk x ⟶ Over.mk f ↦
          ((Scheme.pointSmallEtale z.left).presheafFiber
            (A := ModuleCat.{u + 1} A)).obj G) z) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change (DirectSum.lmap (fun z : Over.mk x ⟶ Over.mk f ↦
    (((Scheme.pointSmallEtale z.left).presheafFiber
      (A := ModuleCat.{u + 1} A)).map α).hom)) _ = _
  exact DirectSum.lmap_lof
    (M := fun z : Over.mk x ⟶ Over.mk f ↦
      ((Scheme.pointSmallEtale z.left).presheafFiber
        (A := ModuleCat.{u + 1} A)).obj F)
    (fun z ↦ (((Scheme.pointSmallEtale z.left).presheafFiber
      (A := ModuleCat.{u + 1} A)).map α).hom) z s

private lemma forwardFamily_naturality {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) (W : U.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    α.app (op W) ≫ forwardFamily f A x G W v =
      forwardFamily f A x F W v ≫ sumMap f A x α := by
  unfold forwardFamily
  rw [Category.assoc, sumMap_lof, ← Category.assoc]
  exact congrArg (· ≫ _)
    ((Scheme.pointSmallEtale (v.left ≫ W.hom)).toPresheafFiber_naturality
      α W (Over.homMk v.left)).symm

open Classical in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [Etale f] in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma unit_naturality {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) (W : U.Etale) :
    ((base f).op.lanUnit.app F).app (op W) ≫
        ((base f).op.lan.map α).app (op ((base f).obj W)) =
      α.app (op W) ≫ ((base f).op.lanUnit.app G).app (op W) := by
  exact (NatTrans.congr_app ((base f).op.lanUnit.naturality α) (op W)).symm

private lemma forward_naturality {F G : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} A}
    (α : F ⟶ G) :
    (Scheme.pointSmallEtale x).presheafFiber.map ((base f).op.lan.map α) ≫
        forward f A x G = forward f A x F ≫ sumMap f A x α := by
  apply hom_ext f A x F
  intro W v
  simp only [← Category.assoc]
  rw [Category.assoc _ _ ((Scheme.pointSmallEtale x).presheafFiber.map _),
    (Scheme.pointSmallEtale x).toPresheafFiber_naturality]
  rw [← Category.assoc, unit_naturality]
  simp only [Category.assoc]
  rw [forward_germ, forwardFamily_naturality]
  simpa only [Category.assoc] using
    congrArg (· ≫ sumMap f A x α) (forward_germ f A x F W v).symm

-- Sheafification does not change the fibre of a point.

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def sheafIso
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
      ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).obj F) ≅
        sum f A x F.obj :=
  (asIso ((Scheme.pointSmallEtale x).presheafFiber.map
    (toSheafify X.smallEtaleTopology (presheaf f A F.obj)))).symm ≪≫
      presheafIso f A x F.obj

private lemma sheafIso_unit
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Scheme.pointSmallEtale x).presheafFiber.map
        (toSheafify X.smallEtaleTopology (presheaf f A F.obj)) ≫
      (sheafIso f A x F).hom = forward f A x F.obj := by
  simp only [sheafIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    IsIso.hom_inv_id_assoc, presheafIso]

private lemma sheafIso_naturality
    {F G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)} (α : F ⟶ G) :
    ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).map α) ≫
      (sheafIso f A x G).hom = (sheafIso f A x F).hom ≫ sumMap f A x α.hom := by
  change (Scheme.pointSmallEtale x).presheafFiber.map
    (sheafifyMap X.smallEtaleTopology ((base f).op.lan.map α.hom)) ≫ _ = _
  apply (cancel_epi ((Scheme.pointSmallEtale x).presheafFiber.map
    (toSheafify X.smallEtaleTopology (presheaf f A F.obj)))).mp
  rw [← Category.assoc, ← Functor.map_comp]
  change (Scheme.pointSmallEtale x).presheafFiber.map
    (toSheafify X.smallEtaleTopology (presheaf f A F.obj) ≫
      sheafifyMap X.smallEtaleTopology ((base f).op.lan.map α.hom)) ≫ _ = _
  rw [← toSheafify_naturality, Functor.map_comp, Category.assoc, sheafIso_unit]
  rw [← Category.assoc, sheafIso_unit]
  exact forward_naturality f A x α.hom

private lemma sheafIso_germ
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
    (v : (Scheme.pointSmallEtale x).fiber.obj ((base f).obj W)) :
    ((base f).op.lanUnit.app F.obj).app (op W) ≫
      (toSheafify X.smallEtaleTopology (presheaf f A F.obj)).app (op ((base f).obj W)) ≫
      (Scheme.pointSmallEtale x).toPresheafFiber ((base f).obj W) v
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) f inferInstance).obj F).obj ≫
      (sheafIso f A x F).hom = forwardFamily f A x F.obj W v := by
  have hh := (Scheme.pointSmallEtale x).toPresheafFiber_naturality
    (toSheafify X.smallEtaleTopology (presheaf f A F.obj)) ((base f).obj W) v
  have h := congrArg (fun h ↦ ((base f).op.lanUnit.app F.obj).app (op W) ≫
    h ≫ (sheafIso f A x F).hom) hh.symm
  simp only [Category.assoc] at h
  rw [sheafIso_unit, forward_germ] at h
  exact h

/-- The natural linear stalk isomorphism for étale sum extension, including its formula
on the germ of each summand section. The index `Over.mk x ⟶ Over.mk u` is precisely
all lifts of the fixed geometric point, with the same algebraically closed field.
Source: Stacks Project, Tags 03S5 and 0710 (blueprint: lem-amb-etale-sum-stalks).

Proof: (1) Write P(V) as the direct sum of F(V,a). Its stalk L maps isomorphically to
that of its sheafification by `lem-weil-pbc-sheafification-geometric-stalk` and the
module sheafification construction `def-weil-presheaf-modules-sheafification`.
The unit and its inverse are linear. (2) Send the a-summand at (V,v) to the germ
in the lift a(v). Étale cancellation (`lem-weil-pbc-etale-composition-cancellation`)
and the stalk colimit relations (`def-weil-pbc-geometric-stalks`,
`def-weil-pbc-category-colimit`) make this a compatible cocone, hence a map from L.
(3) Conversely, a neighbourhood over U composes with u to a neighbourhood over X.
Place each section in its structure-map summand of P; these maps respect refinement,
so induce maps from every lift stalk to L, hence from their direct sum.
(4) Both composites are identities on every section germ, hence on stalks by the
colimit universal property and on sums by finite support.
(5) Compose with the inverse sheafification stalk map. This gives the displayed
section formula. Both sides of the naturality square send every section to the
same germ of its image, proving naturality by finite sums and the colimit property.
The sum presheaf throughout is `def-weil-pbc-etale-sum-extension`.
-/
theorem Etale.exists_etaleSumStalksIso
    {U X : Scheme.{u}} (u : U ⟶ X) [Etale u]
    (A : Type (u + 1)) [CommRing A]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ e : ∀ F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
      (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F)) ≃ₗ[A]
      (⨁ (z : Over.mk x ⟶ Over.mk u),
        ((Scheme.pointSmallEtale z.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj F),
      (∀ (F G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (α : F ⟶ G)
        (s : ((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).obj
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F)),
        e G (((Scheme.pointSmallEtale x).sheafFiber (A := ModuleCat.{u + 1} A)).map
          ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).map α) s) =
        DirectSum.lmap (fun z : Over.mk x ⟶ Over.mk u =>
          (((Scheme.pointSmallEtale z.left).sheafFiber
            (A := ModuleCat.{u + 1} A)).map α).hom) (e F s)) ∧
      (∀ (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) (W : U.Etale)
        (v : Over.mk x ⟶ (Scheme.Etale.forget X).obj
          ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W))
        (s : F.obj.obj (op W)),
        e F
          ((Scheme.pointSmallEtale x).toPresheafFiber
            ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W) v
            ((Etale.etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).obj F).obj
            ((toSheafify X.smallEtaleTopology
              ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).op.lan.obj F.obj)).app
                (op ((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).obj W))
              (((MorphismProperty.Over.map ⊤ (inferInstance : Etale u)).op.lanUnit.app
                F.obj).app (op W) s))) =
        DirectSum.lof A
          (Over.mk x ⟶ Over.mk u)
          (fun z : Over.mk x ⟶ Over.mk u =>
            ((Scheme.pointSmallEtale z.left).sheafFiber (A := ModuleCat.{u + 1} A)).obj F)
          (v ≫ Over.homMk W.hom)
          ((Scheme.pointSmallEtale (v.left ≫ W.hom)).toPresheafFiber W
            (Over.homMk v.left) F.obj s)) := by
  classical
  refine ⟨fun F ↦ (Etale.SumStalks.sheafIso u A x F).toLinearEquiv, ?_, ?_⟩
  · intro F G α s
    exact congrArg (fun h ↦ h s) (Etale.SumStalks.sheafIso_naturality u A x α)
  · intro F W v s
    exact congrArg (fun h ↦ h s) (Etale.SumStalks.sheafIso_germ u A x F W v)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
end Etale.SumStalks

open Classical in
end AlgebraicGeometry
