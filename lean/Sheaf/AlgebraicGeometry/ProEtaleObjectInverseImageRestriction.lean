/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N8, U2
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.Pullback
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Inverse image along an object of the small pro-etale site

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; pro-etale functoriality, Tag 09A5
(blueprint: lem-sfb-proetale-object-inverse-image-restriction).

The comparison data below spell out the canonical presheaf coprojections and
sheafification unit. The theorem applies to an arbitrary site object, with no
monomorphism or finiteness hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The distinguished pair `(U → X, (id, str))` in the inverse-image index.
The chosen pullback puts the variable factor first. Its arrow is the unit of
composition left adjoint to base change, hence is exactly the pair of the identity
and the structure map, rather than an arbitrary arrow to the fibre product.
Source: Stacks, Tags 03CE and 00VC
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
noncomputable def proEtaleObjectInverseImageIndexPoint {X : Scheme.{u}} (W : X.ProEt)
    (U : W.left.ProEt) : proEtaleInverseImageIndex W.hom U :=
  StructuredArrow.mk
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit.app U)

/-- Clause (1)'s canonical comparison data for a specified category of values.
`presheafIso` is restriction to the object followed by the presheaf inverse image;
its components are the distinguished coprojections, expressed using the Kan unit.
The final equation identifies the inverse of `sheafIso` with those coprojections
followed by the actual sheafification unit. Both isomorphisms are natural in the
sheaf, and their components are presheaf/sheaf morphisms, hence natural in site objects.
This structure only packages the assertions; it does not choose any comparison.
Source: Stacks, Tags 03CE, 00VC and 00WH
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
structure ProEtaleObjectRestrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] where
  presheafIso :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan
  coprojection : ∀ (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt),
    (presheafIso.hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op
  sheafification_isIso : ∀ G : Sheaf (ProEt.topology X) D,
    IsIso (toSheafify (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj))
  sheafIso : proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D ≅
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop
  sheafIso_inv : ∀ G : Sheaf (ProEt.topology X) D,
    (sheafIso.inv.app G).hom = presheafIso.hom.app G ≫
      toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)

/-- Restriction of constant-coefficient modules through the constant-ring localization
isomorphism `e : A_W ≅ A_X|_W`. This is the existing sectionwise pushforward of
module sheaves along composition; its scalar action uses `e.hom` and its underlying
abelian presheaf is exactly `U ↦ M(U → W → X)`.
Source: Stacks, Tags 00XZ, 0H7J and 03D2
(blueprint: lem-sfb-proetale-object-inverse-image-restriction). -/
noncomputable abbrev proEtaleObjectModuleRestriction {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A)) :=
  letI : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  SheafOfModules.pushforward.{u + 1} (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing W.left A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private noncomputable def restrictionPresheafIso {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D] :
    AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ⋙
        sheafToPresheaf (ProEt.topology W.left) D ≅
      sheafToPresheaf (ProEt.topology X) D ⋙ (proEtaleBaseChange W.hom).op.lan := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom
    W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  exact Functor.isoWhiskerLeft (sheafToPresheaf (ProEt.topology X) D)
    (a.leftAdjointUniq b)

private theorem restrictionPresheafIso_coprojection {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) (U : W.left.ProEt) :
    ((restrictionPresheafIso W D).hom.app G).app (op U) =
      ((proEtaleBaseChange W.hom).op.leftKanExtensionUnit G.obj).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) ≫
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj).map
          (proEtaleObjectInverseImageIndexPoint W U).hom.op := by
  let a := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    W.hom W.prop trivial).op.whiskerLeft D
  let b := (proEtaleBaseChange W.hom).op.lanAdjunction D
  have h : (a.leftAdjointUniq b).hom.app G.obj =
      (a.homEquiv _ _).symm (b.unit.app G.obj) := by
    apply (a.homEquiv _ _).injective
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b G.obj).trans
      (Equiv.apply_symm_apply _ _).symm
  change ((a.leftAdjointUniq b).hom.app G.obj).app (op U) = _
  rw [h, Adjunction.homEquiv_counit]
  simp only [a, b, NatTrans.comp_app, Functor.whiskeringLeft_obj_map,
    Functor.whiskerLeft_app, Adjunction.whiskerLeft_counit_app_app,
    Functor.lanAdjunction_unit]
  rfl

private theorem restrictionLan_isSheaf {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : Sheaf (ProEt.topology X) D) :
    Presheaf.IsSheaf (ProEt.topology W.left)
      (((proEtaleBaseChange W.hom).op.lan).obj G.obj) :=
  (Presheaf.isSheaf_of_iso_iff ((restrictionPresheafIso W D).app G)).mp
    ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).obj G).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def restrictionComparison {X : Scheme.{u}} (W : X.ProEt)
    (D : Type v) [Category.{u + 1} D] [HasColimitsOfSize.{u + 1, u + 1} D]
    [HasWeakSheafify (ProEt.topology W.left) D] :
    ProEtaleObjectRestrictionComparison W D := by
  let p := restrictionPresheafIso W D
  have hq (G : Sheaf (ProEt.topology X) D) :
      IsIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)) :=
    isIso_toSheafify _ (restrictionLan_isSheaf W D G)
  let e : AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop ≅
      proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D :=
    NatIso.ofComponents (fun G ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (p.app G ≪≫ asIso (toSheafify (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).obj G.obj)))) (by
      intro G H f
      apply Sheaf.hom_ext
      change _ ≫ (p.hom.app H ≫ toSheafify _ _) =
        (p.hom.app G ≫ toSheafify _ _) ≫ _
      have hp := p.hom.naturality f
      change ((AlgebraicGeometry.ProEtale.localizationRestriction D W.hom W.prop).map
        f).hom ≫ p.hom.app H = p.hom.app G ≫
          ((proEtaleBaseChange W.hom).op.lan).map f.hom at hp
      rw [← Category.assoc, hp, Category.assoc]
      have hfmap :
          ((proEtaleSheafInverseImage (X := W.left) (Y := X) W.hom D).map f).hom =
          sheafifyMap (ProEt.topology W.left)
            (((proEtaleBaseChange W.hom).op.lan).map f.hom) := by
        rfl
      rw [hfmap]
      rw [Category.assoc]
      congr 1
      exact toSheafify_naturality (ProEt.topology W.left)
        (((proEtaleBaseChange W.hom).op.lan).map f.hom))
  exact
    { presheafIso := p
      coprojection := restrictionPresheafIso_coprojection W D
      sheafification_isIso := hq
      sheafIso := e.symm
      sheafIso_inv := fun _ ↦ rfl }

private noncomputable def restrictionConstantIso {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] :
    proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A) := by
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  have : F.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap W.prop
  have : F.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap W.prop
  exact (F.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
    (ProEt.topology W.left) (ProEt.topology X)).app
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))

private theorem restrictionConstantIso_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] (U : W.left.ProEt) :
    (toSheafify (ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫
      (restrictionConstantIso W A).hom.hom.app (op U) =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) := by
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  have : F.IsContinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap W.prop
  have : F.IsCocontinuous (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isCocontinuous_overMap W.prop
  exact congrArg (fun f ↦ f.app (op U))
    (F.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (ProEt.topology W.left) (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))

private theorem inverseImageAdjunction_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ((proEtaleSheafAdjunction (X := X) (Y := Y) f CommRingCat.{u + 1}).unit.app R).hom =
      (proEtaleBaseChange f).op.lanUnit.app R.obj ≫
        (proEtaleBaseChange f).op.whiskerLeft
          (toSheafify (ProEt.topology X) ((proEtaleBaseChange f).op.lan.obj R.obj)) := by
  change (sheafToPresheaf _ _).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app R) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionCoefficientMap {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A] :
    proEtaleCoefficientInverseImageMap (X := W.left) (Y := X) W.hom A ≫
      (restrictionConstantIso W A).hom =
      (restrictionComparison W CommRingCat.{u + 1}).sheafIso.hom.app
        (proEtaleConstantRing X A) := by
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing W.left A
  let c := restrictionComparison W CommRingCat.{u + 1}
  let e := restrictionConstantIso W A
  let F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop
  let g := proEtaleCoefficientInverseImageMap (X := W.left) (Y := X) W.hom A
  have hg : (proEtaleSheafAdjunction (X := W.left) (Y := X) W.hom CommRingCat.{u + 1}).unit.app R ≫
      (proEtaleSheafDirectImage (X := W.left) (Y := X) W.hom CommRingCat.{u + 1}).map g =
      proEtaleCoefficientDirectImageMap (X := W.left) (Y := X) W.hom A := by
    exact ((proEtaleSheafAdjunction (X := W.left) (Y := X) W.hom
      CommRingCat.{u + 1}).homEquiv R S).apply_symm_apply
      (proEtaleCoefficientDirectImageMap (X := W.left) (Y := X) W.hom A)
  have h : e.hom ≫ c.sheafIso.inv.app R ≫ g = 𝟙 S := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext (ProEt.topology W.left) _ _ S.property
    apply NatTrans.ext
    funext U
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
    rw [← Category.assoc, ← Category.assoc, restrictionConstantIso_unit]
    rw [c.sheafIso_inv]
    dsimp only [NatTrans.comp_app]
    rw [c.coprojection]
    let k := (proEtaleObjectInverseImageIndexPoint W U.unop).hom.op
    have hn := (toSheafify (ProEt.topology W.left)
      ((proEtaleBaseChange W.hom).op.lan.obj R.obj) ≫ g.hom).naturality k
    have hu := congrArg (fun z ↦ z.hom.app (op (F.obj U.unop))) hg
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
    rw [inverseImageAdjunction_unit] at hu
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
    have hρ := ((sheafificationAdjunction (ProEt.topology X) CommRingCat.{u + 1}).homEquiv
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
        ((proEtaleSheafDirectImage (X := W.left) (Y := X) W.hom
          CommRingCat.{u + 1}).obj S)).apply_symm_apply
        (Functor.whiskerLeft (proEtaleBaseChange W.hom).op
          (toSheafify (ProEt.topology W.left)
            ((Functor.const W.left.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))))
    have hρU := congrArg (fun z ↦ z.app (op (F.obj U.unop))) hρ
    rw [Adjunction.homEquiv_unit] at hρU
    dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hρU
    change (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (F.obj U.unop)) ≫
      (((proEtaleBaseChange W.hom).op.lanUnit.app R.obj).app (op (F.obj U.unop)) ≫
        ((proEtaleBaseChange W.hom).op.lan.obj R.obj).map k) ≫
      (toSheafify (ProEt.topology W.left)
        ((proEtaleBaseChange W.hom).op.lan.obj R.obj)).app U ≫ g.hom.app U = _
    dsimp only [NatTrans.comp_app] at hn
    simp only [Category.assoc] at hn hu ⊢
    erw [hn]
    have hu' := congrArg (fun z ↦
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
          (op (F.obj U.unop)) ≫ z ≫ S.obj.map k) hu
    have hρ' := congrArg (fun z ↦ z ≫ S.obj.map k) hρU
    apply Eq.trans (by
      simpa [S, F, proEtaleObjectInverseImageIndexPoint, proEtaleSheafDirectImage,
        AlgebraicGeometry.ProEtale.lowerStar, Category.assoc] using hu')
    apply Eq.trans (by
      simpa [S, F, proEtaleCoefficientDirectImageMap, proEtaleConstantDirectImageMap,
        Category.assoc] using hρ')
    have ht := (toSheafify (ProEt.topology W.left)
      ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality k
    calc
      _ = (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app U := by
          simpa [S, F, proEtaleObjectInverseImageIndexPoint,
            proEtaleConstantRing, constantSheaf] using ht.symm
      _ = _ := (Category.comp_id _).symm
  change g ≫ e.hom = c.sheafIso.hom.app R
  apply (cancel_epi (c.sheafIso.inv.app R)).mp
  apply (cancel_epi e.hom).mp
  have hh := congrArg (fun z ↦ z ≫ e.hom) h
  simp only [Category.assoc] at hh ⊢
  calc
    e.hom ≫ c.sheafIso.inv.app R ≫ g ≫ e.hom = 𝟙 S ≫ e.hom := hh
    _ = e.hom := Category.id_comp _
    _ = e.hom ≫ c.sheafIso.inv.app R ≫ c.sheafIso.hom.app R := by
      rw [c.sheafIso.inv_hom_id_app]
      exact (Category.comp_id _).symm

private theorem coefficientDirect_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] (U : Y.ProEtᵒᵖ) :
    (toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U ≫
      (proEtaleCoefficientDirectImageMap f A).hom.app U =
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        ((proEtaleBaseChange f).op.obj U) := by
  have h := ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
      ((proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (proEtaleConstantRing X A))).apply_symm_apply
      (Functor.whiskerLeft (proEtaleBaseChange f).op
        (toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))))
  exact congrArg (fun z ↦ z.app U) h
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_counit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    Functor.whiskerRight (NatTrans.op
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).counit)
        (proEtaleConstantRing X A).obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom := by
  let T := (proEtaleSheafDirectImage W.hom CommRingCat.{u + 1}).obj
    ((AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
      W.hom W.prop).obj (proEtaleConstantRing X A))
  apply sheafify_hom_ext (ProEt.topology X) _ _ T.property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, coefficientDirect_unit]
  erw [he]
  have h := (toSheafify (ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).counit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficient_restriction_unit {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    e.hom.hom ≫ (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).op.whiskerLeft
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
      Functor.whiskerRight (NatTrans.op
        (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit)
          (proEtaleConstantRing W.left A).obj = 𝟙 _ := by
  apply sheafify_hom_ext (ProEt.topology W.left) _ _ (proEtaleConstantRing W.left A).property
  apply NatTrans.ext
  funext U
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.id_app]
  rw [← Category.assoc, ← Category.assoc, he]
  erw [coefficientDirect_unit]
  have h := (toSheafify (ProEt.topology W.left)
    ((Functor.const W.left.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).naturality
      ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
        W.hom W.prop trivial).unit.app U.unop).op
  simpa [proEtaleConstantRing, constantSheaf, proEtaleBaseChange] using h.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionModulePullback {X : Scheme.{u}} (W : X.ProEt)
    (A : Type u) [CommRing A]
    [IsIso (proEtaleCoefficientInverseImageMap W.hom A)]
    (e : proEtaleConstantRing W.left A ≅
      (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
        W.hom W.prop).obj (proEtaleConstantRing X A))
    (he : ∀ U : W.left.ProEt,
      (toSheafify (ProEt.topology W.left)
        ((Functor.const W.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app
              (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
  let : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  let P := SheafOfModules.pushforward.{u + 1} (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X)
    (S := (sheafCompose (ProEt.topology W.left)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing W.left A))
    (R := (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A))
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
∃ rho : ∀ M : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)),
          proEtaleConstantModulePullback W.hom A M ≅
            P.obj M,
        ∀ (M N : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))
          (a : M ⟶ N),
          proEtaleConstantModulePullbackMap W.hom A a ≫ (rho N).hom =
            (rho M).hom ≫ P.map a := by
  let : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
    ProEt.isContinuous_overMap (V := W.left) (U := X) W.prop
  let : (proEtaleBaseChange W.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology W.left) :=
    ProEt.isContinuous_overPullback W.hom
  let R := proEtaleConstantRing X A
  let S := proEtaleConstantRing W.left A
  let c := asIso (proEtaleCoefficientInverseImageMap W.hom A)
  have hψ : proEtaleRingDirectImageMap W.hom R S c =
      proEtaleCoefficientDirectImageMap W.hom A := by
    exact ((proEtaleSheafAdjunction W.hom CommRingCat.{u + 1}).homEquiv R S).apply_symm_apply
      (proEtaleCoefficientDirectImageMap W.hom A)
  let φ : ((sheafCompose (ProEt.topology W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) ⟶
      ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology W.left) (ProEt.topology X)).obj
        ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) :=
    ⟨Functor.whiskerRight e.hom.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⟶
      ((proEtaleBaseChange W.hom).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology X) (ProEt.topology W.left)).obj
        ((sheafCompose (ProEt.topology W.left)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
    ⟨Functor.whiskerRight (proEtaleCoefficientDirectImageMap W.hom A).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial
  have H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj =
      (proEtaleCoefficientDirectImageMap W.hom A).hom ≫
        (proEtaleBaseChange W.hom).op.whiskerLeft e.hom.hom :=
    coefficient_restriction_counit W A e he
  have H₂ := coefficient_restriction_unit W A e he
  let a := SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj φ ψ
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁)
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂)
  let b := proEtaleRingModuleAdjunction W.hom R S c
  have hD : proEtaleRingModuleDirectImage W.hom R S c =
      SheafOfModules.pushforward.{u + 1} ψ := by
    unfold proEtaleRingModuleDirectImage
    rw [hψ]
  rw [hD] at b
  let i := b.leftAdjointUniq a
  refine ⟨fun M ↦ i.app M, ?_⟩
  intro M N f
  exact i.hom.naturality f

/-- Inverse image along an object is slice restriction, including the canonical
presheaf comparison, the sheafification unit, the particular coefficient map, and
module pullback. The commutative-ring comparison retains the ring structure needed
for coefficients; `RingCat` also includes noncommutative ring sheaves.

Source: Stacks Project, Sites and Sheaves, Tags 03CE, 00VC, 00XZ, 00WH and 0H7J;
Modules on Sites, Tags 03D2 and 03EK; proetale.tex, Tag 09A5
(blueprint: lem-sfb-proetale-object-inverse-image-restriction).

Proof:
1. Composition is left adjoint to base change. Its unit is the distinguished
   index point, and its Hom equivalence proves that this point is initial.
2. On presheaves, restriction and left Kan extension are left adjoints to the
   same precomposition functor. Uniqueness of left adjoints gives their natural
   isomorphism. The Hom-equivalence formula identifies its components with the
   distinguished coprojections. Restriction is a sheaf, so the sheafification
   unit is invertible and gives the normalized sheaf comparison.
3. Continuous cocontinuous restriction commutes with sheafification, giving
   the constant-ring isomorphism e and its constant-section equation. The
   specified coefficient map is adjoint to the constant-section map. Using
   naturality at the distinguished index point and the Kan-unit formula shows
   that e followed by the inverse comparison and this map fixes constant
   sections. Sheafification uniqueness and cancellation give the coefficient
   equation, and hence invertibility of that particular coefficient map.
4. Sheafification uniqueness on constant sections proves the coefficient unit
   and counit equations for the site adjunction. Mathlib's
   SheafOfModules.pushforwardPushforwardAdj then makes sectionwise module
   restriction left adjoint to the specified module direct image. The existing
   proEtaleRingModuleAdjunction makes the tensor-sheafification pullback left
   adjoint to the same direct image. Uniqueness of left adjoints gives the
   module isomorphism and its naturality. -/
theorem proEtaleObjectInverseImageRestriction (X : Scheme.{u}) (W : X.ProEt)
    (A : Type u) [CommRing A] :
    (∀ U : W.left.ProEt,
      Nonempty (IsInitial (proEtaleObjectInverseImageIndexPoint W U))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W (Type (u + 1))) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W AddCommGrpCat.{u + 1}) ∧
    Nonempty (ProEtaleObjectRestrictionComparison W RingCat.{u + 1}) ∧
    ∃ (comparison : ProEtaleObjectRestrictionComparison W CommRingCat.{u + 1})
      (e : proEtaleConstantRing W.left A ≅
        (AlgebraicGeometry.ProEtale.localizationRestriction CommRingCat.{u + 1}
          W.hom W.prop).obj (proEtaleConstantRing X A)),
      (∀ U : W.left.ProEt,
        (toSheafify (ProEt.topology W.left)
          ((Functor.const W.left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} A)))).app (op U) ≫ e.hom.hom.app (op U) =
          (toSheafify (ProEt.topology X)
            ((Functor.const X.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app
                (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) ∧
      proEtaleCoefficientInverseImageMap W.hom A ≫ e.hom =
        comparison.sheafIso.hom.app (proEtaleConstantRing X A) ∧
      ∃ rho : ∀ M : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)),
          proEtaleConstantModulePullback W.hom A M ≅
            (proEtaleObjectModuleRestriction W A e).obj M,
        ∀ (M N : SheafOfModules.{u + 1}
          ((sheafCompose (ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing X A)))
          (a : M ⟶ N),
          proEtaleConstantModulePullbackMap W.hom A a ≫ (rho N).hom =
            (rho M).hom ≫ (proEtaleObjectModuleRestriction W A e).map a := by
  refine ⟨?_, ⟨restrictionComparison W (Type (u + 1))⟩,
    ⟨restrictionComparison W AddCommGrpCat.{u + 1}⟩,
    ⟨restrictionComparison W RingCat.{u + 1}⟩, ?_⟩
  · intro U
    classical
    let adj := (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial)
    let lift : ∀ b : proEtaleInverseImageIndex W.hom U,
        proEtaleObjectInverseImageIndexPoint W U ⟶ b := fun b ↦
      StructuredArrow.homMk ((adj.homEquiv U b.right).symm b.hom) (by
        exact (adj.homEquiv_unit _ _ _).symm.trans
          ((adj.homEquiv U b.right).apply_symm_apply b.hom))
    refine ⟨IsInitial.ofUniqueHom lift (fun b f ↦ ?_)⟩
    apply StructuredArrow.hom_ext
    apply (adj.homEquiv U b.right).injective
    rw [Adjunction.homEquiv_unit]
    exact (StructuredArrow.w f).trans
      ((adj.homEquiv U b.right).apply_symm_apply b.hom).symm
  · have : IsIso (proEtaleCoefficientInverseImageMap W.hom A) := by
      apply (isIso_comp_right_iff (proEtaleCoefficientInverseImageMap W.hom A)
        (restrictionConstantIso W A).hom).mp
      rw [restrictionCoefficientMap W A]
      infer_instance
    refine ⟨restrictionComparison W CommRingCat.{u + 1}, restrictionConstantIso W A,
      restrictionConstantIso_unit W A, restrictionCoefficientMap W A, ?_⟩
    exact restrictionModulePullback W A (restrictionConstantIso W A)
      (restrictionConstantIso_unit W A)

end AlgebraicGeometry.Scheme
