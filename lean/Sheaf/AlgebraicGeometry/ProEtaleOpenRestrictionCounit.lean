/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module
public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
/-! # Open restriction and the direct-image counit.
Source: Stacks Project, pro-etale functoriality (09A5), Sites (00XZ, 03CB, 03CF),
and Modules on Sites (03D3, 04J0)
(blueprint: lem-sfb-proetale-open-restriction-counit).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 2048
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.ProEtaleOpenRestriction

/-- The inverse-image coefficient ring on X. Source: Stacks `proetale.tex`, Tag 09A5
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on W. Source: Stacks `proetale.tex`, Tag 09A5
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RW {Y W : Scheme.{u}} (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage h CommRingCat.{u + 1}).obj R

/-- The inverse-image coefficient ring on the fibre product X_W. Source: Stacks
Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev RXW {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  (proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1}).obj (RX f R)

/-- The type of coefficient comparisons; `coefficientIso` fixes the canonical one.
Source: Stacks
Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev CoeffCmp {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  RW (pullback.snd f h) (RW h R) ≅ RXW f h R

/-- The category of modules over the inverse-image ring on X. Source: Stacks Modules
on Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev ModX {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :=
  proEtaleRingModules X (RX f R)

/-- Direct image along f followed by restriction along h. Source: Stacks Modules on
Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev Left {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules X (RX f R) ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _) ⋙
    proEtaleRingModulePullback h R (RW h R) (Iso.refl _)

/-- Pullback along the fibre-product projection followed by direct image. Source:
Stacks Modules on Sites, Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev Right {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : CoeffCmp f h R) :
    proEtaleRingModules X (RX f R) ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _) ⋙
    proEtaleRingModuleDirectImage (pullback.snd f h) (RW h R) (RXW f h R) c

/-- The composite pullback from Y via X to X_W. Source: Stacks Modules on Sites, Tag 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AlphaL {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules Y R ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback f R (RX f R) (Iso.refl _) ⋙
    proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _)

/-- The composite pullback from Y via W to X_W. Source: Stacks Modules on Sites,
Tag 04J0 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AlphaR {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (c : CoeffCmp f h R) :
    proEtaleRingModules Y R ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback h R (RW h R) (Iso.refl _) ⋙
    proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Pullback along the first fibre-product projection. Source: Stacks Sites, Tag 03CB
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PFst {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules X (RX f R) ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _)

/-- Pullback along the second fibre-product projection. Source: Stacks Sites, Tag 03CB
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PSnd {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : CoeffCmp f h R) :
    proEtaleRingModules W (RW h R) ⥤
      proEtaleRingModules (pullback f h) (RXW f h R) :=
  proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Pullback along the open immersion h. Source: Stacks Sites, Tag 03CB (blueprint:
lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev PH {X Y W : Scheme.{u}} (_f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModules Y R ⥤ proEtaleRingModules W (RW h R) :=
  proEtaleRingModulePullback h R (RW h R) (Iso.refl _)

/-- The module adjunction for f. Source: Stacks Modules on Sites, Tag 03D3
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AdjF {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R (RX f R) (Iso.refl _) ⊣
      proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _) :=
  proEtaleRingModuleAdjunction f R (RX f R) (Iso.refl _)

/-- The module adjunction for the second fibre-product projection. Source: Stacks
Modules on Sites, Tag 03D3 (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable abbrev AdjSnd {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) (c : CoeffCmp f h R) :
    proEtaleRingModulePullback (pullback.snd f h) (RW h R) (RXW f h R) c ⊣
      proEtaleRingModuleDirectImage (pullback.snd f h) (RW h R) (RXW f h R) c :=
  proEtaleRingModuleAdjunction (pullback.snd f h) (RW h R) (RXW f h R) c

/-- Base-change associativity around the cartesian square, with its canonical projections.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def squareSiteIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleBaseChange f ⋙ proEtaleBaseChange (pullback.fst f h) ≅
      proEtaleBaseChange h ⋙ proEtaleBaseChange (pullback.snd f h) :=
  (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
    (pullback.fst f h) f).symm ≪≫
  eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) (pullback.condition (f := f) (g := h))) ≪≫
  MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤) (pullback.snd f h) h

/-- The inverse-image comparison is the mate of the projection-preserving site isomorphism.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def ringSquareIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y) :
    proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.fst f h) CommRingCat.{u + 1} ≅
      proEtaleSheafInverseImage h CommRingCat.{u + 1} ⋙
        proEtaleSheafInverseImage (pullback.snd f h) CommRingCat.{u + 1} :=
  letI := Functor.isContinuous_comp (proEtaleBaseChange h)
    (proEtaleBaseChange (pullback.snd f h)) (ProEt.topology Y) (ProEt.topology W)
      (ProEt.topology (pullback f h))
  ((conjugateIsoEquiv
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1}))
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1}))).symm
    ((Functor.sheafPushforwardContinuousComp' (eFG := squareSiteIso f h)
      CommRingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)
        (ProEt.topology (pullback f h))) ≪≫
      (Functor.sheafPushforwardContinuousComp (proEtaleBaseChange h)
        (proEtaleBaseChange (pullback.snd f h)) CommRingCat.{u + 1}
          (ProEt.topology Y) (ProEt.topology W)
            (ProEt.topology (pullback f h))).symm)).symm

/-- The coefficient comparison is fixed, not an existentially supplied automorphism.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def coefficientIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) : CoeffCmp f h R :=
  (ringSquareIso f h).symm.app R

/-- Composition sends an object over the source of a weakly etale map to the target site.
Source: Stacks Sites, Tag 00XZ (blueprint: lem-sfb-proetale-open-restriction-counit). -/
abbrev objectComposition {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h] : X.ProEt ⥤ Y.ProEt :=
  MorphismProperty.Over.map (f := h) ⊤ (inferInstance : WeaklyEtale h)

/-- The canonical section coprojection, defined using the module unit and the distinguished
index point `(E → Y, (id, str))`. It is the inverse of the open-slice identification.
Source: Stacks Sites, Tags 00VC, 00XZ; Modules on Sites, Tag 03D3
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def objectCoprojection {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : proEtaleRingModules Y R) (E : X.ProEt)
    (s : M.val.obj (op ((objectComposition h).obj E))) :
    ((proEtaleRingModulePullback h R (RW h R) (Iso.refl _)).obj M).val.obj (op E) :=
  ((proEtaleRingModulePullback h R (RW h R) (Iso.refl _)).obj M).val.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial).unit.app E).op
      (((proEtaleRingModuleAdjunction h R (RW h R) (Iso.refl _)).unit.app M).val.app
        (op ((objectComposition h).obj E)) s)

/-- The canonical fibre-product arrow `(E ×[W] X_W → X) → (E ×[Y] X → X)`.
The map is the identity on E and the first projection on X_W; thus it is the specified
fibre-product identification, rather than a freely supplied section equivalence.
Source: Stacks Sites, Tag 03CF (blueprint: lem-sfb-proetale-open-restriction-counit). -/
noncomputable def sectionArrow {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (E : W.ProEt) :
    (objectComposition (pullback.fst f h)).obj
        ((proEtaleBaseChange (pullback.snd f h)).obj E) ⟶
      (proEtaleBaseChange f).obj ((objectComposition h).obj E) :=
  MorphismProperty.Over.homMk
    (pullback.map E.hom (pullback.snd f h) (E.hom ≫ h) f
      (𝟙 E.left) (pullback.fst f h) h (Category.id_comp _).symm (pullback.condition ..).symm)
    (pullback.lift_snd _ _ _)

/-- The sectionwise assertion with both canonical open-slice identifications explicit.
Bijectivity asserts these are identifications; the final equation fixes beta as pullback
along the displayed fibre-product arrow on every section, for every module and object.
Source: Stacks Sites, Tag 03CF; Modules on Sites, Tag 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
def Sectionwise {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (β : Left f h R ≅ Right f h R (coefficientIso f h R)) : Prop :=
  (∀ (M : proEtaleRingModules Y R) (E : W.ProEt),
    Function.Bijective (objectCoprojection h R M E)) ∧
  (∀ (M : ModX f R) (E : (pullback f h).ProEt),
    Function.Bijective (objectCoprojection (pullback.fst f h) (RX f R) M E)) ∧
  ∀ (M : ModX f R) (E : W.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj ((objectComposition h).obj E)))),
    (β.hom.app M).val.app (op E)
        (objectCoprojection h R
          ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) E s) =
      objectCoprojection (pullback.fst f h) (RX f R) M
        ((proEtaleBaseChange (pullback.snd f h)).obj E)
          (M.val.map (sectionArrow f h E).op s)

/-- Unit normalization uniquely fixes the inverse-image comparison alpha. The two iterated
units at V agree after alpha and the canonical site square. This excludes twists by an
arbitrary natural automorphism and is exactly adjunction-compatible composition.
Source: Stacks Sites, Tag 03CB (blueprint: lem-sfb-proetale-open-restriction-counit). -/
def AlphaNormalization {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) : Prop :=
  ∀ (F : proEtaleRingModules Y R) (V : Y.ProEt) (m : F.val.obj (op V)),
    (α.hom.app F).val.app
        (op ((proEtaleBaseChange (pullback.fst f h)).obj ((proEtaleBaseChange f).obj V)))
      (((AdjF (pullback.fst f h) (RX f R)).unit.app
        ((proEtaleRingModulePullback f R (RX f R) (Iso.refl _)).obj F)).val.app
          (op ((proEtaleBaseChange f).obj V)) (((AdjF f R).unit.app F).val.app (op V) m)) =
    ((AlphaR f h R (coefficientIso f h R)).obj F).val.map
      ((squareSiteIso f h).hom.app V).op
        (((AdjSnd f h R (coefficientIso f h R)).unit.app ((PH f h R).obj F)).val.app
          (op ((proEtaleBaseChange h).obj V))
            (((AdjF h R).unit.app F).val.app (op V) m))

/-- The counit equality as an equality of actual module-sheaf morphisms on X_W.
Source: Stacks Modules on Sites, Tags 03D3 and 04J0
(blueprint: lem-sfb-proetale-open-restriction-counit). -/
def CounitEquation {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (β : Left f h R ≅ Right f h R (coefficientIso f h R))
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) : Prop :=
  ∀ M : ModX f R,
    (PFst f h R).map ((AdjF f R).counit.app M) =
      (α.hom.app ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M)) ≫
        (PSnd f h R (coefficientIso f h R)).map (β.hom.app M) ≫
        (AdjSnd f h R (coefficientIso f h R)).counit.app ((PFst f h R).obj M)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coprojection_bijective {X Y : Scheme.{u}} (h : X ⟶ Y) [WeaklyEtale h]
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (M : proEtaleRingModules Y R) (E : X.ProEt) :
    Function.Bijective (objectCoprojection h R M E) := by
  let G := objectComposition h
  let : G.IsContinuous (ProEt.topology X) (ProEt.topology Y) :=
    ProEt.isContinuous_overMap (inferInstance : WeaklyEtale h)
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{u + 1})
    (ProEt.topology X) (ProEt.topology Y)
  let c₀ := ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).leftAdjointUniq b).app R
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (RW h R)
  let c : B ≅ (G.sheafPushforwardContinuous RingCat.{u + 1}
      (ProEt.topology X) (ProEt.topology Y)).obj A :=
    (sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c₀
  let ψ : A ⟶ ((proEtaleBaseChange h).sheafPushforwardContinuous
      RingCat.{u + 1} (ProEt.topology Y) (ProEt.topology X)).obj B :=
    ⟨Functor.whiskerRight
      ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit) A.obj =
      ψ.hom ≫ (proEtaleBaseChange h).op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext V
    have hc := Adjunction.unit_leftAdjointUniq_hom_app
      (proEtaleSheafAdjunction h CommRingCat.{u + 1}) b R
    exact congrArg (fun f ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (f.hom.app V)) hc.symm
  have H₂ : c.hom.hom ≫ G.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) B.obj = 𝟙 B.obj := by
    apply NatTrans.ext
    funext V
    apply (cancel_mono (c.hom.hom.app V)).mp
    dsimp
    rw [Category.id_comp]
    have hn := c.hom.hom.naturality (a.unit.app V.unop).op
    dsimp at hn
    rw [Category.assoc, Category.assoc, hn]
    have hh := congrArg (fun t ↦ t.app (G.op.obj V)) H₁
    dsimp at hh
    erw [← Category.assoc (ψ.hom.app (G.op.obj V))
      (c.hom.hom.app ((proEtaleBaseChange h).op.obj (G.op.obj V)))
      (A.obj.map (G.map (a.unit.app V.unop)).op), ← hh]
    rw [← Functor.map_comp, ← op_comp]
    erw [a.left_triangle_components]
    change c.hom.hom.app V ≫ A.obj.map (𝟙 (G.op.obj V)) = c.hom.hom.app V
    rw [A.obj.map_id]
    exact Category.comp_id (c.hom.hom.app V)
  let d := SheafOfModules.pushforwardPushforwardAdj a c.hom ψ H₁ H₂
  let d' : SheafOfModules.pushforward.{u + 1} c.hom ⊣
      proEtaleRingModuleDirectImage h R (RW h R) (Iso.refl _) :=
    d.ofNatIsoRight (SheafOfModules.pushforwardCongr (by
      simp [ψ, proEtaleRingDirectImageMap]))
  let e := d'.leftAdjointUniq (proEtaleRingModuleAdjunction h R (RW h R) (Iso.refl _))
  have he : ∀ s, (e.hom.app M).val.app (op E) s = objectCoprojection h R M E s := by
    intro s
    have hx := d'.homEquiv_leftAdjointUniq_hom_app
      (proEtaleRingModuleAdjunction h R (RW h R) (Iso.refl _)) M
    have hy := (d'.homEquiv M _).symm_apply_apply (e.hom.app M)
    rw [show d'.homEquiv M _ (e.hom.app M) =
      (proEtaleRingModuleAdjunction h R (RW h R) (Iso.refl _)).unit.app M from hx] at hy
    have hz := congrArg (fun z ↦ z.val.app (op E) s) hy
    exact hz.symm
  let eE := (SheafOfModules.evaluation B (op E)).mapIso (e.app M)
  have hb := ConcreteCategory.bijective_of_isIso eE.hom
  change Function.Bijective (fun s ↦ (e.hom.app M).val.app (op E) s) at hb
  simpa only [he] using hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalized_alpha {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R),
      AlphaNormalization f h R α := by
  let F := proEtaleBaseChange f
  let G := proEtaleBaseChange (pullback.fst f h)
  let H := proEtaleBaseChange h
  let K := proEtaleBaseChange (pullback.snd f h)
  let JY := ProEt.topology Y
  let JX := ProEt.topology X
  let JW := ProEt.topology W
  let JP := ProEt.topology (pullback f h)
  let : (F ⋙ G).IsContinuous JY JP := Functor.isContinuous_comp F G JY JX JP
  let : (H ⋙ K).IsContinuous JY JP := Functor.isContinuous_comp H K JY JW JP
  let A := (sheafCompose JY (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose JX (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (RX f R)
  let C := (sheafCompose JW (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (RW h R)
  let D := (sheafCompose JP (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (RXW f h R)
  let φf : A ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} JY JX).obj B :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap f R (RX f R) (Iso.refl _)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let φg : B ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} JX JP).obj D :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (pullback.fst f h) (RX f R) (RXW f h R) (Iso.refl _)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let φh : A ⟶ (H.sheafPushforwardContinuous RingCat.{u + 1} JY JW).obj C :=
    ⟨Functor.whiskerRight (proEtaleRingDirectImageMap h R (RW h R) (Iso.refl _)).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let φk : C ⟶ (K.sheafPushforwardContinuous RingCat.{u + 1} JW JP).obj D :=
    ⟨Functor.whiskerRight
      (proEtaleRingDirectImageMap (pullback.snd f h) (RW h R) (RXW f h R)
        (coefficientIso f h R)).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let φL : A ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u + 1} JY JP).obj D :=
    φf ≫ (F.sheafPushforwardContinuous RingCat.{u + 1} JY JX).map φg
  let φR : A ⟶ ((H ⋙ K).sheafPushforwardContinuous RingCat.{u + 1} JY JP).obj D :=
    φh ≫ (H.sheafPushforwardContinuous RingCat.{u + 1} JY JW).map φk
  let t := (Functor.sheafPushforwardContinuousComp' (eFG := squareSiteIso f h)
      CommRingCat.{u + 1} JY JX JP) ≪≫
    (Functor.sheafPushforwardContinuousComp H K CommRingCat.{u + 1} JY JW JP).symm
  have hc := unit_conjugateEquiv_symm
    ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1}))
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1})) t.hom R
  change ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1})).unit.app R ≫
      t.hom.app (RXW f h R) =
    ((proEtaleSheafAdjunction h CommRingCat.{u + 1}).comp
      (proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1})).unit.app R ≫
      (proEtaleSheafDirectImage (pullback.snd f h) CommRingCat.{u + 1} ⋙
        proEtaleSheafDirectImage h CommRingCat.{u + 1}).map (coefficientIso f h R).hom at hc
  have hh : φL ≫ (Functor.sheafPushforwardContinuousNatTrans
      (squareSiteIso f h).inv RingCat.{u + 1} JY JP).app D = φR := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    have hv := congrArg (fun z ↦ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (z.hom.app V)) hc
    change (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
      (((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app V) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (((proEtaleSheafAdjunction (pullback.fst f h) CommRingCat.{u + 1}).unit.app
          (RX f R)).hom.app (op (F.obj V.unop))) ≫
      D.obj.map ((squareSiteIso f h).inv.app V.unop).op =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (((proEtaleSheafAdjunction h CommRingCat.{u + 1}).unit.app R).hom.app V) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        (((proEtaleSheafAdjunction (pullback.snd f h) CommRingCat.{u + 1}).unit.app
          (RW h R)).hom.app (op (H.obj V.unop))) ≫
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((coefficientIso f h R).hom.hom.app (op (K.obj (H.obj V.unop))))
    simp only [Adjunction.comp_unit_app] at hv
    dsimp [t, Functor.sheafPushforwardContinuousComp',
      Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousNatTrans] at hv
    dsimp [Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans] at hv
    dsimp [proEtaleSheafDirectImage, AlgebraicGeometry.ProEtale.lowerStar,
      Functor.sheafPushforwardContinuous] at hv
    simp only [Functor.map_comp, Category.assoc] at hv
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at hv
    exact hv
  let d := (SheafOfModules.pushforwardComp φf φg) ≪≫
    (SheafOfModules.pushforwardCongr₂ (φ := φL) (squareSiteIso f h).symm hh) ≪≫
      (SheafOfModules.pushforwardComp φh φk).symm
  let aL := (AdjF f R).comp (AdjF (pullback.fst f h) (RX f R))
  let aR := (AdjF h R).comp (AdjSnd f h R (coefficientIso f h R))
  let α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R) :=
    ((conjugateIsoEquiv aL aR).symm d).symm
  refine ⟨α, ?_⟩
  intro M V m
  have hx := unit_conjugateEquiv_symm aR aL d.inv M
  have hy := congrArg (fun z ↦ z.val.app (op V) m) hx
  dsimp only [aL, aR, Adjunction.comp_unit_app] at hy
  exact hy.symm

private noncomputable def betaMate {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) :
    Left f h R ⟶ Right f h R (coefficientIso f h R) :=
  (mateEquiv (AdjF f R) (AdjSnd f h R (coefficientIso f h R))
    (TwoSquare.mk (PH f h R) _ _ (PFst f h R) α.inv)).natTrans

private theorem betaMate_counit {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R)) (M : ModX f R) :
    (PFst f h R).map ((AdjF f R).counit.app M) =
      α.hom.app ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) ≫
        (PSnd f h R (coefficientIso f h R)).map ((betaMate f h R α).app M) ≫
        (AdjSnd f h R (coefficientIso f h R)).counit.app ((PFst f h R).obj M) := by
  dsimp only [betaMate]
  rw [mateEquiv_counit (AdjF f R) (AdjSnd f h R (coefficientIso f h R))
    (TwoSquare.mk (PH f h R) _ _ (PFst f h R) α.inv) M]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem betaMate_on_unit {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R))
    (hn : AlphaNormalization f h R α) (M : ModX f R) (V : Y.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj V))) :
    ((betaMate f h R α).app M).val.app (op ((proEtaleBaseChange h).obj V))
        (((AdjF h R).unit.app
          ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M)).val.app
            (op V) s) =
      ((PFst f h R).obj M).val.map ((squareSiteIso f h).inv.app V).op
        (((AdjF (pullback.fst f h) (RX f R)).unit.app M).val.app
          (op ((proEtaleBaseChange f).obj V)) s) := by
  let N := (proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M
  let c := (squareSiteIso f h).app V
  let P := (PFst f h R).obj M
  let Q := (AlphaL f h R).obj N
  let T := (AlphaR f h R (coefficientIso f h R)).obj N
  let t : Q.val.obj (op ((proEtaleBaseChange (pullback.fst f h)).obj
      ((proEtaleBaseChange f).obj V))) := (((AdjF (pullback.fst f h) (RX f R)).unit.app
    ((proEtaleRingModulePullback f R (RX f R) (Iso.refl _)).obj N)).val.app
      (op ((proEtaleBaseChange f).obj V)) (((AdjF f R).unit.app N).val.app (op V) s))
  let z : T.val.obj (op ((proEtaleBaseChange (pullback.snd f h)).obj
      ((proEtaleBaseChange h).obj V))) :=
    ((AdjSnd f h R (coefficientIso f h R)).unit.app ((PH f h R).obj N)).val.app
    (op ((proEtaleBaseChange h).obj V)) (((AdjF h R).unit.app N).val.app (op V) s)
  have hz : (α.hom.app N).val.app (op ((proEtaleBaseChange (pullback.fst f h)).obj
      ((proEtaleBaseChange f).obj V))) t = T.val.map c.hom.op z :=
    hn N V s
  have ha : (α.inv.app N).val.app (op ((proEtaleBaseChange (pullback.snd f h)).obj
      ((proEtaleBaseChange h).obj V))) z = Q.val.map c.inv.op t := by
    have hs : T.val.map c.inv.op (T.val.map c.hom.op z) = z := by
      change (T.val.presheaf.map c.hom.op ≫ T.val.presheaf.map c.inv.op) z = z
      have hi := congrArg (fun a ↦ T.val.presheaf.map a) (congrArg Quiver.Hom.op c.inv_hom_id)
      exact congrArg (fun a ↦ a z)
        ((T.val.presheaf.map_comp c.hom.op c.inv.op).symm.trans
          (hi.trans (T.val.presheaf.map_id _)))
    have hh := (congrArg (fun x ↦ T.val.map c.inv.op x) hz).trans hs
    have hm := (PresheafOfModules.naturality_apply (α.hom.app N).val c.inv.op t).trans hh
    calc
      _ = (α.inv.app N).val.app _ ((α.hom.app N).val.app _
          (Q.val.map c.inv.op t)) := congrArg (fun x ↦ (α.inv.app N).val.app _ x) hm.symm
      _ = _ := congrArg (fun a ↦ a.val.app _ (Q.val.map c.inv.op t))
        (α.hom_inv_id_app N)
  change (((PFst f h R).map ((AdjF f R).counit.app M)).val.app
    (op ((proEtaleBaseChange (pullback.snd f h)).obj
      ((proEtaleBaseChange h).obj V))))
        ((α.inv.app N).val.app _ z) = _
  rw [ha]
  refine (PresheafOfModules.naturality_apply
    ((PFst f h R).map ((AdjF f R).counit.app M)).val c.inv.op t).trans ?_
  apply congrArg (fun x ↦ P.val.map c.inv.op x)
  have hg := (AdjF (pullback.fst f h) (RX f R)).unit.naturality
    ((AdjF f R).counit.app M)
  have hge := congrArg (fun a ↦ a.val.app (op ((proEtaleBaseChange f).obj V))
    (((AdjF f R).unit.app N).val.app (op V) s)) hg
  dsimp only [t]
  refine hge.symm.trans ?_
  have hf := congrArg (fun a ↦ a.val.app (op V) s)
    ((AdjF f R).right_triangle_components M)
  change ((AdjF f R).counit.app M).val.app (op ((proEtaleBaseChange f).obj V))
    (((AdjF f R).unit.app _).val.app (op V) s) = s at hf
  exact congrArg (fun x ↦ ((AdjF (pullback.fst f h) (RX f R)).unit.app M).val.app
    (op ((proEtaleBaseChange f).obj V)) x) hf

set_option backward.defeqAttrib.useBackward true in
private theorem pullback_eqToIso {A B : Scheme.{u}} {i j : A ⟶ B} (e : i = j) :
    eqToIso (congrArg (fun k ↦ proEtaleBaseChange k) e) =
      MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) e := by
  subst e
  apply Iso.ext
  apply NatTrans.ext
  funext V
  apply MorphismProperty.Over.Hom.ext
  simp [MorphismProperty.Over.pullbackCongr, proEtaleBaseChange]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem betaMate_section {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R))
    (hn : AlphaNormalization f h R α) (M : ModX f R) (E : W.ProEt)
    (s : M.val.obj (op ((proEtaleBaseChange f).obj ((objectComposition h).obj E)))) :
    ((betaMate f h R α).app M).val.app (op E)
        (objectCoprojection h R
          ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) E s) =
      objectCoprojection (pullback.fst f h) (RX f R) M
        ((proEtaleBaseChange (pullback.snd f h)).obj E)
          (M.val.map (sectionArrow f h E).op s) := by
  let V := (objectComposition h).obj E
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ h inferInstance trivial
  let b := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤
    (pullback.fst f h) inferInstance trivial
  let K := proEtaleBaseChange (pullback.snd f h)
  let G := proEtaleBaseChange (pullback.fst f h)
  have hk : K.map (a.unit.app E) ≫ (squareSiteIso f h).inv.app V =
      b.unit.app (K.obj E) ≫ G.map (sectionArrow f h E) := by
    apply MorphismProperty.Over.Hom.ext
    change (K.map (a.unit.app E)).left ≫ ((squareSiteIso f h).inv.app V).left =
      (b.unit.app (K.obj E)).left ≫ (G.map (sectionArrow f h E)).left
    dsimp only [squareSiteIso]
    rw [pullback_eqToIso (pullback.condition (f := f) (g := h))]
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
    erw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    dsimp [a, b, K, G, V, sectionArrow, proEtaleBaseChange,
      MorphismProperty.Over.pullbackComp, MorphismProperty.Over.pullbackCongr,
      MorphismProperty.Over.isoMk, MorphismProperty.Comma.isoMk,
      MorphismProperty.Comma.homFromCommaOfIsIso, MorphismProperty.Over.pullback,
      objectComposition, MorphismProperty.Over.map, MorphismProperty.Comma.Hom.comp,
      MorphismProperty.Comma.mapRight, MorphismProperty.Over.mk,
      MorphismProperty.Comma.isoFromComma, MorphismProperty.Over.homMk, Comma.isoMk]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [Category.assoc]
    · simp [Category.assoc]
  dsimp only [objectCoprojection]
  erw [PresheafOfModules.naturality_apply]
  change ((PFst f h R).obj M).val.map (K.map (a.unit.app E)).op
    (((betaMate f h R α).app M).val.app (op ((proEtaleBaseChange h).obj V))
      (((AdjF h R).unit.app _).val.app (op V) s)) = _
  rw [betaMate_on_unit f h R α hn]
  erw [← PresheafOfModules.map_comp_apply, ← op_comp, hk, op_comp,
    PresheafOfModules.map_comp_apply]
  congr 1
  exact (PresheafOfModules.naturality_apply
    ((AdjF (pullback.fst f h) (RX f R)).unit.app M).val (sectionArrow f h E).op s).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionArrow_isIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (E : W.ProEt) : IsIso (sectionArrow f h E) := by
  let i : pullback (E.hom ≫ h) f ⟶ pullback E.hom (pullback.snd f h) :=
    pullback.lift (pullback.fst _ _)
      (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ E.hom)
        (by simpa only [Category.assoc] using (pullback.condition (f := E.hom ≫ h)
          (g := f)).symm))
      (by simp)
  let e : pullback E.hom (pullback.snd f h) ≅ pullback (E.hom ≫ h) f :=
    { hom := (sectionArrow f h E).left
      inv := i
      hom_inv_id := by
        apply pullback.hom_ext
        · simp [sectionArrow, i]
        · apply pullback.hom_ext <;> simp [sectionArrow, i, pullback.condition]
      inv_hom_id := by
        apply pullback.hom_ext <;> simp [sectionArrow, i] }
  let e' : (objectComposition (pullback.fst f h)).obj
      ((proEtaleBaseChange (pullback.snd f h)).obj E) ≅
      (proEtaleBaseChange f).obj ((objectComposition h).obj E) :=
    MorphismProperty.Over.isoMk (Q := ⊤) e
    (by change (sectionArrow f h E).left ≫ pullback.snd (E.hom ≫ h) f = _
        simp [sectionArrow])
  change IsIso e'.hom
  infer_instance

private theorem moduleMap_isIso_of_bijective
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Sheaf J RingCat.{u + 1}} {M N : SheafOfModules.{u + 1} A}
    (z : M ⟶ N) (hz : ∀ E, Function.Bijective (z.val.app E)) : IsIso z := by
  have hzi (E) : IsIso (z.val.app E) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (hz E)
  let e : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun E ↦ asIso (z.val.app E)) (by intro U V g; exact z.val.naturality g)
  have : IsIso z.val := show IsIso e.hom from inferInstance
  have : IsIso ((SheafOfModules.forget A).map z) := ‹IsIso z.val›
  exact isIso_of_reflects_iso z (SheafOfModules.forget A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem betaMate_isIso {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R))
    (hn : AlphaNormalization f h R α) (M : ModX f R) :
    IsIso ((betaMate f h R α).app M) := by
  apply moduleMap_isIso_of_bijective
  intro E
  let Z := E.unop
  have : IsIso (sectionArrow f h Z) := sectionArrow_isIso f h Z
  have hs := ConcreteCategory.bijective_of_isIso
    (M.val.presheaf.map (sectionArrow f h Z).op)
  have hg := coprojection_bijective (pullback.fst f h) (RX f R) M
    ((proEtaleBaseChange (pullback.snd f h)).obj Z)
  have hh := coprojection_bijective h R
    ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) Z
  have hb : Function.Bijective
      (fun s ↦ ((betaMate f h R α).app M).val.app E
        (objectCoprojection h R
          ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) Z s)) := by
    change Function.Bijective (fun s ↦ ((betaMate f h R α).app M).val.app (op Z)
      (objectCoprojection h R
        ((proEtaleRingModuleDirectImage f R (RX f R) (Iso.refl _)).obj M) Z s))
    simp_rw [betaMate_section f h R α hn]
    exact hg.comp hs
  constructor
  · intro x y hxy
    obtain ⟨a, rfl⟩ := hh.2 x
    obtain ⟨b, rfl⟩ := hh.2 y
    exact congrArg _ (hb.1 hxy)
  · intro y
    obtain ⟨a, ha⟩ := hb.2 y
    exact ⟨_, ha⟩

/--
The canonical open restriction comparison, its sectionwise fibre-product formula, and
its counit mate equation (blueprint: lem-sfb-proetale-open-restriction-counit).

For a weakly etale map, the site adjunction between object composition and base change
induces a sheaf adjunction. Uniqueness of left adjoints identifies its coefficient ring
with the actual inverse-image ring. The unit equation supplies the two coefficient
identities needed by `SheafOfModules.pushforwardPushforwardAdj`. Comparing this
adjunction with the canonical module adjunction identifies its comparison on sections
with `objectCoprojection`; hence that coprojection is bijective.

The canonical site-square isomorphism gives a comparison of the two composite module
direct images. Conjugating by their canonical adjunctions produces alpha, and the
conjugate unit equation gives `AlphaNormalization`. Define beta as the mate of alpha
inverse. The mate counit identity immediately gives `CounitEquation`.

Unit normalization and the right triangle identity compute beta on unit sections.
Naturality then gives its formula on object coprojections: the two intervening arrows
are equal by the fibre-product universal property, so beta acts by `sectionArrow`.
An explicit inverse built from two pullback lifts proves that arrow invertible.
Its action on sections and both object coprojections are therefore bijective; the
section formula makes every component of beta bijective. The module-sheaf forgetful
functor reflects isomorphisms, giving the required natural isomorphism and
`Sectionwise`.

Source: Stacks Project `proetale.tex`, Tag 09A5; Sites Tags 00XZ, 03CB and 03CF;
Modules on Sites Tags 03D3 and 04J0. The formal proof uses Mathlib's uniqueness,
composition, conjugation and mate APIs for the actual pro-etale adjunctions.
-/
theorem proEtaleOpenRestrictionCounit {X Y W : Scheme.{u}} (f : X ⟶ Y) (h : W ⟶ Y)
    [IsOpenImmersion h] (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    ∃ β : Left f h R ≅ Right f h R (coefficientIso f h R),
      Sectionwise f h R β ∧
      ∃ α : AlphaL f h R ≅ AlphaR f h R (coefficientIso f h R),
        AlphaNormalization f h R α ∧ CounitEquation f h R β α := by
  obtain ⟨α, hn⟩ := normalized_alpha f h R
  have hi (M : ModX f R) : IsIso ((betaMate f h R α).app M) :=
    betaMate_isIso f h R α hn M
  let β : Left f h R ≅ Right f h R (coefficientIso f h R) :=
    NatIso.ofComponents (fun M ↦ asIso ((betaMate f h R α).app M))
      (fun a ↦ (betaMate f h R α).naturality a)
  refine ⟨β, ⟨?_, ?_, ?_⟩, α, hn, ?_⟩
  · exact fun M E ↦ coprojection_bijective h R M E
  · exact fun M E ↦ coprojection_bijective (pullback.fst f h) (RX f R) M E
  · exact fun M E s ↦ betaMate_section f h R α hn M E s
  · exact fun M ↦ betaMate_counit f h R α M

end AlgebraicGeometry.Scheme.ProEtaleOpenRestriction
