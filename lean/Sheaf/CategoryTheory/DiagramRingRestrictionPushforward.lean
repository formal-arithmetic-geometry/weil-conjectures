/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q07
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Sheaf.CategoryTheory.DiagramSiteSheafEquivalence
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Coefficient restriction and direct image on derived diagram topoi

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition, applied on the small diagram sites
(blueprint: lem-pur-diagram-ring-restriction-pushforward).

Ring diagrams are represented by ring sheaves on `diagramSiteTopology J C K`.
Their module sheaves have precisely the semilinear horizontal transition maps.
The helpers below transport the componentwise geometric adjunction to those sites.
The final equation characterizes the comparison through the common composite:
its two sides are the two derived composition units, after termwise scalar restriction.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

/-- Componentwise inverse image, transported to the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; the product-site realization
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientInverse
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (F : Sheaf L (Type u) ⥤ Sheaf K (Type u)) :=
  ((diagramSiteSheafEquivalence J D L).functor ⋙
    (Functor.whiskeringRight J _ _).obj F) ⋙ (diagramSiteSheafEquivalence J C K).inverse

/-- Componentwise direct image, transported to the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; the product-site realization
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientDirect
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (G : Sheaf K (Type u) ⥤ Sheaf L (Type u)) :=
  (diagramSiteSheafEquivalence J C K).functor ⋙
    ((Functor.whiskeringRight J _ _).obj G ⋙ (diagramSiteSheafEquivalence J D L).inverse)

/-- The componentwise geometric adjunction on the diagram sites.
Source: Stacks Project, Sites, Tag 00XA; componentwise adjunction and site equivalence
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
def diagramCoefficientAdjunction
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    {F : Sheaf L (Type u) ⥤ Sheaf K (Type u)}
    {G : Sheaf K (Type u) ⥤ Sheaf L (Type u)} (adj : F ⊣ G) :
    diagramCoefficientInverse J C D K L F ⊣ diagramCoefficientDirect J C D K L G :=
  ((diagramSiteSheafEquivalence J D L).toAdjunction.comp
    (adj.whiskerRight J)).comp (diagramSiteSheafEquivalence J C K).symm.toAdjunction

/-- Forget module structure to the underlying sheaf of sets on a diagram site.
This is only the composite of the existing forgetful functors.
Source: Stacks Project, Modules on Sites, Tag 03DA
(blueprint: lem-pur-diagram-ring-restriction-pushforward). -/
noncomputable abbrev diagramCoefficientUnderlying
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u}) :=
  SheafOfModules.toSheaf.{u} R ⋙ sheafCompose K (forget AddCommGrpCat)


section

set_option backward.isDefEq.respectTransparency false

-- Cache standard sheaf instances once: their repeated search dominates elaboration.
private theorem coefficientRingCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget RingCat.{u}) := inferInstance

private theorem coefficientAddCompose
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.HasSheafCompose (forget AddCommGrpCat.{u}) := inferInstance

private theorem coefficientSheafify
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    HasSheafify K AddCommGrpCat.{u} := inferInstance

private theorem coefficientLocallyBijective
    {C : Type u} [SmallCategory C] (K : GrothendieckTopology C) :
    K.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance

attribute [local instance] coefficientRingCompose coefficientAddCompose coefficientSheafify
  coefficientLocallyBijective

private noncomputable def linearOperation
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R : Sheaf K RingCat.{u}} (M : ringedSiteModules.{u} R)
    (T : Sheaf K (Type u))
    (a : T ⟶ (sheafCompose K (forget RingCat)).obj R)
    (x y : T ⟶ (diagramCoefficientUnderlying R).obj M) :
    T ⟶ (diagramCoefficientUnderlying R).obj M :=
  ⟨{ app := fun U ↦ ↾(fun t ↦ (a.hom.app U t) •
        (show M.val.obj U from x.hom.app U t) + (show M.val.obj U from y.hom.app U t))
     naturality := by
       intro U V f
       ext t
       have ha := CategoryTheory.congr_fun (a.hom.naturality f) t
       have hx := CategoryTheory.congr_fun (x.hom.naturality f) t
       have hy := CategoryTheory.congr_fun (y.hom.naturality f) t
       change _ = M.val.map f (_ + _)
       rw [(M.val.map f).hom.map_add, M.val.map_smul]
       change a.hom.app V (T.obj.map f t) = (R.obj.map f).hom (a.hom.app U t) at ha
       change x.hom.app V (T.obj.map f t) = M.val.map f (x.hom.app U t) at hx
       change y.hom.app V (T.obj.map f t) = M.val.map f (y.hom.app U t) at hy
       exact congrArg₂ (fun (v w : M.val.obj V) ↦ v + w)
         (congrArg₂ (fun (r : R.obj.obj V) (z : M.val.obj V) ↦ r • z) ha hx) hy }⟩

private theorem ordinaryCoefficientComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {AX BX : Sheaf K RingCat.{u}} {AY BY : Sheaf L RingCat.{u}}
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (f : RingedToposMorphism BX BY) (g : RingedToposMorphism AX AY)
    (hInv : f.inverse = g.inverse) (hDir : f.direct = g.direct)
    (hAdj : HEq f.adj g.adj)
    (hRing : f.inverse.map ((sheafCompose L (forget RingCat)).map aY) ≫ f.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose L (forget RingCat)).obj AY)) hInv) ≫
        g.ringMap ≫ (sheafCompose K (forget RingCat)).map aX) :
    ∃ c : f.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
        SheafOfModules.restrictScalars.{u} aX ⋙ g.modules,
      ∀ M : ringedSiteModules.{u} BX,
        (diagramCoefficientUnderlying AY).map (c.hom.app M) ≫
            g.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
          f.underlying.hom.app M ≫
            eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M)) hDir) := by
  classical
  rcases f with ⟨F, G, adj, hF, p, hp0, hp1, hpadd, hpmul, H, hH, eH, hlinH⟩
  rcases g with ⟨F', G', adj', hF', q, hq0, hq1, hqadd, hqmul, I, hI, eI, hlinI⟩
  dsimp only at hInv hDir hAdj hRing ⊢
  subst F'
  subst G'
  cases hAdj
  simp only [eqToHom_refl, Category.id_comp] at hRing
  let resX := SheafOfModules.restrictScalars.{u} aX
  let resY := SheafOfModules.restrictScalars.{u} aY
  let α (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M)) ≅
        (diagramCoefficientUnderlying AY).obj (I.obj (resX.obj M)) :=
    eH.app M ≪≫ (eI.app (resX.obj M)).symm
  have hα (M : ringedSiteModules.{u} BX) :
      (α M).hom ≫ eI.hom.app (resX.obj M) = eH.hom.app M := by
    change (eH.hom.app M ≫ eI.inv.app (resX.obj M)) ≫ eI.hom.app (resX.obj M) = _
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ eH.hom.app M ≫ k) (eI.inv_hom_id_app (resX.obj M))).trans
        (Category.comp_id _))
  have hlinear (M : ringedSiteModules.{u} BX) (T : Sheaf L (Type u))
      (a : T ⟶ (sheafCompose L (forget RingCat)).obj AY)
      (x y : T ⟶ (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))) :
      linearOperation (resY.obj (H.obj M)) T a x y ≫ (α M).hom =
        linearOperation (I.obj (resX.obj M)) T a (x ≫ (α M).hom) (y ≫ (α M).hom) := by
    apply (cancel_mono (eI.hom.app (resX.obj M))).mp
    apply (adj.homEquiv T ((diagramCoefficientUnderlying BX).obj M)).symm.injective
    rw [Category.assoc, hα]
    ext U t
    have hb := hlinH M T (a ≫ (sheafCompose L (forget RingCat)).map aY)
      x y (linearOperation (resY.obj (H.obj M)) T a x y) (fun _ _ ↦ rfl) U t
    have hs := hlinI (resX.obj M) T a (x ≫ (α M).hom) (y ≫ (α M).hom)
      (linearOperation (I.obj (resX.obj M)) T a (x ≫ (α M).hom) (y ≫ (α M).hom))
      (fun _ _ ↦ rfl) U t
    have hr : F.map (a ≫ (sheafCompose L (forget RingCat)).map aY) ≫ p =
        (F.map a ≫ q) ≫ (sheafCompose K (forget RingCat)).map aX := by
      rw [F.map_comp, Category.assoc, hRing, Category.assoc]
    simp only [Category.assoc, hα] at hs
    rw [hr] at hb
    exact hb.trans hs.symm
  let one (T : Sheaf L (Type u)) : T ⟶ (sheafCompose L (forget RingCat)).obj AY :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : AY.obj.obj U))
       naturality := by intro U V f; ext t; exact (AY.obj.map f).hom.map_one.symm }⟩
  have hadd (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (x y : (resY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (x + y) =
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U y) := by
    let X := (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))
    have hh := congrArg (fun f ↦ f.hom.app U (x, y))
      (hlinear M (X ⊗ X) (one _) (CartesianMonoidalCategory.fst X X)
        (CartesianMonoidalCategory.snd X X))
    change (α M).hom.hom.app U ((1 : AY.obj.obj U) • x + y) =
      (1 : AY.obj.obj U) •
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
          (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U y) at hh
    simpa only [one_smul] using hh
  have hsmul (M : ringedSiteModules.{u} BX) (U : Dᵒᵖ)
      (r : AY.obj.obj U) (x : (resY.obj (H.obj M)).val.obj U) :
      (α M).hom.hom.app U (r • x) = r •
        (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) := by
    let X := (diagramCoefficientUnderlying AY).obj (resY.obj (H.obj M))
    let R := (sheafCompose L (forget RingCat)).obj AY
    let z : R ⊗ X ⟶ X :=
      ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : (resY.obj (H.obj M)).val.obj U))
         naturality := by
           intro U V f
           ext t
           exact ((resY.obj (H.obj M)).val.map f).hom.map_zero.symm }⟩
    have hh := congrArg (fun f ↦ f.hom.app U (r, x))
      (hlinear M (R ⊗ X) (CartesianMonoidalCategory.fst R X)
        (CartesianMonoidalCategory.snd R X) z)
    have hzero : (α M).hom.hom.app U (0 : (resY.obj (H.obj M)).val.obj U) =
        (0 : (I.obj (resX.obj M)).val.obj U) := by
      have hz := hadd M U 0 0
      exact (@add_eq_left ((I.obj (resX.obj M)).val.obj U)
        inferInstance inferInstance _ _).mp (by simpa only [zero_add] using hz.symm)
    change (α M).hom.hom.app U (r • x + 0) = r •
      (show (I.obj (resX.obj M)).val.obj U from (α M).hom.hom.app U x) +
        (show (I.obj (resX.obj M)).val.obj U from
          (α M).hom.hom.app U (0 : (resY.obj (H.obj M)).val.obj U)) at hh
    simpa only [add_zero, hzero] using hh
  let f (M : ringedSiteModules.{u} BX) : resY.obj (H.obj M) ⟶ I.obj (resX.obj M) :=
    { val :=
        { app := fun U ↦ @ModuleCat.ofHom (AY.obj.obj U) inferInstance
            ((resY.obj (H.obj M)).val.obj U) ((I.obj (resX.obj M)).val.obj U)
            ((resY.obj (H.obj M)).val.obj U).isAddCommGroup
            ((resY.obj (H.obj M)).val.obj U).isModule
            ((I.obj (resX.obj M)).val.obj U).isAddCommGroup
            ((I.obj (resX.obj M)).val.obj U).isModule
            { toFun := (α M).hom.hom.app U
              map_add' := hadd M U
              map_smul' := hsmul M U }
          naturality := by
            intro U V h
            ext x
            exact CategoryTheory.congr_fun ((α M).hom.hom.naturality h) x } }
  have hf (M : ringedSiteModules.{u} BX) :
      (diagramCoefficientUnderlying AY).map (f M) = (α M).hom := rfl
  have hi (M : ringedSiteModules.{u} BX) : IsIso (f M) := by
    have : IsIso ((diagramCoefficientUnderlying AY).map (f M)) := by rw [hf]; infer_instance
    exact isIso_of_reflects_iso (f M) (diagramCoefficientUnderlying AY)
  let β : H ⋙ resY ⟶ resX ⋙ I :=
    { app := f
      naturality := by
        intro M N h
        apply (diagramCoefficientUnderlying AY).map_injective
        simp only [Functor.map_comp, hf]
        apply (cancel_mono (eI.hom.app (resX.obj N))).mp
        simp only [Category.assoc, hα]
        have hI' := eI.hom.naturality (resX.map h)
        have hH' := eH.hom.naturality h
        change (diagramCoefficientUnderlying AY).map (I.map (resX.map h)) ≫
            eI.hom.app (resX.obj N) = eI.hom.app (resX.obj M) ≫
              G.map ((diagramCoefficientUnderlying BX).map h) at hI'
        change (diagramCoefficientUnderlying AY).map (resY.map (H.map h)) ≫
            eH.hom.app N = eH.hom.app M ≫
              G.map ((diagramCoefficientUnderlying BX).map h) at hH'
        dsimp only [Functor.comp_map]
        erw [hI', ← Category.assoc, hα]
        exact hH' }
  have : IsIso β := NatIso.isIso_of_isIso_app β
  refine ⟨asIso β, ?_⟩
  intro M
  simp only [eqToHom_refl, Category.comp_id]
  exact hα M

private theorem coefficientRestriction_exact
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    {R S : Sheaf K RingCat.{u}} (a : R ⟶ S) :
    PreservesFiniteLimits (SheafOfModules.restrictScalars.{u} a) ∧
      PreservesFiniteColimits (SheafOfModules.restrictScalars.{u} a) := by
  let r := SheafOfModules.restrictScalars.{u} a
  have : PreservesFiniteLimits (r ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf S))
  have : PreservesFiniteColimits (r ⋙ SheafOfModules.toSheaf R) :=
    inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf S))
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u} R) :=
    reflectsFiniteColimitsOfReflectsIsomorphisms _
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves r (SheafOfModules.toSheaf R),
    preservesFiniteColimits_of_reflects_of_preserves r (SheafOfModules.toSheaf R)⟩

private theorem coefficientCommRingSheaf
    {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K RingCat.{u})
    (hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a) :
    ∃ O : Sheaf K CommRingCat.{u},
      (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj O = R := by
  let obj (U : Cᵒᵖ) : CommRingCat.{u} :=
    { carrier := R.obj.obj U
      commRing := { (inferInstance : Ring (R.obj.obj U)) with mul_comm := hcomm U } }
  let Oc : Cᵒᵖ ⥤ CommRingCat.{u} :=
    { obj := obj
      map := fun {U V} g ↦
        @CommRingCat.ofHom (obj U) (obj V) (obj U).commRing (obj V).commRing
          (R.obj.map g).hom
      map_id := fun U ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_id U)
      map_comp := fun g h ↦ by
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (R.obj.map_comp g h) }
  have hO : Presheaf.IsSheaf K Oc := by
    apply Presheaf.isSheaf_of_isSheaf_comp K Oc (forget₂ CommRingCat RingCat)
    exact R.property
  exact ⟨⟨Oc, hO⟩, rfl⟩

private theorem derivedCoefficientComparison
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : A' ⥤ B') (x : A ⥤ A') (y : B ⥤ B')
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    (rX : DerivedCategory.{w} A ⥤ DerivedCategory.{w} A')
    (rY : DerivedCategory.{w} B ⥤ DerivedCategory.{w} B')
    (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
      x.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
      y.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w})
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RG : DerivedCategory.{w} A' ⥤ DerivedCategory.{w} B')
    (etaF : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (etaG : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RG)
    (hF : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (etaF.app I))
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj I)))
    (c : F ⋙ y ≅ x ⋙ G) :
    ∃! kappa : RF ⋙ rY ≅ rX ⋙ RG,
      ∀ M : CochainComplex A ℤ,
        phiY.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
            rY.map (etaF.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
          DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
            etaG.app ((x.mapHomologicalComplex (.up ℤ)).obj M) ≫ RG.map (phiX.inv.app M) := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let xc := x.mapHomologicalComplex (.up ℤ)
  let cc := NatIso.mapHomologicalComplex c (.up ℤ)
  -- Both units derive the same ordinary composite; exactness is encoded by phiX and phiY.
  let etaL : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ rY) :=
    Functor.whiskerLeft Fc phiY.inv ≫ Functor.whiskerRight etaF rY
  let etaR : (F ⋙ y).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (rX ⋙ RG) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q.{w} ≫
      Functor.whiskerLeft xc etaG ≫ Functor.whiskerRight phiX.inv RG
  have hL : (RF ⋙ rY).IsRightDerivedFunctor etaL
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaL
    intro I
    have := hF I.obj I.property
    change IsIso (phiY.inv.app (Fc.obj I.obj) ≫ rY.map (etaF.app I.obj))
    infer_instance
  have hR : (rX ⋙ RG).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derives (F ⋙ y)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have := hG I.obj I.property
    change IsIso (DerivedCategory.Q.map (cc.hom.app I.obj) ≫
      etaG.app (xc.obj I.obj) ≫ RG.map (phiX.inv.app I.obj))
    infer_instance
  let _ := hL
  let _ := hR
  let kappa := Functor.rightDerivedUnique (RF ⋙ rY) (rX ⋙ RG) etaL etaR
    (HomologicalComplex.quasiIso A (.up ℤ))
  have hkappa (M : CochainComplex A ℤ) :
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M) = etaR.app M := by
    simpa only [kappa, Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Iso.refl, NatTrans.id_app, Category.id_comp] using
      (Functor.rightDerivedNatTrans_app (RF ⋙ rY) (rX ⋙ RG) etaL etaR
        (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom M)
  refine ⟨kappa, ?_, ?_⟩
  · intro M
    simpa only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using hkappa M
  · intro k hk
    apply Iso.ext
    apply Functor.rightDerived_ext (RF ⋙ rY) etaL
      (HomologicalComplex.quasiIso A (.up ℤ))
    apply NatTrans.ext
    funext M
    change etaL.app M ≫ k.hom.app (DerivedCategory.Q.obj M) =
      etaL.app M ≫ kappa.hom.app (DerivedCategory.Q.obj M)
    rw [hkappa]
    simpa only [etaL, etaR, cc, Fc, xc, NatIso.mapHomologicalComplex,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using hk M

private theorem coefficientAcyclicDerived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    (R S : Sheaf K RingCat.{u}) (T : Sheaf L RingCat.{u})
    (hR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ (U : Cᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    (hT : ∀ (U : Dᵒᵖ) (a b : T.obj.obj U), a * b = b * a)
    (a : R ⟶ S) (f : RingedToposMorphism R T)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} S)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} T)] :
    ∃ (RF : DerivedCategory.{w} (ringedSiteModules.{u} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} T))
      (eta : f.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RF),
      RF.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} R) (.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} R) ℤ,
        I.IsKInjective → IsIso (eta.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} S) ℤ,
        I.IsKInjective → IsIso (eta.app
          (((SheafOfModules.restrictScalars.{u} a).mapHomologicalComplex (.up ℤ)).obj I))) := by
  obtain ⟨OR, rfl⟩ := coefficientCommRingSheaf R hR
  obtain ⟨OS, rfl⟩ := coefficientCommRingSheaf S hS
  obtain ⟨OT, rfl⟩ := coefficientCommRingSheaf T hT
  let r := siteRestrictionRingedTopos a
  -- The composition unit detects acyclicity of restricted K-injectives.
  obtain ⟨Rr, RF, Rc, etar, eta, etac, hr, hf, hc, hI, hF, k, hk, -⟩ :=
    ringedToposDerivedPushforwardComposition K K L OS OR OT r f
  refine ⟨RF, eta, hf, hF, ?_⟩
  intro I hInj
  have : IsIso (etar.app I) := (hI I hInj).1
  have : IsIso (etac.app I) := (hI I hInj).2
  have hh : IsIso (eta.app ((r.modules.mapHomologicalComplex (.up ℤ)).obj I) ≫
      RF.map (etar.app I)) := by
    rw [← hk.1 I]
    infer_instance
  let := hh
  have hi : IsIso (eta.app ((r.modules.mapHomologicalComplex (.up ℤ)).obj I)) :=
    IsIso.of_isIso_comp_right _ (RF.map (etar.app I))
  exact hi

end

-- Keep the original interface, including hBY and hStructuralS, which this proof does not need.
set_option linter.unusedVariables false in
/-- Derived scalar restriction commutes with derived diagram direct image, with its
common-composite normalization before evaluation.

Source: Stacks Project, Cohomology on Sites, Tag 0D6E,
lemma-derived-pushforward-composition
(blueprint: lem-pur-diagram-ring-restriction-pushforward).

Proof plan:
1. Use lem-weil-pbc-diagram-site-realization to realize the diagram topoi.
A ring sheaf on the product site is the ring diagram; its module sheaves have
semilinear transitions by def-weil-sheaf-of-modules-category. The geometric
adjunction is the componentwise adjunction transported by the site equivalences.
2. The identity-topos ring maps aX and aY have module direct images
SheafOfModules.restrictScalars (def-pc-sheaf-restrict-scalars). The square hRing
identifies the two structural maps of the composite. Under the specified
underlying direct-image identifications this gives the unique ordinary iso c.
3. Restriction changes only scalar actions, so is exact on underlying abelian
sheaves. By lem-weil-pbc-exact-functor-derived-factorization, it has termwise
localization lifts rX and rY with the isomorphisms phiX and phiY. For a resolution
M -> I, restriction preserves the quasi-isomorphism, even if its image is not
K-injective; this identifies the lifts with the derived identity-topos direct images.
4. Apply lem-weil-pbc-ringed-topoi-derived-pushforward-composition to both
factorizations of the common ringed-topos morphism. The two composition
comparisons, through the derived direct image of that common morphism, give kappa.
5. The composition comparisons commute with their resolution units. After the
termwise identifications of step 3, this is exactly the displayed equation for
every complex M. Uniqueness of derived functors makes this equation characterize
kappa uniquely. All functors act on the full diagram site; no evaluation is used. -/
theorem diagramRingRestrictionPushforward
    (J C D : Type u) [SmallCategory J] [SmallCategory C] [SmallCategory D]
    (K : GrothendieckTopology C) (L : GrothendieckTopology D)
    (SX : Sheaf K RingCat.{u}) (SY : Sheaf L RingCat.{u})
    (hSX : ∀ (U : Cᵒᵖ) (a b : SX.obj.obj U), a * b = b * a)
    (hSY : ∀ (U : Dᵒᵖ) (a b : SY.obj.obj U), a * b = b * a)
    (BX : Sheaf (diagramSiteTopology J C K) RingCat.{u})
    (BY : Sheaf (diagramSiteTopology J D L) RingCat.{u})
    (hBX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (hBY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : BY.obj.obj U), a * b = b * a)
    (aX : diagramSiteRing J C K SX ⟶ BX) (aY : diagramSiteRing J D L SY ⟶ BY)
    (s : RingedToposMorphism SX SY)
    (fB : RingedToposMorphism BX BY)
    (fS : RingedToposMorphism (diagramSiteRing J C K SX) (diagramSiteRing J D L SY))
    (hInvB : fB.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hInvS : fS.inverse = diagramCoefficientInverse J C D K L s.inverse)
    (hDirB : fB.direct = diagramCoefficientDirect J C D K L s.direct)
    (hDirS : fS.direct = diagramCoefficientDirect J C D K L s.direct)
    (hAdjB : HEq fB.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hAdjS : HEq fS.adj (diagramCoefficientAdjunction J C D K L s.adj))
    (hStructuralS : ∀ (j : J) (U : C),
      HEq (fS.ringMap.hom.app (Opposite.op (Opposite.op j, U)))
        (s.ringMap.hom.app (Opposite.op U)))
    (hRing : fB.inverse.map ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).map aY) ≫ fB.ringMap =
      eqToHom (congrArg (fun H ↦ H.obj ((sheafCompose (diagramSiteTopology J D L)
        (forget RingCat)).obj (diagramSiteRing J D L SY)))
        (hInvB.trans hInvS.symm)) ≫ fS.ringMap ≫
      (sheafCompose (diagramSiteTopology J C K) (forget RingCat)).map aX)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX))]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY))] :
    ∃ (rX : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)))
      (rY : DerivedCategory.{w} (ringedSiteModules.{u} BY) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (phiX : DerivedCategory.Q.{w} ⋙ rX ≅
        (SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (phiY : DerivedCategory.Q.{w} ⋙ rY ≅
        (SheafOfModules.restrictScalars.{u} aY).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q.{w})
      (RB : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} BY))
      (RS : DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ⥤
        DerivedCategory.{w} (ringedSiteModules.{u} (diagramSiteRing J D L SY)))
      (etaB : fB.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RB)
      (etaS : fS.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ RS),
      RB.IsRightDerivedFunctor etaB
        (HomologicalComplex.quasiIso (ringedSiteModules.{u} BX) (ComplexShape.up ℤ)) ∧
      RS.IsRightDerivedFunctor etaS (HomologicalComplex.quasiIso
        (ringedSiteModules.{u} (diagramSiteRing J C K SX)) (ComplexShape.up ℤ)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} BX) ℤ,
        I.IsKInjective → IsIso (etaB.app I)) ∧
      (∀ I : CochainComplex (ringedSiteModules.{u} (diagramSiteRing J C K SX)) ℤ,
        I.IsKInjective → IsIso (etaS.app I)) ∧
      ∃! c : fB.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
          SheafOfModules.restrictScalars.{u} aX ⋙ fS.modules,
        (∀ M : ringedSiteModules.{u} BX,
          (diagramCoefficientUnderlying (diagramSiteRing J D L SY)).map (c.hom.app M) ≫
              fS.underlying.hom.app ((SheafOfModules.restrictScalars.{u} aX).obj M) =
            fB.underlying.hom.app M ≫
              eqToHom (congrArg (fun H ↦ H.obj ((diagramCoefficientUnderlying BX).obj M))
                (hDirB.trans hDirS.symm))) ∧
        ∃! kappa : RB ⋙ rY ≅ rX ⋙ RS,
          ∀ M : CochainComplex (ringedSiteModules.{u} BX) ℤ,
            phiY.inv.app ((fB.modules.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
                rY.map (etaB.app M) ≫ kappa.hom.app (DerivedCategory.Q.{w}.obj M) =
              DerivedCategory.Q.{w}.map
                  ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app M) ≫
                etaS.app
                  (((SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex
                    (ComplexShape.up ℤ)).obj M) ≫ RS.map (phiX.inv.app M) := by
  -- Unfold the concrete restriction functors only while assembling the proof.
  set_option backward.isDefEq.respectTransparency false in
    exact (by
      classical
      let := coefficientRingCompose (diagramSiteTopology J C K)
      let := coefficientRingCompose (diagramSiteTopology J D L)
      let := coefficientAddCompose (diagramSiteTopology J C K)
      let := coefficientAddCompose (diagramSiteTopology J D L)
      let := coefficientSheafify (diagramSiteTopology J C K)
      let := coefficientSheafify (diagramSiteTopology J D L)
      let := coefficientLocallyBijective (diagramSiteTopology J C K)
      let := coefficientLocallyBijective (diagramSiteTopology J D L)
      let AX := diagramSiteRing J C K SX
      let AY := diagramSiteRing J D L SY
      have hAX : ∀ (U : (Jᵒᵖ × C)ᵒᵖ) (a b : AX.obj.obj U), a * b = b * a := by
        intro U a b
        exact hSX _ a b
      have hAY : ∀ (U : (Jᵒᵖ × D)ᵒᵖ) (a b : AY.obj.obj U), a * b = b * a := by
        intro U a b
        exact hSY _ a b
      have hgroth : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} BX) :=
        SheafOfModules.isGrothendieckAbelian BX
      let := hgroth
      let _ : Abelian.HasKInjectiveResolutions (ringedSiteModules.{u} BX) := inferInstance
      obtain ⟨RB, etaB, hRB, hB⟩ := exists_derived.{w} fB.modules
      obtain ⟨RS, etaS, hRS, hS, hSXacyc⟩ :=
        coefficientAcyclicDerived AX BX AY hAX hBX hAY aX fS
      let resX := SheafOfModules.restrictScalars.{u} aX
      let resY := SheafOfModules.restrictScalars.{u} aY
      have : PreservesFiniteLimits resX := (coefficientRestriction_exact aX).1
      have : PreservesFiniteColimits resX := (coefficientRestriction_exact aX).2
      have : PreservesFiniteLimits resY := (coefficientRestriction_exact aY).1
      have : PreservesFiniteColimits resY := (coefficientRestriction_exact aY).2
      let rX : DerivedCategory.{w} (ringedSiteModules.{u} BX) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u} AX) := resX.mapDerivedCategory.{w, w}
      let rY : DerivedCategory.{w} (ringedSiteModules.{u} BY) ⥤
          DerivedCategory.{w} (ringedSiteModules.{u} AY) := resY.mapDerivedCategory.{w, w}
      let phiX : DerivedCategory.Q.{w} ⋙ rX ≅
          resX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} :=
        resX.mapDerivedCategoryFactors.{w, w}
      let phiY : DerivedCategory.Q.{w} ⋙ rY ≅
          resY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} :=
        resY.mapDerivedCategoryFactors.{w, w}
      -- Normalize on underlying sheaves first, then apply uniqueness of right derived functors.
      obtain ⟨c, hc⟩ := ordinaryCoefficientComparison aX aY fB fS
        (hInvB.trans hInvS.symm) (hDirB.trans hDirS.symm)
        (hAdjB.trans hAdjS.symm) hRing
      refine ⟨rX, rY, phiX, phiY, RB, RS, etaB, etaS, hRB, hRS, hB, hS, c, ?_, ?_⟩
      · refine ⟨hc, ?_⟩
        exact derivedCoefficientComparison fB.modules fS.modules resX resY
          rX rY phiX phiY RB RS etaB etaS hB hSXacyc c
      · intro c' hc'
        apply Iso.ext
        apply NatTrans.ext
        funext M
        apply (diagramCoefficientUnderlying AY).map_injective
        apply (cancel_mono (fS.underlying.hom.app (resX.obj M))).mp
        exact (hc'.1 M).trans (hc M).symm
    )

end CategoryTheory
