/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GeneratingPullbackChartGeometry
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.ProperBaseChange.RingedToposKFlatPullback
import all WeilConjectures.ProperBaseChange.GeometricModuleTransport
import all WeilConjectures.CategoryTheory.ProperBaseChange.ContinuousCocontinuousRingedRestriction

/-! The ordinary module inverse-image comparison of a ringed object-slice square.

Source: Stacks Project, Modules on Sites, Tags 03D7, 04IE and 04IF.
(blueprint: lem-weil-pbc-object-slice-module-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4000
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private noncomputable abbrev sets
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.toSheaf R ⋙ sheafCompose J (forget AddCommGrpCat)

private theorem inverse_product_comparison
    {A B : Type*} [Category A] [Category B] [HasBinaryProducts A] [HasBinaryProducts B]
    (F G : A ⥤ B) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (e : F ≅ G) (X Y : A) :
    inv (prodComparison F X Y) ≫ e.hom.app (X ⨯ Y) =
      prod.map (e.hom.app X) (e.hom.app Y) ≫ inv (prodComparison G X Y) := by
  apply (cancel_mono (prodComparison G X Y)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [prodComparison_natural_of_natTrans]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

private theorem transport_binary_operation
    {A B : Type*} [Category A] [Category B] [HasBinaryProducts A] [HasBinaryProducts B]
    (F G : A ⥤ B) [PreservesFiniteProducts F] [PreservesFiniteProducts G]
    (e : F ≅ G) {X Y Z : A} (a : X ⨯ Y ⟶ Z)
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : B}
    (p₁ : P₁ ⟶ F.obj X) (p₂ : P₂ ⟶ F.obj Y) (p₃ : P₃ ⟶ F.obj Z)
    (q₁ : Q₁ ⟶ G.obj X) (q₂ : Q₂ ⟶ G.obj Y) (q₃ : Q₃ ⟶ G.obj Z) [Mono q₃]
    (b : P₁ ⨯ P₂ ⟶ P₃) (c : Q₁ ⨯ Q₂ ⟶ Q₃)
    (k₁ : P₁ ⟶ Q₁) (k₂ : P₂ ⟶ Q₂) (k₃ : P₃ ⟶ Q₃)
    (h₁ : k₁ ≫ q₁ = p₁ ≫ e.hom.app X)
    (h₂ : k₂ ≫ q₂ = p₂ ≫ e.hom.app Y)
    (h₃ : k₃ ≫ q₃ = p₃ ≫ e.hom.app Z)
    (hb : b ≫ p₃ = prod.map p₁ p₂ ≫ inv (prodComparison F X Y) ≫ F.map a)
    (hc : c ≫ q₃ = prod.map q₁ q₂ ≫ inv (prodComparison G X Y) ≫ G.map a) :
    b ≫ k₃ = prod.map k₁ k₂ ≫ c := by
  apply (cancel_mono q₃).mp
  rw [Category.assoc, h₃, ← Category.assoc, hb]
  rw [Category.assoc, Category.assoc, e.hom.naturality a]
  rw [← Category.assoc (inv (prodComparison F X Y)),
    inverse_product_comparison F G e]
  rw [Category.assoc (prod.map k₁ k₂), hc]
  simp only [← Category.assoc, prod.map_map, h₁, h₂]

private theorem ringed_module_right_iso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f g : RingedToposMorphism
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B))
    (t : f.inverse ≅ g.inverse)
    (hring : t.hom.app ((sheafCompose K (forget CommRingCat)).obj B) ≫
      g.ringMap = f.ringMap) : Nonempty (f.modules ≅ g.modules) := by
  classical
  let : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let : PreservesLimits g.direct := g.adj.rightAdjoint_preservesLimits
  let r : f.direct ≅ g.direct := conjugateIsoEquiv f.adj g.adj t.symm
  have mate {X : Sheaf K (Type u)} {Y : Sheaf J (Type u)}
      (a : X ⟶ f.direct.obj Y) :
      (g.adj.homEquiv _ _).symm (a ≫ r.hom.app Y) =
        t.inv.app X ≫ (f.adj.homEquiv _ _).symm a := by
    rw [Adjunction.homEquiv_counit, g.inverse.map_comp, Category.assoc]
    change g.inverse.map a ≫ g.inverse.map
      ((conjugateEquiv f.adj g.adj t.inv).app Y) ≫ g.adj.counit.app Y = _
    rw [conjugateEquiv_counit, t.inv.naturality_assoc]
    rw [Adjunction.homEquiv_counit]
  have hd : f.adj.homEquiv
        (SheafOfModules.GeometricConstruction.rset B)
        (SheafOfModules.GeometricConstruction.rset A) f.ringMap ≫
      r.hom.app (SheafOfModules.GeometricConstruction.rset A) =
        g.adj.homEquiv (SheafOfModules.GeometricConstruction.rset B)
          (SheafOfModules.GeometricConstruction.rset A) g.ringMap := by
    apply (g.adj.homEquiv (SheafOfModules.GeometricConstruction.rset B)
      (SheafOfModules.GeometricConstruction.rset A)).symm.injective
    rw [mate, Equiv.symm_apply_apply, Equiv.symm_apply_apply, ← hring]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  let h : f.modules ⋙ sets ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) ≅
      g.modules ⋙ sets ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B) :=
    f.underlying ≪≫ Functor.isoWhiskerLeft (sets _) r ≪≫ g.underlying.symm
  have lifts (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) :
      ∃ φ : f.modules.obj M ⟶ g.modules.obj M,
        (sets ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)).map φ = (h.app M).hom := by
    have hm : (h.app M).hom ≫ g.underlying.hom.app M =
        f.underlying.hom.app M ≫ r.hom.app ((sets _).obj M) := by
      simp [h]
    obtain ⟨hfadd, hfsmul⟩ := h4_supplied_operations f M
    obtain ⟨hgadd, hgsmul⟩ := h4_supplied_operations g M
    have ha := transport_binary_operation f.direct g.direct r (madd A M)
      (f.underlying.hom.app M) (f.underlying.hom.app M) (f.underlying.hom.app M)
      (g.underlying.hom.app M) (g.underlying.hom.app M) (g.underlying.hom.app M)
      (madd B (f.modules.obj M)) (madd B (g.modules.obj M))
      (h.app M).hom (h.app M).hom (h.app M).hom hm hm hm hfadd hgadd
    have hs := transport_binary_operation f.direct g.direct r (msmul A M)
      (f.adj.homEquiv (SheafOfModules.GeometricConstruction.rset B)
        (SheafOfModules.GeometricConstruction.rset A) f.ringMap) (f.underlying.hom.app M)
      (f.underlying.hom.app M)
      (g.adj.homEquiv (SheafOfModules.GeometricConstruction.rset B)
        (SheafOfModules.GeometricConstruction.rset A) g.ringMap) (g.underlying.hom.app M)
      (g.underlying.hom.app M)
      (msmul B (f.modules.obj M)) (msmul B (g.modules.obj M))
      (𝟙 _) (h.app M).hom (h.app M).hom (by simpa using hd.symm) hm hm hfsmul hgsmul
    obtain ⟨φ, hφ⟩ := (SheafOfModules.linear_iff (𝟙 B) (f.modules.obj M) (g.modules.obj M)
      (madd B (f.modules.obj M)) (madd B (g.modules.obj M))
      (msmul B (f.modules.obj M)) (msmul B (g.modules.obj M))
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (h.app M).hom).mpr
        ⟨ha, by simpa only [Functor.map_id] using hs⟩
    exact ⟨φ, hφ⟩
  choose φ hφ using lifts
  have (M : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)) : IsIso (φ M) := by
    have : IsIso ((sets ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)).map (φ M)) := by
      rw [hφ]
      infer_instance
    exact isIso_of_reflects_iso (φ M) (sets _)
  refine ⟨NatIso.ofComponents (fun M ↦ asIso (φ M)) ?_⟩
  intro M N a
  apply (sets ((sheafCompose K (forget₂ CommRingCat RingCat)).obj B)).map_injective
  simp only [Functor.map_comp, asIso_hom, hφ]
  simpa only [Functor.comp_map, Iso.app_hom] using h.hom.naturality a

private noncomputable def composeRinged
    {C D E : Type u} [SmallCategory C] [SmallCategory D] [SmallCategory E]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : GrothendieckTopology E}
    {A : Sheaf J RingCat.{u}} {B : Sheaf K RingCat.{u}} {R : Sheaf L RingCat.{u}}
    (f : RingedToposMorphism A B) (g : RingedToposMorphism B R) :
    RingedToposMorphism A R := by
  let : PreservesFiniteLimits f.inverse := f.leftExact
  let : PreservesFiniteLimits g.inverse := g.leftExact
  let e : (f.modules ⋙ g.modules) ⋙ sets R ≅ sets A ⋙ (f.direct ⋙ g.direct) :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft f.modules g.underlying ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight f.underlying g.direct ≪≫
        Functor.associator _ _ _
  refine {
    inverse := g.inverse ⋙ f.inverse
    direct := f.direct ⋙ g.direct
    adj := g.adj.comp f.adj
    leftExact := comp_preservesFiniteLimits _ _
    ringMap := f.inverse.map g.ringMap ≫ f.ringMap
    ring_zero := ?_
    ring_one := ?_
    ring_add := ?_
    ring_mul := ?_
    modules := f.modules ⋙ g.modules
    additive := inferInstance
    underlying := e
    module_linear := ?_ }
  · intro T z hz U t
    change (f.inverse.map (g.inverse.map z) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app
      U t = @Zero.zero (A.obj.obj U) inferInstance
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      f.ring_zero (g.inverse.obj T) (g.inverse.map z ≫ g.ringMap)
        (g.ring_zero T z hz) U t
  · intro T z hz U t
    change (f.inverse.map (g.inverse.map z) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app
      U t = @One.one (A.obj.obj U) inferInstance
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      f.ring_one (g.inverse.obj T) (g.inverse.map z ≫ g.ringMap)
        (g.ring_one T z hz) U t
  · intro T x y z hz U t
    change (f.inverse.map (g.inverse.map z) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app
      U t = @Add.add (A.obj.obj U) inferInstance
        ((f.inverse.map (g.inverse.map x) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app U t)
        ((f.inverse.map (g.inverse.map y) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app U t)
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      f.ring_add (g.inverse.obj T)
        (g.inverse.map x ≫ g.ringMap) (g.inverse.map y ≫ g.ringMap)
        (g.inverse.map z ≫ g.ringMap) (g.ring_add T x y z hz) U t
  · intro T x y z hz U t
    change (f.inverse.map (g.inverse.map z) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app
      U t = @Mul.mul (A.obj.obj U) inferInstance
        ((f.inverse.map (g.inverse.map x) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app U t)
        ((f.inverse.map (g.inverse.map y) ≫ f.inverse.map g.ringMap ≫ f.ringMap).hom.app U t)
    simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
      f.ring_mul (g.inverse.obj T)
        (g.inverse.map x ≫ g.ringMap) (g.inverse.map y ≫ g.ringMap)
        (g.inverse.map z ≫ g.ringMap) (g.ring_mul T x y z hz) U t
  · intro M T a x y z hz U t
    let trans (v : T ⟶ (sets R).obj (g.modules.obj (f.modules.obj M))) :=
      (g.adj.homEquiv _ _).symm (v ≫ g.underlying.hom.app (f.modules.obj M))
    have hg := g.module_linear (f.modules.obj M) T a x y z hz
    have hf := f.module_linear M (g.inverse.obj T) (g.inverse.map a ≫ g.ringMap)
      (trans x) (trans y) (trans z) hg U t
    have he (v : T ⟶ (sets R).obj (g.modules.obj (f.modules.obj M))) :
        ((g.adj.comp f.adj).homEquiv _ _).symm (v ≫ e.hom.app M) =
          (f.adj.homEquiv _ _).symm (trans v ≫ f.underlying.hom.app M) := by
      dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_hom_app,
        Functor.associator_inv_app, Functor.isoWhiskerLeft_hom,
        Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app]
      simp only [Category.id_comp, Category.comp_id, Adjunction.comp_homEquiv,
        Equiv.symm_trans_apply]
      congr 1
      rw [← Category.assoc v]
      exact g.adj.homEquiv_naturality_right_symm
        (v ≫ g.underlying.hom.app (f.modules.obj M)) (f.underlying.hom.app M)
    have hfac : (g.inverse ⋙ f.inverse).map a ≫
        (f.inverse.map g.ringMap ≫ f.ringMap) =
        f.inverse.map (g.inverse.map a ≫ g.ringMap) ≫ f.ringMap := by
      simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [he, he, he, hfac]
    change (((f.adj.homEquiv _ _).symm
        (trans z ≫ f.underlying.hom.app M)).hom.app U t) =
      @Add.add (M.val.obj U) inferInstance
        (@SMul.smul (A.obj.obj U) (M.val.obj U) inferInstance
          ((f.inverse.map (g.inverse.map a ≫ g.ringMap) ≫ f.ringMap).hom.app U t)
          (((f.adj.homEquiv _ _).symm
            (trans x ≫ f.underlying.hom.app M)).hom.app U t))
        (((f.adj.homEquiv _ _).symm
          (trans y ≫ f.underlying.hom.app M)).hom.app U t)
    exact hf



/-- A ringed inverse-image restriction square induces the ordinary module square.
Source: Stacks Project, Modules on Sites, Tags 03D7, 04IE and 04IF.
(blueprint: lem-weil-pbc-object-slice-module-comparison).

Proof: realize the two restrictions by the continuous cocontinuous object-site
projections and their induced ringed morphisms. Compose each projection with the
corresponding side of the square. Their inverse-image functors are identified by
the chart comparison, and the structural equation identifies their ring maps.
The mate of this comparison identifies the sheaf direct images. Naturality of
this mate at addition and scalar multiplication, together with the transpose
formula for the structural ring maps, shows that it lifts to a linear natural
isomorphism of the induced module direct images. Its components are invertible
because the forgetful functor reflects isomorphisms. The two composite module
left adjoints are therefore naturally isomorphic by uniqueness of left adjoints.
This gives the required ordinary pullback comparison without an exactness or
flatness assumption. Natural transformations preserve finite-product comparisons,
which supplies the binary-operation calculation used for the linearity check. -/
theorem object_slice_module_comparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RY : Sheaf J CommRingCat.{u}) (RX : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX)
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY))
    (U : D) (V : C)
    (chart : ObjectSliceRingedChart RY RX f U V)
    (G : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) ⥤
      ringedSiteModules.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX))
    (hG : G ⊣ f.modules)
    (F : ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (RY.over V)) ⥤
      ringedSiteModules.{u}
        ((sheafCompose (K.over U) (forget₂ CommRingCat RingCat)).obj (RX.over U)))
    (hF : F ⊣ chart.morphism.modules) :
    Nonempty (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj RY) V ⋙ F ≅
      G ⋙ SheafOfModules.overFunctor.{u}
        ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RX) U) := by
  classical
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj RY
  let S := (sheafCompose K (forget₂ CommRingCat RingCat)).obj RX
  let ly := ringedRestriction (J := J.over V) (Over.forget V) R
  let lx := ringedRestriction (J := K.over U) (Over.forget U) S
  let a := composeRinged chart.morphism ly
  let b := composeRinged lx f
  let ht : a.inverse ≅ b.inverse := chart.comparison
  have hr : ht.hom.app ((sheafCompose J (forget CommRingCat)).obj RY) ≫
      b.ringMap = a.ringMap := by
    dsimp only [ht, a, b, composeRinged, lx, ly, ringedRestriction, R, S, restrictedRing]
    simp only [Functor.map_id, Category.comp_id]
    erw [Category.id_comp]
    exact chart.structural.symm
  obtain ⟨e⟩ := ringed_module_right_iso (RX.over U) RY a b ht hr
  have ay : SheafOfModules.overFunctor R V ⊣ ly.modules :=
    familyAdjunction (J := J.over V) (Over.forget V) R
  have ax : SheafOfModules.overFunctor S U ⊣ lx.modules :=
    familyAdjunction (J := K.over U) (Over.forget U) S
  exact ⟨Adjunction.leftAdjointUniq ((ay.comp hF).ofNatIsoRight e) (hG.comp ax)⟩

end CategoryTheory
