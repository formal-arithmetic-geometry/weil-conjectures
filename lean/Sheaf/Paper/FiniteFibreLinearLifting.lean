/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K7
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Paper.LatticeNormalizationRationalExact
import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems

/-! # Lifting an equivariant finite module fibre isomorphism

Source: Stacks Project, Tag 0DV5 (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.Scheme

private instance forgetPreserves {R : Type (u + 1)} [CommRing R] :
    PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _

private theorem set_fibre_map
    {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group) (F G : T.FLC)
    (f : (flcFiber p.point).obj F → (flcFiber p.point).obj G)
    (hf : ∀ (g : p.group) x,
      f ((c.γ g).hom.app F x) = (c.γ g).hom.app G (f x)) :
    ∃ d : F ⟶ G, (flcFiber p.point).map d = f := by
  classical
  let : ConnectedSpace T := p.connected
  let A := c.Φ.inverse.obj F
  let B := c.Φ.inverse.obj G
  let eF : ULift.{u + 1} ((FiniteEtale.fiber p.point).obj A) ≅
      (flcFiber p.point).obj F :=
    (c.η.app A).symm ≪≫ (flcFiber p.point).mapIso (c.Φ.counitIso.app F)
  let eG : ULift.{u + 1} ((FiniteEtale.fiber p.point).obj B) ≅
      (flcFiber p.point).obj G :=
    (c.η.app B).symm ≪≫ (flcFiber p.point).mapIso (c.Φ.counitIso.app G)
  have he (H : T.FLC) (g : p.group)
      (z : ULift.{u + 1} ((FiniteEtale.fiber p.point).obj (c.Φ.inverse.obj H))) :
      let e := (c.η.app (c.Φ.inverse.obj H)).symm ≪≫
        (flcFiber p.point).mapIso (c.Φ.counitIso.app H)
      e.hom ⟨g • z.down⟩ = (c.γ g).hom.app H (e.hom z) := by
    dsimp only
    have h := c.finiteEtaleAction (c.Φ.inverse.obj H) g
      ((c.η.app (c.Φ.inverse.obj H)).inv z)
    have h' : (c.η.app (c.Φ.inverse.obj H)).inv ⟨g • z.down⟩ =
        (c.γ g).hom.app (c.Φ.functor.obj (c.Φ.inverse.obj H))
          ((c.η.app (c.Φ.inverse.obj H)).inv z) := by
      apply (c.η.app (c.Φ.inverse.obj H)).toEquiv.injective
      change (c.η.app (c.Φ.inverse.obj H)).hom
        ((c.η.app (c.Φ.inverse.obj H)).inv _) = _
      rw [Iso.inv_hom_id_apply]
      have hz := ConcreteCategory.congr_hom
        (c.η.inv_hom_id_app (c.Φ.inverse.obj H)) z
      change (c.η.app (c.Φ.inverse.obj H)).hom
        ((c.γ g).hom.app (c.Φ.functor.obj (c.Φ.inverse.obj H))
          ((c.η.app (c.Φ.inverse.obj H)).inv z)) =
          ULift.up (g • ((c.η.app (c.Φ.inverse.obj H)).hom
            ((c.η.app (c.Φ.inverse.obj H)).inv z)).down) at h
      rw [Iso.inv_hom_id_apply] at h
      exact h.symm
    change (flcFiber p.point).map (c.Φ.counitIso.hom.app H)
      ((c.η.app (c.Φ.inverse.obj H)).inv ⟨g • z.down⟩) = _
    rw [h']
    exact ConcreteCategory.congr_hom
      ((c.γ g).hom.naturality (c.Φ.counitIso.hom.app H)).symm _
  let k : (FiniteEtale.fiber p.point).obj A → (FiniteEtale.fiber p.point).obj B :=
    fun x ↦ (eG.inv (f (eF.hom ⟨x⟩))).down
  have hk (g : p.group) (x : (FiniteEtale.fiber p.point).obj A) :
      k (g • x) = g • k x := by
    apply ULift.up_injective
    apply eG.toEquiv.injective
    change eG.hom (eG.inv (f (eF.hom ⟨g • x⟩))) = eG.hom ⟨g • k x⟩
    erw [he F, Iso.inv_hom_id_apply, hf]
    erw [he G]
    congr 1
    exact (Iso.inv_hom_id_apply eG _).symm
  let E := FiniteEtale.equivalenceContAction p.point p.group
  let a : E.functor.obj A ⟶ E.functor.obj B :=
    ObjectProperty.homMk ⟨ObjectProperty.homMk (TypeCat.ofHom k), fun g ↦ by
      apply ConcreteCategory.hom_ext
      intro x
      exact hk g x⟩
  let d : F ⟶ G := c.Φ.counitIso.inv.app F ≫ c.Φ.functor.map (E.functor.preimage a) ≫
    c.Φ.counitIso.hom.app G
  refine ⟨d, ?_⟩
  funext x
  let q := E.functor.preimage a
  have ha : (FiniteEtale.fiber p.point).map q =
      ObjectProperty.homMk (TypeCat.ofHom k) := by
    exact congrArg (fun h ↦ h.hom.hom) (E.functor.map_preimage a)
  have hn := ConcreteCategory.congr_hom (c.η.inv.naturality q)
    ((c.η.hom.app A) ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x))
  dsimp only [d]
  simp only [Functor.map_comp, CategoryTheory.comp_apply]
  change (flcFiber p.point).map (c.Φ.counitIso.hom.app G)
    ((flcFiber p.point).map (c.Φ.functor.map q)
      ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x)) = f x
  have hx : (c.η.inv.app A)
      ((c.η.hom.app A) ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x)) =
      (flcFiber p.point).map (c.Φ.counitIso.inv.app F) x :=
    ConcreteCategory.congr_hom (c.η.hom_inv_id_app A) _
  change (c.η.inv.app B)
      ((CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}).map
        ((FiniteEtale.fiber p.point).map q)
        ((c.η.hom.app A) ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x))) =
    (flcFiber p.point).map (c.Φ.functor.map q)
      ((c.η.inv.app A)
        ((c.η.hom.app A) ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x))) at hn
  rw [hx, ha] at hn
  rw [← hn]
  change eG.hom ⟨k ((c.η.hom.app A)
    ((flcFiber p.point).map (c.Φ.counitIso.inv.app F) x)).down⟩ = f x
  change eG.hom (eG.inv (f (eF.hom (eF.inv x)))) = f x
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]


private theorem set_map_linear
    {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    {R : Type (u + 1)} [CommRing R]
    (F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hG : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R G))
    (d : galoisUnderlyingSetSheaf R F ⟶ galoisUnderlyingSetSheaf R G)
    (e : (((pointSmallEtale p.point).sheafFiber (A := ModuleCat.{u + 1} R)).obj F) →ₗ[R]
      (((pointSmallEtale p.point).sheafFiber (A := ModuleCat.{u + 1} R)).obj G))
    (hd : ∀ x, (pointSmallEtale p.point).sheafFiber.map d
      ((((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F).inv x) =
      (((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).app G).inv (e x)) :
    ∃ f : F ⟶ G,
      (sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} R))).map f = d := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let St := (pointSmallEtale p.point).sheafFiber (A := Type (u + 1))
  let U := galoisUnderlyingSetSheaf R F
  let V := galoisUnderlyingSetSheaf R G
  let kF := (((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F).symm
  let kG := (((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app G).symm
  have hgerm (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
      (A : T.Etale) (ξ : (pointSmallEtale p.point).fiber.obj A) (x : H.obj.obj (op A)) :
      St.map (𝟙 (galoisUnderlyingSetSheaf R H))
        ((pointSmallEtale p.point).toPresheafFiber A ξ
          (galoisUnderlyingSetSheaf R H).obj x) =
      (((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).inv
          ((pointSmallEtale p.point).toPresheafFiber A ξ H.obj x) := by
    rw [St.map_id]
    let k := (((pointSmallEtale p.point).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H)
    have h := ConcreteCategory.congr_hom
      ((pointSmallEtale p.point).toPresheafFiber_presheafFiberCompIso_hom_app
        (CategoryTheory.forget (ModuleCat.{u + 1} R)) A ξ H.obj) x
    apply k.toEquiv.injective
    change k.hom _ = k.hom (k.inv _)
    rw [Iso.inv_hom_id_apply]
    exact h
  let add (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      galoisUnderlyingSetSheaf R H ⨯ galoisUnderlyingSetSheaf R H ⟶
        galoisUnderlyingSetSheaf R H :=
    ⟨{ app := fun A ↦ TypeCat.ofHom (fun x ↦
          @Add.add (H.obj.obj A) inferInstance
            ((prod.fst (X := galoisUnderlyingSetSheaf R H)
              (Y := galoisUnderlyingSetSheaf R H)).hom.app A x)
            ((prod.snd (X := galoisUnderlyingSetSheaf R H)
              (Y := galoisUnderlyingSetSheaf R H)).hom.app A x))
       naturality := fun A B f ↦ by
         ext x
         symm
         change (H.obj.map f) (_ + _) = _
         rw [map_add]
         congr 1
         · exact (ConcreteCategory.congr_hom
             ((prod.fst (X := galoisUnderlyingSetSheaf R H)
               (Y := galoisUnderlyingSetSheaf R H)).hom.naturality f) x).symm
         · exact (ConcreteCategory.congr_hom
             ((prod.snd (X := galoisUnderlyingSetSheaf R H)
               (Y := galoisUnderlyingSetSheaf R H)).hom.naturality f) x).symm }⟩
  let smul (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : R) :
      galoisUnderlyingSetSheaf R H ⟶ galoisUnderlyingSetSheaf R H :=
    ⟨{ app := fun A ↦ TypeCat.ofHom (fun x : H.obj.obj A ↦ r • x)
       naturality := fun A B f ↦ by
         ext x
         exact (map_smul (H.obj.map f).hom r (show H.obj.obj A from x)).symm }⟩
  have ha (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
      (w : St.obj (galoisUnderlyingSetSheaf R H ⨯ galoisUnderlyingSetSheaf R H)) :
      St.map (add H) w =
        (((pointSmallEtale p.point).sheafFiberCompIso
          (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).inv
          (((((pointSmallEtale p.point).sheafFiberCompIso
            (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).hom
              (St.map prod.fst w)) +
           ((((pointSmallEtale p.point).sheafFiberCompIso
            (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).hom
              (St.map prod.snd w))) := by
    dsimp only [St] at w ⊢
    obtain ⟨A, ξ, x, rfl⟩ := (pointSmallEtale p.point).toPresheafFiber_jointly_surjective
      (P := (galoisUnderlyingSetSheaf R H ⨯ galoisUnderlyingSetSheaf R H).obj) w
    have hn (f : galoisUnderlyingSetSheaf R H ⨯ galoisUnderlyingSetSheaf R H ⟶
        galoisUnderlyingSetSheaf R H) := ConcreteCategory.congr_hom
      ((pointSmallEtale p.point).toPresheafFiber_naturality f.hom A ξ) x
    simp only [CategoryTheory.comp_apply] at hn
    erw [hn (add H), hn prod.fst, hn prod.snd]
    have h := hgerm H A ξ
    simp only [St.map_id, CategoryTheory.id_apply] at h
    erw [h, h, h]
    simp only [Iso.inv_hom_id_apply]
    congr 1
    change (pointSmallEtale p.point).toPresheafFiber A ξ H.obj (_ + _) = _
    exact map_add ((pointSmallEtale p.point).toPresheafFiber A ξ H.obj).hom _ _
  have hs (H : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) (r : R)
      (x : ((pointSmallEtale p.point).sheafFiber (A := ModuleCat.{u + 1} R)).obj H) :
      St.map (smul H r)
        ((((pointSmallEtale p.point).sheafFiberCompIso
          (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).inv x) =
      (((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).app H).inv (r • x) := by
    obtain ⟨A, ξ, x, rfl⟩ := (pointSmallEtale p.point).toPresheafFiber_jointly_surjective
      (P := H.obj) x
    have h := hgerm H A ξ
    simp only [St.map_id, CategoryTheory.id_apply] at h
    rw [← h]
    have hn := ConcreteCategory.congr_hom
      ((pointSmallEtale p.point).toPresheafFiber_naturality (smul H r).hom A ξ) x
    simp only [CategoryTheory.comp_apply] at hn
    erw [hn]
    change (pointSmallEtale p.point).toPresheafFiber A ξ
      (galoisUnderlyingSetSheaf R H).obj (r • x) = _
    erw [h]
    apply congrArg _
    exact map_smul ((pointSmallEtale p.point).toPresheafFiber A ξ H.obj).hom r x
  have hprod : IsLisseEtaleSheafOfSets (U ⨯ U) := by
    obtain ⟨⟨𝒰, h𝒰⟩, hf⟩ := hF
    refine ⟨⟨𝒰, fun i ↦ ?_⟩, isFiniteSheaf_prod hf hf⟩
    have := h𝒰 i
    exact isConstant_over_prod _
  have : (flcFiber p.point).Faithful := finite_fiber_faithful p c
  have ext {A B : Sheaf T.smallEtaleTopology (Type (u + 1))}
      (hA : IsLisseEtaleSheafOfSets A) (hB : IsLisseEtaleSheafOfSets B)
      (f g : A ⟶ B) (h : St.map f = St.map g) : f = g := by
    exact congrArg (fun k : (⟨A, hA⟩ : T.FLC) ⟶ ⟨B, hB⟩ ↦ k.hom)
      ((flcFiber p.point).map_injective h)
  have hadd : add F ≫ d = prod.map d d ≫ add G := by
    apply ext hprod hG
    apply ConcreteCategory.hom_ext
    intro w
    simp only [Functor.map_comp, CategoryTheory.comp_apply]
    rw [ha]
    change St.map d (kF.hom (kF.inv (St.map prod.fst w) +
      kF.inv (St.map prod.snd w))) = _
    erw [hd, e.map_add, ha]
    have h₁ := congrArg (fun f ↦ St.map f w) (prod.map_fst d d)
    have h₂ := congrArg (fun f ↦ St.map f w) (prod.map_snd d d)
    simp only [Functor.map_comp, CategoryTheory.comp_apply] at h₁ h₂
    erw [h₁, h₂]
    have hd' (x : St.obj U) : St.map d x = kG.hom (e (kF.inv x)) := by
      have hh := hd (kF.inv x)
      change St.map d (kF.hom (kF.inv x)) = kG.hom (e (kF.inv x)) at hh
      rw [Iso.inv_hom_id_apply] at hh
      exact hh
    erw [hd', hd']
    change kG.hom _ = kG.hom (kG.inv (kG.hom _) + kG.inv (kG.hom _))
    simp only [Iso.hom_inv_id_apply]
    rfl
  have hsmul (r : R) : smul F r ≫ d = d ≫ smul G r := by
    apply ext hF hG
    apply ConcreteCategory.hom_ext
    intro x
    obtain ⟨x, rfl⟩ := kF.toEquiv.surjective x
    simp only [Functor.map_comp, CategoryTheory.comp_apply]
    change St.map d (St.map (smul F r) (kF.hom x)) =
      St.map (smul G r) (St.map d (kF.hom x))
    erw [hs, hd, hd, hs, e.map_smul]
  let fst : U ⨯ U ⟶ U := prod.fst
  let snd : U ⨯ U ⟶ U := prod.snd
  let f : F ⟶ G :=
    ⟨{ app := fun A ↦ ModuleCat.ofHom
         { toFun := fun x : F.obj.obj A ↦ (d.hom.app A x : G.obj.obj A)
           map_add' := fun x y ↦ by
             have hxy : ∃ z : (U ⨯ U).obj.obj A,
                 fst.hom.app A z = x ∧ snd.hom.app A z = y := by
               obtain ⟨z, hz⟩ :=
                 (Functor.bijective_map_prod_fst_snd
                   (sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj A) U U).2
                     (x, y)
               exact ⟨z, congrArg Prod.fst hz, congrArg Prod.snd hz⟩
             obtain ⟨z, hz₁, hz₂⟩ := hxy
             have h := ConcreteCategory.congr_hom
               (congrArg (fun k : U ⨯ U ⟶ V ↦ k.hom.app A) hadd) z
             change d.hom.app A (@Add.add (F.obj.obj A) inferInstance
                 (fst.hom.app A z) (snd.hom.app A z)) =
               @Add.add (G.obj.obj A) inferInstance
                 ((prod.fst (X := V) (Y := V)).hom.app A ((prod.map d d).hom.app A z))
                 ((prod.snd (X := V) (Y := V)).hom.app A ((prod.map d d).hom.app A z)) at h
             have h₁ := ConcreteCategory.congr_hom
               (congrArg (fun k : U ⨯ U ⟶ V ↦ k.hom.app A) (prod.map_fst d d)) z
             have h₂ := ConcreteCategory.congr_hom
               (congrArg (fun k : U ⨯ U ⟶ V ↦ k.hom.app A) (prod.map_snd d d)) z
             change (prod.fst (X := V) (Y := V)).hom.app A ((prod.map d d).hom.app A z) =
               d.hom.app A (fst.hom.app A z) at h₁
             change (prod.snd (X := V) (Y := V)).hom.app A ((prod.map d d).hom.app A z) =
               d.hom.app A (snd.hom.app A z) at h₂
             rw [h₁, h₂, hz₁, hz₂] at h
             exact h
           map_smul' := fun r x ↦
             ConcreteCategory.congr_hom
               (congrArg (fun k : U ⟶ V ↦ k.hom.app A) (hsmul r)) x }
       naturality := fun A B f ↦ by
         ext x
         exact ConcreteCategory.congr_hom (d.hom.naturality f) x }⟩
  exact ⟨f, rfl⟩

/-- An equivariant linear isomorphism of finite locally constant module fibres lifts
uniquely to a module-sheaf isomorphism. The coefficient ring itself need not be finite.

Source: Stacks Project, Tag 0DV5 (3), proof by module objects in finite locally constant
sheaves; Bhatt--Scholze, Corollary 6.8.5, p. 60
(blueprint: lem-a1-finite-fibre-linear-lifting).

Proof: Use the finite-etale/FLC equivalence and the finite-etale fundamental-group
fibre equivalence to lift the underlying equivariant bijection to an isomorphism of
finite locally constant set sheaves. The comparison with evaluation on the given
fundamental group is precisely the finiteEtaleAction equation. On fibres the lifted
map preserves addition and every integral scalar, because the given map is linear.
The finite fibre functor is faithful; apply this to the addition diagram, whose source
is the product of two finite locally constant set sheaves, and separately to each
scalar diagram. The lifted set map therefore preserves addition and scalars on all
sections, and so defines a module-sheaf map. The same argument applies to the inverse.
Faithfulness on underlying finite locally constant sheaves proves uniqueness. Only
finiteness of the module stalks is used; infinitely many scalar diagrams are checked
one at a time, so finiteness of the coefficient ring is unnecessary. -/
theorem finite_fibre_linear_lifting (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {T : Scheme.{u}} (p : SfMonodromyPoint T)
    (c : GaloisLisseFiniteCorrespondence p.point p.group)
    (F G : Sheaf T.smallEtaleTopology
      (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf _ F))
    (hG : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf _ G))
    (e : (((pointSmallEtale p.point).sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj F)
      ≃ₗ[Padic.coefficientExtensionIntegers l E]
      (((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj G))
    (he : ∀ (g : p.group) (x y : ((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).obj F),
      sfModuleFiberToSet l E p F y =
        (c.γ g).hom.app (galoisUnderlyingFLC _ F hF) (sfModuleFiberToSet l E p F x) →
      sfModuleFiberToSet l E p G (e y) =
        (c.γ g).hom.app (galoisUnderlyingFLC _ G hG)
          (sfModuleFiberToSet l E p G (e x))) :
    ∃! d : F ≅ G,
      ((pointSmallEtale p.point).sheafFiber
        (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))).mapIso d =
          e.toModuleIso := by
  classical
  let R := Padic.coefficientExtensionIntegers l E
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} _
  let A : T.FLC := galoisUnderlyingFLC R F hF
  let B : T.FLC := galoisUnderlyingFLC R G hG
  let kF := (((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app F).symm
  let kG := (((pointSmallEtale p.point).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} R))).app G).symm
  let f := fun x : (flcFiber p.point).obj A ↦ kG.hom (e (kF.inv x))
  have hf (g : p.group) (x : (flcFiber p.point).obj A) :
      f ((c.γ g).hom.app A x) = (c.γ g).hom.app B (f x) := by
    apply he g (kF.inv x) (kF.inv ((c.γ g).hom.app A x))
    change kF.hom (kF.inv _) = (c.γ g).hom.app A (kF.hom (kF.inv x))
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  obtain ⟨d, hd⟩ := set_fibre_map p c A B f hf
  have hdf (x) : (pointSmallEtale p.point).sheafFiber.map d.hom (kF.hom x) =
      kG.hom (e x) := by
    change (flcFiber p.point).map d (kF.hom x) = _
    rw [hd]
    change kG.hom (e (kF.inv (kF.hom x))) = _
    rw [Iso.hom_inv_id_apply]
  obtain ⟨a, ha⟩ := set_map_linear p c F G hF hG d.hom e.toLinearMap hdf
  let invf := fun x : (flcFiber p.point).obj B ↦ kF.hom (e.symm (kG.inv x))
  have hinvf (g : p.group) (x : (flcFiber p.point).obj B) :
      invf ((c.γ g).hom.app B x) = (c.γ g).hom.app A (invf x) := by
    have hleft (x) : invf (f x) = x := by
      change kF.hom (e.symm (kG.inv (kG.hom (e (kF.inv x))))) = x
      rw [Iso.hom_inv_id_apply, e.symm_apply_apply, Iso.inv_hom_id_apply]
    have hright (x) : f (invf x) = x := by
      change kG.hom (e (kF.inv (kF.hom (e.symm (kG.inv x))))) = x
      rw [Iso.hom_inv_id_apply, e.apply_symm_apply, Iso.inv_hom_id_apply]
    apply (fun {x y} h ↦ (hleft x).symm.trans ((congrArg invf h).trans (hleft y)))
    rw [hright, hf, hright]
  obtain ⟨d', hd'⟩ := set_fibre_map p c B A invf hinvf
  have hdf' (x) : (pointSmallEtale p.point).sheafFiber.map d'.hom (kG.hom x) =
      kF.hom (e.symm x) := by
    change (flcFiber p.point).map d' (kG.hom x) = _
    rw [hd']
    change kF.hom (e.symm (kG.inv (kG.hom x))) = _
    rw [Iso.hom_inv_id_apply]
  obtain ⟨b, hb⟩ := set_map_linear p c G F hG hF d'.hom e.symm.toLinearMap hdf'
  let D := sheafCompose T.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R))
  have : (flcFiber p.point).Faithful := finite_fiber_faithful p c
  have ext {H K : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)}
      (hH : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R H))
      (hK : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R K))
      (a b : H ⟶ K)
      (h : ((pointSmallEtale p.point).sheafFiber.map a) =
        ((pointSmallEtale p.point).sheafFiber.map b)) : a = b := by
    apply D.map_injective
    suffices (ObjectProperty.homMk (D.map a) :
        galoisUnderlyingFLC R H hH ⟶ galoisUnderlyingFLC R K hK) =
          ObjectProperty.homMk (D.map b) from congrArg (fun f ↦ f.hom) this
    apply (flcFiber p.point).map_injective
    let k := (pointSmallEtale p.point).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} R))
    apply (cancel_mono (k.hom.app K)).mp
    exact (k.hom.naturality a).trans
      ((congrArg (fun t ↦ k.hom.app H ≫ (CategoryTheory.forget _).map t) h).trans
        (k.hom.naturality b).symm)
  have hmap : ((pointSmallEtale p.point).sheafFiber.map a) = e.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply kG.toEquiv.injective
    have h := ConcreteCategory.congr_hom
      (((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm.hom.naturality a).symm x
    change (pointSmallEtale p.point).sheafFiber.map (D.map a) (kF.hom x) =
      kG.hom (((pointSmallEtale p.point).sheafFiber.map a) x) at h
    rw [ha] at h
    exact h.symm.trans (hdf x)
  have hmap' : ((pointSmallEtale p.point).sheafFiber.map b) = e.toModuleIso.inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply kF.toEquiv.injective
    have h := ConcreteCategory.congr_hom
      (((pointSmallEtale p.point).sheafFiberCompIso
        (CategoryTheory.forget (ModuleCat.{u + 1} R))).symm.hom.naturality b).symm x
    change (pointSmallEtale p.point).sheafFiber.map (D.map b) (kG.hom x) =
      kF.hom (((pointSmallEtale p.point).sheafFiber.map b) x) at h
    rw [hb] at h
    exact h.symm.trans (hdf' x)
  let q : F ≅ G :=
    { hom := a
      inv := b
      hom_inv_id := ext hF hF _ _ (by
        rw [Functor.map_comp, hmap, hmap']
        exact e.toModuleIso.hom_inv_id.trans
          ((pointSmallEtale p.point).sheafFiber.map_id F).symm)
      inv_hom_id := ext hG hG _ _ (by
        rw [Functor.map_comp, hmap', hmap]
        exact e.toModuleIso.inv_hom_id.trans
          ((pointSmallEtale p.point).sheafFiber.map_id G).symm) }
  refine ⟨q, Iso.ext hmap, ?_⟩
  intro q' hq'
  apply Iso.ext
  apply ext hF hG
  exact (congrArg (fun t ↦ t.hom) hq').trans hmap.symm

end AlgebraicGeometry.Scheme
