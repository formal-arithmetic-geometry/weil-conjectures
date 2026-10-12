/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Representation

/-!
# Transport of stalks of finite locally constant sheaves along paths

Let `s, s'` be geometric points of a scheme `Y` and `τ : F_s ≅ F_{s'}` an isomorphism of the fibre
functors on finite étale `Y`-schemes (a path from `s` to `s'`). Identifying the stalk of a finite
locally constant sheaf of sets with the geometric fibre of the finite étale `Y`-scheme representing
it, `τ` transports stalks at `s` to stalks at `s'`
(`AlgebraicGeometry.Scheme.FiniteLocallyConstant.transport`), naturally in the sheaf. For finite
locally constant sheaves of modules over a finite ring the transport is linear
(`AlgebraicGeometry.Scheme.FiniteLocallyConstantModule.transportLinearEquiv`), since it is natural
with respect to the addition `F ⊞ F ⟶ F` and the scalar multiplications.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
  (s : Spec (.of Ω) ⟶ Y) (s' : Spec (.of Ω') ⟶ Y)
  (τ : FiniteEtale.fiber s ≅ FiniteEtale.fiber s')

namespace FiniteEtale

/-- The bijection of geometric fibres given by an isomorphism of fibre functors. -/
noncomputable def fiberEquivOfIso (P : Y.FiniteEtale) : (fiber s).obj P ≃ (fiber s').obj P where
  toFun := τ.hom.app P
  invFun := τ.inv.app P
  left_inv x := ConcreteCategory.congr_hom (τ.hom_inv_id_app P) x
  right_inv x := ConcreteCategory.congr_hom (τ.inv_hom_id_app P) x

end FiniteEtale

namespace FiniteLocallyConstant

open FiniteEtale

/-- The transport of the stalks of a finite locally constant sheaf of sets along an isomorphism
of fibre functors, through the geometric fibres of the representing finite étale scheme. -/
noncomputable def transport (F : Y.FiniteLocallyConstant) : stalk s F ≃ stalk s' F :=
  ((repStalkEquiv s F).trans (Equiv.ulift.trans ((fiberEquivOfIso s s' τ (rep Y F)).trans
    Equiv.ulift.symm))).trans (repStalkEquiv s' F).symm

lemma isoStalkEquiv_transport {F : Y.FiniteLocallyConstant} {P : Y.FiniteEtale}
    (i : F ≅ (sectionsFunctor Y).obj P) (x : stalk s F) :
    isoStalkEquiv s' i (transport s s' τ F x) =
      ULift.up (τ.hom.app P (isoStalkEquiv s i x).down) := by
  obtain ⟨φ, hφ⟩ := exists_sectionsFunctor_map_eq ((repIso F).inv ≫ i.hom)
  have h : 𝟙 F ≫ i.hom = (repIso F).hom ≫ (sectionsFunctor Y).map φ := by
    rw [hφ, Iso.hom_inv_id_assoc, Category.id_comp]
  have key {Ω'' : Type u} [Field Ω''] [IsSepClosed Ω''] (s'' : Spec (.of Ω'') ⟶ Y)
      (y : stalk s'' F) :
      isoStalkEquiv s'' i y =
        ULift.up ((FiniteEtale.fiber s'').map φ (repStalkEquiv s'' F y).down) := by
    simpa [stalkMap_id] using isoStalkEquiv_stalkMap s'' (repIso F) i (𝟙 F) φ h y
  rw [key, key]
  unfold transport
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom.naturality φ) _).symm

lemma stalkMap_transport {F F' : Y.FiniteLocallyConstant} (f : F ⟶ F') (x : stalk s F) :
    stalkMap s' f (transport s s' τ F x) = transport s s' τ F' (stalkMap s f x) := by
  obtain ⟨φ, hφ⟩ := exists_sectionsFunctor_map_eq ((repIso F).inv ≫ f ≫ (repIso F').hom)
  have h : f ≫ (repIso F').hom = (repIso F).hom ≫ (sectionsFunctor Y).map φ := by
    rw [hφ, Iso.hom_inv_id_assoc]
  apply (repStalkEquiv s' F').injective
  rw [isoStalkEquiv_stalkMap s' _ _ f φ h, isoStalkEquiv_transport, isoStalkEquiv_transport,
    isoStalkEquiv_stalkMap s _ _ f φ h]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom.naturality φ) _).symm

end FiniteLocallyConstant

namespace FiniteLocallyConstantModule

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The transport of the stalks of a finite locally constant sheaf of `Λ`-modules along an
isomorphism of fibre functors. -/
noncomputable def transport (F : Y.FiniteLocallyConstantModule Λ) (x : stalk s F) : stalk s' F :=
  forgetStalkEquiv s' F
    (FiniteLocallyConstant.transport s s' τ _ ((forgetStalkEquiv s F).symm x))

lemma stalkMap_transport {F F' : Y.FiniteLocallyConstantModule Λ} (f : F ⟶ F') (x : stalk s F) :
    stalkMap s' f (transport s s' τ F x) = transport s s' τ F' (stalkMap s f x) := by
  simp only [transport]
  rw [← forgetStalkEquiv_naturality, FiniteLocallyConstant.stalkMap_transport,
    forgetStalkEquiv_symm_naturality]

lemma transport_symm_transport (F : Y.FiniteLocallyConstantModule Λ) (x : stalk s F) :
    transport s' s τ.symm F (transport s s' τ F x) = x := by
  simp only [transport, Equiv.symm_apply_apply]
  apply (forgetStalkEquiv s F).symm.injective
  rw [Equiv.symm_apply_apply]
  apply (FiniteLocallyConstant.repStalkEquiv s _).injective
  rw [FiniteLocallyConstant.isoStalkEquiv_transport, FiniteLocallyConstant.isoStalkEquiv_transport]
  exact congrArg ULift.up (ConcreteCategory.congr_hom (τ.hom_inv_id_app _) _)

lemma transport_add (F : Y.FiniteLocallyConstantModule Λ) (x y : stalk s F) :
    transport s s' τ F (x + y) = transport s s' τ F x + transport s s' τ F y := by
  have h₁ := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  have h₂ := (pointSmallEtale s').sheafFiber_additive (A := ModuleCat.{u + 1} Λ)
  let fst : double F ⟶ F := ObjectProperty.homMk biprod.fst
  let snd : double F ⟶ F := ObjectProperty.homMk biprod.snd
  let inl : F ⟶ double F := ObjectProperty.homMk biprod.inl
  let inr : F ⟶ double F := ObjectProperty.homMk biprod.inr
  let add : double F ⟶ F := ObjectProperty.homMk (biprod.desc (𝟙 _) (𝟙 _))
  have hdesc : (biprod.desc (𝟙 F.obj) (𝟙 F.obj)) = biprod.fst + biprod.snd := by
    simp [biprod.desc_eq]
  have hadd (w : stalk s (double F)) :
      stalkMap s add w = stalkMap s fst w + stalkMap s snd w := by
    change (pointSmallEtale s).sheafFiber.map (biprod.desc (𝟙 F.obj) (𝟙 F.obj)) w = _
    rw [hdesc, Functor.map_add]
    rfl
  have hadd' (w : stalk s' (double F)) :
      stalkMap s' add w = stalkMap s' fst w + stalkMap s' snd w := by
    change (pointSmallEtale s').sheafFiber.map (biprod.desc (𝟙 F.obj) (𝟙 F.obj)) w = _
    rw [hdesc, Functor.map_add]
    rfl
  have hcomp {A B C : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (a : A ⟶ B) (b : B ⟶ C)
      (w) : (pointSmallEtale s).sheafFiber.map (a ≫ b) w =
        (pointSmallEtale s).sheafFiber.map b ((pointSmallEtale s).sheafFiber.map a w) := by
    rw [Functor.map_comp, ConcreteCategory.comp_apply]
  have hid {A : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (w) :
      (pointSmallEtale s).sheafFiber.map (𝟙 A) w = w := by
    rw [CategoryTheory.Functor.map_id]
    rfl
  have hzero {A B : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (w) :
      (pointSmallEtale s).sheafFiber.map (0 : A ⟶ B) w = 0 := by
    rw [Functor.map_zero]
    rfl
  let z := stalkMap s inl x + stalkMap s inr y
  have e₁ : stalkMap s fst (stalkMap s inl x) = x := by
    change (pointSmallEtale s).sheafFiber.map (biprod.fst : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inl : F.obj ⟶ F.obj ⊞ F.obj) x) = x
    rw [← hcomp, biprod.inl_fst, hid]
  have e₂ : stalkMap s fst (stalkMap s inr y) = 0 := by
    change (pointSmallEtale s).sheafFiber.map (biprod.fst : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inr : F.obj ⟶ F.obj ⊞ F.obj) y) = 0
    rw [← hcomp, biprod.inr_fst, hzero]
  have e₃ : stalkMap s snd (stalkMap s inl x) = 0 := by
    change (pointSmallEtale s).sheafFiber.map (biprod.snd : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inl : F.obj ⟶ F.obj ⊞ F.obj) x) = 0
    rw [← hcomp, biprod.inl_snd, hzero]
  have e₄ : stalkMap s snd (stalkMap s inr y) = y := by
    change (pointSmallEtale s).sheafFiber.map (biprod.snd : F.obj ⊞ F.obj ⟶ F.obj)
      ((pointSmallEtale s).sheafFiber.map (biprod.inr : F.obj ⟶ F.obj ⊞ F.obj) y) = y
    rw [← hcomp, biprod.inr_snd, hid]
  have hfst : stalkMap s fst z = x := by
    simp only [z, map_add, e₁, e₂, add_zero]
  have hsnd : stalkMap s snd z = y := by
    simp only [z, map_add, e₃, e₄, zero_add]
  rw [← hfst, ← hsnd, ← hadd, ← stalkMap_transport, hadd', stalkMap_transport,
    stalkMap_transport]

lemma transport_smul (F : Y.FiniteLocallyConstantModule Λ) (c : Λ) (x : stalk s F) :
    transport s s' τ F (c • x) = c • transport s s' τ F x := by
  let m : F ⟶ F := ObjectProperty.homMk (c • 𝟙 F.obj)
  have hm {Ω'' : Type u} [Field Ω''] [IsSepClosed Ω''] (s'' : Spec (.of Ω'') ⟶ Y)
      (w : stalk s'' F) : stalkMap s'' m w = c • w := by
    change (pointSmallEtale s'').sheafFiber.map (c • 𝟙 F.obj) w = _
    rw [GrothendieckTopology.Point.sheafFiber_map_smul, CategoryTheory.Functor.map_id]
    rfl
  rw [← hm s x, ← stalkMap_transport, hm]

/-- The `Λ`-linear transport of the stalks of a finite locally constant sheaf of `Λ`-modules
along an isomorphism of fibre functors. -/
noncomputable def transportLinearEquiv (F : Y.FiniteLocallyConstantModule Λ) :
    stalk s F ≃ₗ[Λ] stalk s' F where
  toFun := transport s s' τ F
  invFun := transport s' s τ.symm F
  map_add' := transport_add s s' τ F
  map_smul' := transport_smul s s' τ F
  left_inv := transport_symm_transport s s' τ F
  right_inv x := by
    have := transport_symm_transport s' s τ.symm F x
    rwa [Iso.symm_symm_eq] at this

lemma transportLinearEquiv_apply (F : Y.FiniteLocallyConstantModule Λ) (x : stalk s F) :
    transportLinearEquiv s s' τ F x = transport s s' τ F x :=
  rfl

section Invariants

variable [ConnectedSpace Y] (G : Type u) [Group G]
  [∀ P, MulAction G ((FiniteEtale.fiber s).obj P)]
  [PreGaloisCategory.IsNaturalSMul (FiniteEtale.fiber s) G]

lemma smul_stalk_zero (F : Y.FiniteLocallyConstantModule Λ) (g : G) :
    smul s G g (0 : stalk s F) = 0 := by
  have := smul_smul s G g (0 : Λ) (0 : stalk s F)
  rwa [zero_smul, zero_smul] at this

/-- The invariants of a subgroup `H` of the fundamental group `G = π₁(Y, s)` in the stalk `F_s`
of a finite locally constant sheaf of `Λ`-modules. -/
def invariants (F : Y.FiniteLocallyConstantModule Λ) (H : Subgroup G) :
    Submodule Λ (stalk s F) where
  carrier := {x | ∀ g ∈ H, smul s G g x = x}
  add_mem' {a b} ha hb g hg := by rw [smul_add, ha g hg, hb g hg]
  zero_mem' g _ := smul_stalk_zero s G F g
  smul_mem' c x hx g hg := by rw [smul_smul, hx g hg]

end Invariants

end FiniteLocallyConstantModule

end AlgebraicGeometry.Scheme
