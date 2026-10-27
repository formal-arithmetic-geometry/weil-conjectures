/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.AlgebraicGeometry.MeromorphicModule
import Sheaf.AlgebraicGeometry.AssociatedPointsEqWeaklyAssociatedPoints
import Sheaf.AlgebraicGeometry.MeromorphicGenericProduct
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Meromorphic sections and generic-point products

Source: Stacks Project, Divisors, Tag 0EMH (divisors-lemma-quasi-coherent-K).
(blueprint: lem-sc-meromorphic-sheaf-generic-product).

The stalk identifications are normalized on ordinary sections. Multiplication of meromorphic
sections is characterized by the local fraction formula, so the final clause concerns the
canonical meromorphic action, not an arbitrary action transported from a product.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_generalization_eq {X : Scheme.{u}}
    (η : {x : X // x ∈ genericPoints X}) {x : X} (hx : x ⤳ η.val) : x = η.val := by
  apply (hx.antisymm ?_).eq
  apply specializes_iff_closure_subset.mpr
  exact η.property.2 (isIrreducible_singleton.closure) hx.closure_subset

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_spec_subsingleton {X : Scheme.{u}}
    (η : {x : X // x ∈ genericPoints X}) :
    Subsingleton (Spec (X.presheaf.stalk η.val)) := by
  constructor
  intro p q
  apply (X.fromSpecStalk η.val).isEmbedding.injective
  have h (p : Spec (X.presheaf.stalk η.val)) : X.fromSpecStalk η.val p = η.val := by
    apply generic_generalization_eq η
    exact (Scheme.range_fromSpecStalk (x := η.val)).subset ⟨p, rfl⟩
  exact (h p).trans (h q).symm

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_regular_isUnit {X : Scheme.{u}}
    (η : {x : X // x ∈ genericPoints X}) {a : X.presheaf.stalk η.val}
    (ha : a ∈ nonZeroDivisors (X.presheaf.stalk η.val)) : IsUnit a := by
  let : Subsingleton (PrimeSpectrum (X.presheaf.stalk η.val)) := generic_spec_subsingleton η
  have hm : IsMinimalPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk η.val)) := by
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    intro q hq _
    have he := Subsingleton.elim (⟨q, hq.1⟩ : PrimeSpectrum (X.presheaf.stalk η.val))
      (⟨IsLocalRing.maximalIdeal _, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk η.val))
    exact (congrArg PrimeSpectrum.asIdeal he).ge
  apply IsLocalRing.notMem_maximalIdeal.mp
  exact fun h ↦ notMem_nonZeroDivisors_of_mem_mem_minimalPrimes h hm ha

open CategoryTheory.Limits TopologicalSpace in
private theorem localized_stalk_bijective (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor Ab.{u} η.val).map
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (meromorphicLocalization X M))) := by
  classical
  have hunit (U : X.Opens) (hη : η.val ∈ U) (b : meromorphicDenominators X U) :
      IsUnit (X.presheaf.germ U η.val hη b.val) := by
    apply generic_regular_isUnit η
    exact Submonoid.mem_iInf.mp b.property ⟨η.val, hη⟩
  constructor
  · intro s t hst
    obtain ⟨U, hU, s, rfl⟩ := M.presheaf.exists_germ_eq s
    obtain ⟨V, hV, t, rfl⟩ := M.presheaf.exists_germ_eq t
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply] at hst
    obtain ⟨W, hW, iU, iV, hw⟩ :=
      TopCat.Presheaf.germ_eq (meromorphicPresheaf X M).presheaf η.val hU hV _ _ hst
    change meromorphicRestriction X M iU (LocalizedModule.mk s 1) =
      meromorphicRestriction X M iV (LocalizedModule.mk t 1) at hw
    change meromorphicRestriction X M iU (LocalizedModule.mkLinearMap _ _ s) =
      meromorphicRestriction X M iV (LocalizedModule.mkLinearMap _ _ t) at hw
    rw [meromorphicLocalization_natural, meromorphicLocalization_natural] at hw
    obtain ⟨b, hb⟩ := LocalizedModule.mk_eq.mp hw
    simp only [one_smul, Submonoid.smul_def] at hb
    have hg := congrArg (M.presheaf.germ W η.val hW) hb
    erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val,
      PresheafOfModules.germ_smul (R := X.presheaf) M.val] at hg
    have he := (hunit W hW b).smul_left_cancel.mp hg
    exact (M.presheaf.germ_res_apply iU η.val hW s).symm.trans
      (he.trans (M.presheaf.germ_res_apply iV η.val hW t))
  · intro z
    obtain ⟨U, hU, z, rfl⟩ := TopCat.Presheaf.exists_germ_eq (meromorphicPresheaf X M).presheaf z
    induction z using LocalizedModule.induction_on with
    | h m b =>
      obtain ⟨V, i, hV, hv⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U b.val
        η.val hU (hunit U hU b)
      obtain ⟨v, hv⟩ := hv
      refine ⟨M.presheaf.germ V η.val hV (v⁻¹ • M.presheaf.map i.op m), ?_⟩
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rw [← TopCat.Presheaf.germ_res_apply (meromorphicPresheaf X M).presheaf i η.val hV
        (LocalizedModule.mk m b)]
      apply congrArg (TopCat.Presheaf.germ (meromorphicPresheaf X M).presheaf V η.val hV)
      change LocalizedModule.mk (v⁻¹ • M.presheaf.map i.op m) 1 =
        meromorphicRestriction X M i (LocalizedModule.mk m b)
      change LocalizedModule.mk (v⁻¹ • M.presheaf.map i.op m) 1 =
        (exists_meromorphicRestriction X M i).choose (LocalizedModule.mk m b)
      rw [(exists_meromorphicRestriction X M i).choose_spec]
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, restrictMeromorphicDenominator]
      rw [← hv]
      exact smul_inv_smul v _

open CategoryTheory.Limits TopologicalSpace in
private theorem meromorphic_stalk_bijective (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) :
    Function.Bijective (PresheafOfModules.stalkAddMap (x := η.val)
      (toMeromorphicModule X M).val) := by
  have hu : Function.Bijective (PresheafOfModules.stalkAddMap (x := η.val)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (meromorphicPresheaf X M))) := by
    let t := (TopCat.Presheaf.stalkFunctor Ab.{u} η.val).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
        (meromorphicPresheaf X M).presheaf)
    let : IsIso t := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso η.val Ab.{u} _
    change Function.Bijective t
    exact ConcreteCategory.bijective_of_isIso t
  have he : (toMeromorphicModule X M).val = meromorphicLocalization X M ≫
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (meromorphicPresheaf X M) := by
    exact (SheafOfModules.fullyFaithfulForget X.ringCatSheaf).map_preimage _
  rw [he]
  simp only [PresheafOfModules.stalkAddMap, Functor.map_comp]
  exact hu.comp (localized_stalk_bijective X M η)

open CategoryTheory.Limits TopologicalSpace in
private noncomputable def meromorphicStalkEquiv (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) :
    (meromorphicModule X M).presheaf.stalk η.val ≃+ M.presheaf.stalk η.val :=
  (AddEquiv.ofBijective (PresheafOfModules.stalkAddMap (x := η.val)
    (toMeromorphicModule X M).val) (meromorphic_stalk_bijective X M η)).symm

open CategoryTheory.Limits TopologicalSpace in
private theorem meromorphicStalkEquiv_germ (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (m : Γ(M, U)) :
    meromorphicStalkEquiv X M η ((meromorphicModule X M).presheaf.germ U η.val hη
      ((toMeromorphicModule X M).val.app (op U) m)) = M.presheaf.germ U η.val hη m := by
  apply (meromorphicStalkEquiv X M η).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U η.val hη
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (toMeromorphicModule X M).val) m).symm

open CategoryTheory.Limits TopologicalSpace in
private noncomputable def unitStalkEquiv (X : Scheme.{u}) (x : X) :
    (unit X).presheaf.stalk x ≃+ X.presheaf.stalk x := by
  let e := (preservesColimitIso ((forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u}))
    ((TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf)).symm
  exact e.addCommGroupIsoToAddEquiv

open CategoryTheory.Limits TopologicalSpace in
private theorem unitStalkEquiv_germ (X : Scheme.{u}) (x : X)
    (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    unitStalkEquiv X x ((unit X).presheaf.germ U x hx a) = X.presheaf.germ U x hx a := by
  exact ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} Ab.{u})
      ((OpenNhds.inclusion x).op ⋙ X.presheaf) (op ⟨U, hx⟩)) a

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_preimage_eq_top {X : Scheme.{u}}
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) :
    X.fromSpecStalk η.val ⁻¹ᵁ U = ⊤ := by
  let : Subsingleton (Spec (X.presheaf.stalk η.val)) := generic_spec_subsingleton η
  apply top_unique
  intro p _
  change X.fromSpecStalk η.val p ∈ U
  rw [Subsingleton.elim p (IsLocalRing.closedPoint (X.presheaf.stalk η.val)),
    Scheme.fromSpecStalk_closedPoint]
  exact hη

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_preimage_eq_bot {X : Scheme.{u}}
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∉ U) :
    X.fromSpecStalk η.val ⁻¹ᵁ U = ⊥ := by
  let : Subsingleton (Spec (X.presheaf.stalk η.val)) := generic_spec_subsingleton η
  apply bot_unique
  intro p hp
  change X.fromSpecStalk η.val p ∈ U at hp
  rw [Subsingleton.elim p (IsLocalRing.closedPoint (X.presheaf.stalk η.val)),
    Scheme.fromSpecStalk_closedPoint] at hp
  exact hη hp

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_toOpen_bijective (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) :
    Function.Bijective (tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val)
      (M.presheaf.stalk η.val)) (X.fromSpecStalk η.val ⁻¹ᵁ U)) := by
  rw [generic_preimage_eq_top η U hη]
  exact ConcreteCategory.bijective_of_isIso _

open CategoryTheory.Limits TopologicalSpace in
private noncomputable abbrev genericFactor (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) : X.Modules :=
  (pushforward (X.fromSpecStalk η.val)).obj
    (tilde (ModuleCat.of (X.presheaf.stalk η.val) (M.presheaf.stalk η.val)))

open CategoryTheory.Limits TopologicalSpace in
private noncomputable def genericFiberEquiv (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U) :
    M.presheaf.stalk η.val ≃+ Γ(genericFactor X M η, U) :=
  AddEquiv.ofBijective (tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val)
    (M.presheaf.stalk η.val)) (X.fromSpecStalk η.val ⁻¹ᵁ U)).hom.toAddMonoidHom
      (generic_toOpen_bijective X M η U hη)

open CategoryTheory.Limits TopologicalSpace in
private noncomputable def genericCoordinate (X : Scheme.{u}) (M : X.Modules)
    (e : meromorphicModule X M ≅ ∏ᶜ genericFactor X M)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (s : Γ(meromorphicModule X M, U)) : M.presheaf.stalk η.val :=
  (genericFiberEquiv X M η U hη).symm
    ((e.hom ≫ Pi.π _ η).val.app (op U) s)

open CategoryTheory.Limits TopologicalSpace in
private theorem genericCoordinate_res (X : Scheme.{u}) (M : X.Modules)
    (e : meromorphicModule X M ≅ ∏ᶜ genericFactor X M)
    (η : {x : X // x ∈ genericPoints X}) (U V : X.Opens) (i : V ⟶ U)
    (hV : η.val ∈ V) (hU : η.val ∈ U) (s : Γ(meromorphicModule X M, U)) :
    genericCoordinate X M e η V hV ((meromorphicModule X M).presheaf.map i.op s) =
      genericCoordinate X M e η U hU s := by
  apply (genericFiberEquiv X M η V hV).injective
  simp only [genericCoordinate, AddEquiv.apply_symm_apply]
  have hn := PresheafOfModules.naturality_apply (e.hom ≫ Pi.π _ η).val i.op s
  change _ = _ at hn
  erw [hn]
  have ht := ConcreteCategory.congr_hom
    (tilde.toOpen_res (ModuleCat.of (X.presheaf.stalk η.val)
      (M.presheaf.stalk η.val)) (X.fromSpecStalk η.val ⁻¹ᵁ U)
        (X.fromSpecStalk η.val ⁻¹ᵁ V)
        ((TopologicalSpace.Opens.map (X.fromSpecStalk η.val).base).map i))
    (genericCoordinate X M e η U hU s)
  exact ((ht.symm.trans (congrArg ((genericFactor X M η).presheaf.map i.op)
    ((genericFiberEquiv X M η U hU).apply_symm_apply _)))).symm

open CategoryTheory.Limits TopologicalSpace in
private theorem genericCoordinate_germ (X : Scheme.{u}) (M : X.Modules)
    (e : meromorphicModule X M ≅ ∏ᶜ genericFactor X M)
    (he : ∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
      (m : Γ(M, U)), (toMeromorphicModule X M ≫ e.hom ≫ Pi.π _ η).val.app (op U) m =
        tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (M.presheaf.stalk η.val))
          (X.fromSpecStalk η.val ⁻¹ᵁ U) (M.presheaf.germ U η.val hη m))
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (s : Γ(meromorphicModule X M, U)) :
    genericCoordinate X M e η U hη s =
      meromorphicStalkEquiv X M η ((meromorphicModule X M).presheaf.germ U η.val hη s) := by
  have hord (V : X.Opens) (hV : η.val ∈ V) (m : Γ(M, V)) :
      genericCoordinate X M e η V hV ((toMeromorphicModule X M).val.app (op V) m) =
        M.presheaf.germ V η.val hV m := by
    apply (genericFiberEquiv X M η V hV).injective
    simp only [genericCoordinate, AddEquiv.apply_symm_apply]
    exact he η V hV m
  obtain ⟨z, hz⟩ := (meromorphic_stalk_bijective X M η).2
    ((meromorphicModule X M).presheaf.germ U η.val hη s)
  obtain ⟨V, hV, m, rfl⟩ := M.presheaf.exists_germ_eq z
  have hz' : (meromorphicModule X M).presheaf.germ V η.val hV
      ((toMeromorphicModule X M).val.app (op V) m) =
        (meromorphicModule X M).presheaf.germ U η.val hη s := by
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply V η.val hV
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (toMeromorphicModule X M).val) m).symm.trans hz
  obtain ⟨W, hW, iV, iU, hw⟩ := (meromorphicModule X M).presheaf.germ_eq
    η.val hV hη _ _ hz'
  rw [← genericCoordinate_res X M e η U W iU hW hη, ← hw,
    genericCoordinate_res X M e η V W iV hW hV, hord]
  rw [← hz', meromorphicStalkEquiv_germ]

open CategoryTheory.Limits TopologicalSpace in
private theorem product_sections_bijective (X : Scheme.{u})
    {I : Type u} (F : I → X.Modules) (N : X.Modules) (e : N ≅ ∏ᶜ F) (U : X.Opens) :
    Function.Bijective (fun s : Γ(N, U) ↦
      fun η : I ↦ (e.hom ≫ Pi.π _ η).val.app (op U) s) := by
  let H := SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
    forget (ModuleCat.{u} Γ(X, U))
  have : PreservesLimitsOfShape (Discrete I) H := by
    dsimp [H]
    infer_instance
  let h := isLimitOfHasProductOfPreservesLimit H F
  let i := h.conePointUniqueUpToIso (Types.productLimitCone (fun η ↦ H.obj (F η))).isLimit
  have hi : Function.Bijective (fun s : Γ(∏ᶜ F, U) ↦
      fun η : I ↦ (Pi.π F η).val.app (op U) s) := by
    have hi_fun : (fun s : Γ(∏ᶜ F, U) ↦
        fun η : I ↦ (Pi.π F η).val.app (op U) s) = i.hom := by
      funext s η
      exact (ConcreteCategory.congr_hom
        (h.conePointUniqueUpToIso_hom_comp
          (Types.productLimitCone (fun η ↦ H.obj (F η))).isLimit ⟨η⟩) s).symm
    rw [hi_fun]
    exact i.toEquiv.bijective
  exact hi.comp (ConcreteCategory.bijective_of_isIso (H.map e.hom))

open CategoryTheory.Limits TopologicalSpace in
private theorem genericCoordinate_bijective (X : Scheme.{u}) (M : X.Modules)
    (e : meromorphicModule X M ≅ ∏ᶜ genericFactor X M) (U : X.Opens) :
    Function.Bijective (fun s : Γ(meromorphicModule X M, U) ↦
      fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
        genericCoordinate X M e ⟨η.val, η.property.1⟩ U η.property.2 s) := by
  classical
  have hb := product_sections_bijective X (genericFactor X M) _ e U
  have hout (η : {x : X // x ∈ genericPoints X}) (hη : η.val ∉ U)
      (s t : Γ(genericFactor X M η, U)) : s = t := by
    apply TopCat.Presheaf.section_ext
      ((SheafOfModules.toSheaf _).obj
        (tilde (ModuleCat.of (X.presheaf.stalk η.val) (M.presheaf.stalk η.val))))
    intro p hp
    rw [generic_preimage_eq_bot η U hη] at hp
    exact False.elim hp
  constructor
  · intro s t hst
    apply hb.1
    funext η
    by_cases hη : η.val ∈ U
    · have h := congrFun hst ⟨η.val, η.property, hη⟩
      exact (genericFiberEquiv X M η U hη).symm.injective h
    · exact hout η hη _ _
  · intro t
    let z : ∀ η : {x : X // x ∈ genericPoints X}, Γ(genericFactor X M η, U) :=
      fun η ↦ if hη : η.val ∈ U then
        genericFiberEquiv X M η U hη (t ⟨η.val, η.property, hη⟩) else 0
    obtain ⟨s, hs⟩ := hb.2 z
    refine ⟨s, ?_⟩
    funext η
    have h := congrFun hs ⟨η.val, η.property.1⟩
    dsimp only [z] at h
    rw [dif_pos η.property.2] at h
    exact congrArg (genericFiberEquiv X M ⟨η.val, η.property.1⟩ U η.property.2).symm h
      |>.trans ((genericFiberEquiv X M ⟨η.val, η.property.1⟩ U η.property.2).symm_apply_apply _)

open CategoryTheory.Limits TopologicalSpace in
private theorem meromorphicStalkEquiv_smul (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X})
    (r : X.presheaf.stalk η.val) (z : (meromorphicModule X M).presheaf.stalk η.val) :
    meromorphicStalkEquiv X M η (r • z) = r • meromorphicStalkEquiv X M η z := by
  apply (meromorphicStalkEquiv X M η).symm.injective
  simp only [AddEquiv.symm_apply_apply]
  change r • z = PresheafOfModules.stalkAddMap (toMeromorphicModule X M).val
    (r • meromorphicStalkEquiv X M η z)
  have hlin (m : M.presheaf.stalk η.val) :
      PresheafOfModules.stalkAddMap (toMeromorphicModule X M).val (r • m) =
        r • PresheafOfModules.stalkAddMap (toMeromorphicModule X M).val m := by
    obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hV, m, rfl⟩ := M.presheaf.exists_germ_eq m
    have hx : η.val ∈ U ⊓ V := ⟨hU, hV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) η.val hx a,
      ← M.presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) η.val hx m]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) M.val]
    dsimp only [PresheafOfModules.stalkAddMap]
    erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change TopCat.Presheaf.germ (meromorphicModule X M).presheaf _ η.val hx
      (((toMeromorphicModule X M).val.app _) (_ • _)) = _
    rw [LinearMap.map_smul]
    exact PresheafOfModules.germ_smul (R := X.presheaf) (meromorphicModule X M).val _ _ _ _ _
  rw [hlin]
  congr 1
  exact ((meromorphicStalkEquiv X M η).symm_apply_apply z).symm

open CategoryTheory.Limits TopologicalSpace in
private theorem fraction_cancel (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) (b : meromorphicDenominators X U) :
    b.val • meromorphicFraction X M U (LocalizedModule.mk m b) =
      (toMeromorphicModule X M).val.app (op U) m := by
  rw [← (meromorphicFraction X M U).map_smul]
  have hf : b.val • LocalizedModule.mk m b = LocalizedModule.mkLinearMap _ _ m := by
    change b.val • LocalizedModule.mk m b = LocalizedModule.mk m 1
    simpa only [LocalizedModule.smul'_mk, Submonoid.smul_def] using
      LocalizedModule.mk_cancel b m
  rw [hf]
  rfl

open CategoryTheory.Limits TopologicalSpace in
private theorem fraction_germ_cancel (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
    (m : Γ(M, U)) (b : meromorphicDenominators X U) :
    X.presheaf.germ U η.val hη b.val • meromorphicStalkEquiv X M η
      ((meromorphicModule X M).presheaf.germ U η.val hη
        (meromorphicFraction X M U (LocalizedModule.mk m b))) = M.presheaf.germ U η.val hη m := by
  rw [← meromorphicStalkEquiv_smul]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) (meromorphicModule X M).val]
  rw [fraction_cancel]
  exact meromorphicStalkEquiv_germ X M η U hη m

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_germs_bijective (X : Scheme.{u}) (M : X.Modules)
    (e : meromorphicModule X M ≅ ∏ᶜ genericFactor X M)
    (he : ∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
      (m : Γ(M, U)), (toMeromorphicModule X M ≫ e.hom ≫ Pi.π _ η).val.app (op U) m =
        tilde.toOpen (ModuleCat.of (X.presheaf.stalk η.val) (M.presheaf.stalk η.val))
          (X.fromSpecStalk η.val ⁻¹ᵁ U) (M.presheaf.germ U η.val hη m)) (U : X.Opens) :
    Function.Bijective (fun s : Γ(meromorphicModule X M, U) ↦
      fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
        meromorphicStalkEquiv X M ⟨η.val, η.property.1⟩
          ((meromorphicModule X M).presheaf.germ U η.val η.property.2 s)) := by
  have hb := genericCoordinate_bijective X M e U
  simpa only [genericCoordinate_germ X M e he] using hb

open CategoryTheory.Limits TopologicalSpace in
private theorem generic_germ_res (X : Scheme.{u}) (M : X.Modules)
    (η : {x : X // x ∈ genericPoints X}) (U V : X.Opens) (i : V ⟶ U)
    (hV : η.val ∈ V) (hU : η.val ∈ U) (s : Γ(meromorphicModule X M, U)) :
    meromorphicStalkEquiv X M η ((meromorphicModule X M).presheaf.germ V η.val hV
      ((meromorphicModule X M).presheaf.map i.op s)) =
    meromorphicStalkEquiv X M η ((meromorphicModule X M).presheaf.germ U η.val hU s) := by
  rw [TopCat.Presheaf.germ_res_apply]

open CategoryTheory.Limits TopologicalSpace in
private theorem unitStalkEquiv_smul (X : Scheme.{u}) (x : X)
    (r : X.presheaf.stalk x) (s : (unit X).presheaf.stalk x) :
    unitStalkEquiv X x (r • s) = r * unitStalkEquiv X x s := by
  obtain ⟨U, hU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hV, b, rfl⟩ := (unit X).presheaf.exists_germ_eq s
  have hx : x ∈ U ⊓ V := ⟨hU, hV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left : U ⊓ V ⟶ U) x hx a,
    ← (unit X).presheaf.germ_res_apply (homOfLE inf_le_right : U ⊓ V ⟶ V) x hx b]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf) (unit X).val]
  erw [unitStalkEquiv_germ]
  rw [unitStalkEquiv_germ, ← map_mul]
  rfl

/-- The canonical generic-stalk identifications give bijections on sections, compatible with
restriction and multiplication. Source: Stacks, Tag 0EMH, with the generic-stalk computation
in Tag 0EMF (blueprint: lem-sc-meromorphic-sheaf-generic-product).

Proof: (1) By lem-sc-ass-weakass-locally-noetherian, no embedded associated points means
that all weakly associated points are generic. A quasi-compact open has a finite affine
Noetherian cover; lem-weil-pbc-noetherian-open-subscheme-noetherian and
lem-sc-noetherian-finite-irreducible-components give finitely many components. Apply
lem-sc-meromorphic-weakass-generic-product (Tag 0EMF).
(2) A generic local ring has dimension zero and is Artinian. Every nonunit is nilpotent,
hence a zero-divisor, so localization at non-zero-divisors fixes it. Sheafification preserves
stalks and localization commutes with their filtered colimits. Evaluating the product on U
retains exactly the generic points in U, and the comparison is the germ map.
(3) For invertible L, the same product theorem gives the module comparison. Stalks commute
with tensor products (Modules Tag 01CE), yielding K(L)_η = O_η tensor L_η = L_η.
The stalk action rule of def-weil-pbc-module-stalk sends a product to the product of germs;
the fraction rule (a/b)(m/c) = (am)/(bc) and the germ restriction rule give the two
compatibilities below. The recorded meromorphicModule_tensor_iso identifies the localized
module used here with K_X tensor L. -/
theorem meromorphicSheaf_generic_product
    {X : Scheme.{u}} [IsLocallyNoetherian X]
    (h_no_embedded : ∀ x : X,
      (∃ a : X.presheaf.stalk x, IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)).colon {a}) →
      x ∈ genericPoints X)
    (L : X.Modules) [L.IsInvertible] :
    letI (x : X) : Module (X.presheaf.stalk x) (L.presheaf.stalk x) :=
      inferInstanceAs (Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) L.val.presheaf x))
    ∃ (eK : ∀ η : {x : X // x ∈ genericPoints X},
        (meromorphicModule X (unit X)).presheaf.stalk η.val ≃+ X.presheaf.stalk η.val)
      (eL : ∀ η : {x : X // x ∈ genericPoints X},
        (meromorphicModule X L).presheaf.stalk η.val ≃+ L.presheaf.stalk η.val)
      (mul : ∀ U : X.Opens, Γ(meromorphicModule X (unit X), U) →
        Γ(meromorphicModule X L, U) → Γ(meromorphicModule X L, U)),
      (∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
        (a : Γ(X, U)),
        eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hη
          ((toMeromorphicModule X (unit X)).val.app (op U) a)) =
            X.presheaf.germ U η.val hη a) ∧
      (∀ (η : {x : X // x ∈ genericPoints X}) (U : X.Opens) (hη : η.val ∈ U)
        (m : Γ(L, U)),
        eL η ((meromorphicModule X L).presheaf.germ U η.val hη
          ((toMeromorphicModule X L).val.app (op U) m)) = L.presheaf.germ U η.val hη m) ∧
      (∀ U : X.Opens, Function.Bijective
        (fun s : Γ(meromorphicModule X (unit X), U) ↦
          fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
            eK ⟨η.val, η.property.1⟩
              ((meromorphicModule X (unit X)).presheaf.germ U η.val η.property.2 s))) ∧
      (∀ U : X.Opens, Function.Bijective
        (fun t : Γ(meromorphicModule X L, U) ↦
          fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
            eL ⟨η.val, η.property.1⟩
              ((meromorphicModule X L).presheaf.germ U η.val η.property.2 t))) ∧
      (∀ (U V : X.Opens) (i : V ⟶ U) (η : {x : X // x ∈ genericPoints X})
        (hV : η.val ∈ V) (hU : η.val ∈ U) (s : Γ(meromorphicModule X (unit X), U))
        (t : Γ(meromorphicModule X L, U)),
        eK η ((meromorphicModule X (unit X)).presheaf.germ V η.val hV
            ((meromorphicModule X (unit X)).presheaf.map i.op s)) =
          eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hU s) ∧
        eL η ((meromorphicModule X L).presheaf.germ V η.val hV
            ((meromorphicModule X L).presheaf.map i.op t)) =
          eL η ((meromorphicModule X L).presheaf.germ U η.val hU t)) ∧
      (∀ (U : X.Opens) (a : Γ(X, U)) (m : Γ(L, U))
        (b c : meromorphicDenominators X U),
        mul U (meromorphicFraction X (unit X) U (LocalizedModule.mk a b))
          (meromorphicFraction X L U (LocalizedModule.mk m c)) =
            meromorphicFraction X L U (LocalizedModule.mk (a • m) (b * c))) ∧
      (∀ (U V : X.Opens) (i : V ⟶ U) (s : Γ(meromorphicModule X (unit X), U))
        (t : Γ(meromorphicModule X L, U)),
        (meromorphicModule X L).presheaf.map i.op (mul U s t) =
          mul V ((meromorphicModule X (unit X)).presheaf.map i.op s)
            ((meromorphicModule X L).presheaf.map i.op t)) ∧
      (∀ (U : X.Opens) (η : {x : X // x ∈ genericPoints X}) (hη : η.val ∈ U)
        (s : Γ(meromorphicModule X (unit X), U)) (t : Γ(meromorphicModule X L, U)),
        eL η ((meromorphicModule X L).presheaf.germ U η.val hη (mul U s t)) =
          eK η ((meromorphicModule X (unit X)).presheaf.germ U η.val hη s) •
            eL η ((meromorphicModule X L).presheaf.germ U η.val hη t)) := by
  classical
  have hweak : ∀ x : X, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∈
      Ideal.WeakAss (X.presheaf.stalk x) → x ∈ genericPoints X := by
    intro x hx
    apply h_no_embedded x
    have h := Scheme.associatedPoints_eq_weaklyAssociatedPoints X
    exact Set.ext_iff.mp h x |>.mpr hx
  have hfinite : ∀ U : X.Opens, IsCompact (U : Set X) →
      (irreducibleComponents U).Finite := by
    intro U hU
    let : CompactSpace U := isCompact_iff_compactSpace.mp hU
    let : IsNoetherian U.toScheme := ⟨⟩
    let : TopologicalSpace.NoetherianSpace U :=
      inferInstanceAs (TopologicalSpace.NoetherianSpace U.toScheme)
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  obtain ⟨e, he⟩ := (meromorphicModule_generic_product X L hweak hfinite).2.2
  let : (unit X).IsQuasicoherent := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
  obtain ⟨e₀, he₀⟩ := (meromorphicModule_generic_product X (unit X) hweak hfinite).2.2
  let eL := meromorphicStalkEquiv X L
  let eK := fun η ↦ (meromorphicStalkEquiv X (unit X) η).trans (unitStalkEquiv X η.val)
  let cL := fun (U : X.Opens) (t : Γ(meromorphicModule X L, U))
    (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) ↦
      eL ⟨η.val, η.property.1⟩
        ((meromorphicModule X L).presheaf.germ U η.val η.property.2 t)
  let cK := fun (U : X.Opens) (s : Γ(meromorphicModule X (unit X), U))
    (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) ↦
      eK ⟨η.val, η.property.1⟩
        ((meromorphicModule X (unit X)).presheaf.germ U η.val η.property.2 s)
  have bL : ∀ U, Function.Bijective (cL U) := generic_germs_bijective X L e he
  have bK : ∀ U, Function.Bijective (cK U) := by
    intro U
    exact (Equiv.piCongrRight (fun η : {x : X // x ∈ genericPoints X ∧ x ∈ U} ↦
      (unitStalkEquiv X η.val).toEquiv)).bijective.comp
        (generic_germs_bijective X (unit X) e₀ he₀ U)
  let invL := fun U ↦ Equiv.ofBijective (cL U) (bL U)
  let mul := fun U s t ↦ (invL U).symm (fun η ↦ cK U s η • cL U t η)
  have hmul (U : X.Opens) (s : Γ(meromorphicModule X (unit X), U))
      (t : Γ(meromorphicModule X L, U))
      (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) :
      cL U (mul U s t) η = cK U s η • cL U t η :=
    congrFun ((invL U).apply_symm_apply _) η
  refine ⟨eK, eL, mul, ?_, ?_, bK, bL, ?_, ?_, ?_, ?_⟩
  · intro η U hη a
    exact (congrArg (unitStalkEquiv X η.val)
      (meromorphicStalkEquiv_germ X (unit X) η U hη a)).trans
        (unitStalkEquiv_germ X η.val U hη a)
  · exact meromorphicStalkEquiv_germ X L
  · intro U V i η hV hU s t
    constructor
    · exact congrArg (unitStalkEquiv X η.val)
        (generic_germ_res X (unit X) η U V i hV hU s)
    · exact generic_germ_res X L η U V i hV hU t
  · intro U a m b c
    apply (bL U).1
    funext η
    rw [hmul]
    let ξ : {x : X // x ∈ genericPoints X} := ⟨η.val, η.property.1⟩
    let g := X.presheaf.germ U η.val η.property.2
    have hB : IsUnit (g b.val) := generic_regular_isUnit ξ
      (Submonoid.mem_iInf.mp b.property ⟨η.val, η.property.2⟩)
    have hC : IsUnit (g c.val) := generic_regular_isUnit ξ
      (Submonoid.mem_iInf.mp c.property ⟨η.val, η.property.2⟩)
    have hb := congrArg (unitStalkEquiv X η.val)
      (fraction_germ_cancel X (unit X) ξ U η.property.2 a b)
    rw [unitStalkEquiv_smul, unitStalkEquiv_germ] at hb
    change g b.val * cK U
      (meromorphicFraction X (unit X) U (LocalizedModule.mk a b)) η = g a at hb
    have hc := fraction_germ_cancel X L ξ U η.property.2 m c
    change g c.val • cL U (meromorphicFraction X L U (LocalizedModule.mk m c)) η =
      L.presheaf.germ U η.val η.property.2 m at hc
    have hbc := fraction_germ_cancel X L ξ U η.property.2 (a • m) (b * c)
    change g (b.val * c.val) • cL U
      (meromorphicFraction X L U (LocalizedModule.mk (a • m) (b * c))) η = _ at hbc
    rw [map_mul] at hbc
    erw [PresheafOfModules.germ_smul (R := X.presheaf) L.val] at hbc
    apply ((hB.mul hC).smul_left_cancel).mp
    calc
      (g b.val * g c.val) •
          (cK U (meromorphicFraction X (unit X) U (LocalizedModule.mk a b)) η •
            cL U (meromorphicFraction X L U (LocalizedModule.mk m c)) η) =
          (g b.val * cK U
            (meromorphicFraction X (unit X) U (LocalizedModule.mk a b)) η) •
            (g c.val • cL U
              (meromorphicFraction X L U (LocalizedModule.mk m c)) η) := by
        simp only [smul_smul]
        congr 1
        ring
      _ = g a • L.presheaf.germ U η.val η.property.2 m := by rw [hb, hc]
      _ = _ := hbc.symm
  · intro U V i s t
    apply (bL V).1
    funext η
    change eL ⟨η.val, η.property.1⟩
      ((meromorphicModule X L).presheaf.germ V η.val η.property.2
      ((meromorphicModule X L).presheaf.map i.op (mul U s t))) = _
    rw [TopCat.Presheaf.germ_res_apply]
    have hm := hmul U s t ⟨η.val, η.property.1, i.le η.property.2⟩
    rw [hmul]
    exact hm.trans (congrArg₂ (· • ·)
      (congrArg (unitStalkEquiv X η.val)
        (generic_germ_res X (unit X) ⟨η.val, η.property.1⟩ U V i
          η.property.2 (i.le η.property.2) s)).symm
      (generic_germ_res X L ⟨η.val, η.property.1⟩ U V i
        η.property.2 (i.le η.property.2) t).symm)
  · intro U η hη s t
    exact hmul U s t ⟨η.val, η.property, hη⟩

end AlgebraicGeometry
