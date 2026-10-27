/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module
public import Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import all Sheaf.CategoryTheory.RingedToposKFlatPullback
import all Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import all Sheaf.CategoryTheory.GeometricModuleTransport
import all Sheaf.CategoryTheory.GeometricModuleConstruction
import Sheaf.CategoryTheory.AlgebraicInverseImageOfTransport
/-!
# Underlying inverse image for an isomorphic structural ring map

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3
(blueprint: lem-pur-cartesian-module-pullback-underlying).

The module adjunction is normalized by the given geometric adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules
open SheafOfModules.GeometricConstruction
namespace CategoryTheory
private theorem cartesian_image
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (base A) (base B)) [IsIso f.ringMap] :
    ∃ I : AlgebraicInverseImage f.inverse B A, I.ringUnderlying.hom = f.ringMap := by
  let := f.leftExact
  let e := (asIso f.ringMap).symm
  have ha : f.inverse.map (radd B) =
      prodComparison f.inverse (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ radd A ≫ e.hom := by
    apply (cancel_mono f.ringMap).mp
    simp only [Category.assoc, e, Iso.symm_hom, Iso.symm_inv, asIso_hom,
      asIso_inv, IsIso.inv_hom_id, Category.comp_id]
    exact binary_of_graph f.inverse f.ringMap f.ringMap f.ringMap (radd B) (radd A)
      (fun U x y ↦ @Add.add (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Add.add (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) f.ring_add
  have hm : f.inverse.map (rmul B) =
      prodComparison f.inverse (rset B) (rset B) ≫
        prod.map e.inv e.inv ≫ rmul A ≫ e.hom := by
    apply (cancel_mono f.ringMap).mp
    simp only [Category.assoc, e, Iso.symm_hom, Iso.symm_inv, asIso_hom,
      asIso_inv, IsIso.inv_hom_id, Category.comp_id]
    exact binary_of_graph f.inverse f.ringMap f.ringMap f.ringMap (rmul B) (rmul A)
      (fun U x y ↦ @Mul.mul (B.obj.obj U) inferInstance x y)
      (fun U x y ↦ @Mul.mul (A.obj.obj U) inferInstance x y)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) f.ring_mul
  obtain ⟨L, P, eL, eP, hL, hP⟩ := geometric_module_construction K J
    f.inverse f.direct f.adj B A A e (radd B) (rmul B) (radd A) (rmul A)
    ⟨(fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), (fun _ _ ↦ rfl), ha, hm⟩ (𝟙 A)
  obtain ⟨I, hI, hr, hu⟩ := algebraicInverseImage_of_module_transport K J
    f.inverse B A e L eL hL
  exact ⟨I, congrArg Iso.hom hr⟩
set_option maxHeartbeats 800000 in
-- The module Hom normalization expands the two transported scalar operations.
private theorem image_adjunction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {A : Sheaf J CommRingCat.{u}} {B : Sheaf K CommRingCat.{u}}
    (f : RingedToposMorphism (base A) (base B))
    (I : AlgebraicInverseImage f.inverse B A) (hI : I.ringUnderlying.hom = f.ringMap) :
    ∃ adj : I.modules ⊣ f.modules,
      ∀ M H (a : I.modules.obj M ⟶ H),
        (mset B).map (adj.homEquiv M H a) ≫ f.underlying.hom.app H =
          f.adj.homEquiv _ _ (I.moduleUnderlying.inv.app M ≫ (mset A).map a) := by
  let := f.leftExact
  let : PreservesLimits f.direct := f.adj.rightAdjoint_preservesLimits
  let eR := I.ringUnderlying.symm
  let eI := I.moduleUnderlying
  let eP := f.underlying
  have hec : eR.inv ≫ 𝟙 (rset A) = f.ringMap := by
    simpa only [eR, Iso.symm_inv, Category.comp_id] using hI
  let E : ∀ M H, ((mset A).obj (I.modules.obj M) ⟶ (mset A).obj H) ≃
      ((mset B).obj M ⟶ (mset B).obj (f.modules.obj H)) :=
    fun M H ↦ mateIsoEquiv f.adj (eI.app M) (eP.app H)
  have hImage M H (α : (mset A).obj (I.modules.obj M) ⟶ (mset A).obj H) :
      (∃ a : I.modules.obj M ⟶ H, (mset A).map a = α) ↔
        ∃ b : M ⟶ f.modules.obj H, (mset B).map b = E M H α := by
    have hLA : f.inverse.map (madd B M) =
        prodComparison f.inverse ((mset B).obj M) ((mset B).obj M) ≫
          prod.map (eI.inv.app M) (eI.inv.app M) ≫ madd A (I.modules.obj M) ≫
            eI.hom.app M := by
      apply (cancel_mono (eI.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse (eI.inv.app M) (eI.inv.app M) (eI.inv.app M)
        (madd B M) (madd A (I.modules.obj M))
        (fun U x y ↦ @Add.add (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @Add.add ((I.modules.obj M).val.obj U) inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T x y z hz U t ↦ I.moduleAdd M T x y z hz U t)
    have hLS : f.inverse.map (msmul B M) =
        prodComparison f.inverse (rset B) ((mset B).obj M) ≫
          prod.map eR.inv (eI.inv.app M) ≫ msmul A (I.modules.obj M) ≫ eI.hom.app M := by
      apply (cancel_mono (eI.inv.app M)).mp
      simp only [Category.assoc, Iso.hom_inv_id_app]
      exact binary_of_graph f.inverse eR.inv (eI.inv.app M) (eI.inv.app M)
        (msmul B M) (msmul A (I.modules.obj M))
        (fun U x y ↦ @SMul.smul (B.obj.obj U) (M.val.obj U) inferInstance x y)
        (fun U x y ↦ @SMul.smul (A.obj.obj U) ((I.modules.obj M).val.obj U)
          inferInstance x y)
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
        (fun T a x z hz U t ↦ I.moduleSMul M T a x z hz U t)
    have hRightAdd := (h4_supplied_operations f H).1
    have hRightSmul := (h4_supplied_operations f H).2
    rw [← hec] at hRightSmul
    have hm : f.adj.homEquiv _ _ (eI.inv.app M ≫ α) = E M H α ≫ eP.hom.app H :=
      mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) α
    have hAdd := binary_mate_iso_iff f.adj (eI.app M) (eI.app M) (eI.app M)
      (eP.hom.app H) (eP.hom.app H) (eP.app H) (madd B M)
      (madd A (I.modules.obj M)) (madd A H) (madd B (f.modules.obj H))
      hLA hRightAdd α α α (E M H α) (E M H α) (E M H α) hm hm hm
    have hSmul := binary_mate_iso_iff f.adj eR (eI.app M) (eI.app M)
      (f.adj.homEquiv _ _ (eR.inv ≫ (𝟙 (rset A))))
      (eP.hom.app H) (eP.app H) (msmul B M) (msmul A (I.modules.obj M))
      (msmul A H) (msmul B (f.modules.obj H)) hLS hRightSmul
      ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map (𝟙 A)) α α
      (𝟙 (rset B)) (E M H α) (E M H α)
      (by exact (Category.id_comp _).symm) hm hm
    have hSame := linear_iff (𝟙 B) M (f.modules.obj H)
      (madd B M) (madd B (f.modules.obj H)) (msmul B M) (msmul B (f.modules.obj H))
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (E M H α)
    exact (linear_iff (𝟙 A) (I.modules.obj M) H (madd A (I.modules.obj M)) (madd A H)
      (msmul A (I.modules.obj M)) (msmul A H)
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) α).trans
        ((and_congr hAdd hSmul).trans hSame.symm)
  let B' : ∀ M H, (I.modules.obj M ⟶ H) ≃ (M ⟶ f.modules.obj H) :=
    fun M H ↦ restrictHomEquiv (mset A) (mset B) (E M H) (hImage M H)
  have hB M H a : (mset B).map (B' M H a) ≫ eP.hom.app H =
      f.adj.homEquiv _ _ (eI.inv.app M ≫ (mset A).map a) := by
    rw [restrictHomEquiv_map]
    exact (mateIsoEquiv_equation f.adj (eI.app M) (eP.app H) _).symm
  have hBL {M N} (a : M ⟶ N) H b :
      B' M H (I.modules.map a ≫ b) = a ≫ B' N H b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H)).mp
    rw [hB, (mset B).map_comp, Category.assoc, hB, (mset A).map_comp]
    have hn : eI.inv.app M ≫ (mset A).map (I.modules.map a) =
        f.inverse.map ((mset B).map a) ≫ eI.inv.app N := (eI.inv.naturality a).symm
    rw [← Category.assoc, hn, Category.assoc, f.adj.homEquiv_naturality_left]
  have hBR M {H H'} a (b : H ⟶ H') :
      B' M H' (a ≫ b) = B' M H a ≫ f.modules.map b := by
    apply (mset B).map_injective
    apply (cancel_mono (eP.hom.app H')).mp
    rw [hB, (mset B).map_comp, Category.assoc]
    have hn : (mset B).map (f.modules.map b) ≫ eP.hom.app H' =
        eP.hom.app H ≫ f.direct.map ((mset A).map b) := eP.hom.naturality b
    rw [hn, ← Category.assoc, hB, (mset A).map_comp]
    change f.adj.homEquiv _ _ (eI.inv.app M ≫
      ((mset A).map a ≫ (mset A).map b)) = _
    rw [← Category.assoc, f.adj.homEquiv_naturality_right]
  let adj : I.modules ⊣ f.modules := Adjunction.mkOfHomEquiv {
    homEquiv := B'
    homEquiv_naturality_left_symm := by
      intro M N H a b
      apply (B' M H).injective
      rw [Equiv.apply_symm_apply, hBL, Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro M H H' a b
      exact hBR M a b }
  refine ⟨adj, ?_⟩
  intro M H a
  simpa only [adj, Adjunction.mkOfHomEquiv_homEquiv] using hB M H a
private theorem cartesian_pull_underlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (A : Sheaf J CommRingCat.{u}) (B : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (base A) (base B)) [IsIso f.ringMap]
    (L : ringedSiteModules.{u} (base B) ⥤ ringedSiteModules.{u} (base A))
    (adj : L ⊣ f.modules) :
    ∃ e : L ⋙ mset A ≅ mset B ⋙ f.inverse,
      ∀ M H (a : L.obj M ⟶ H),
        (mset B).map (adj.homEquiv M H a) ≫ f.underlying.hom.app H =
          f.adj.homEquiv _ _ (e.inv.app M ≫ (mset A).map a) := by
  obtain ⟨I, hr⟩ := cartesian_image A B f
  obtain ⟨adjI, hI⟩ := image_adjunction f I hr
  let i := adj.leftAdjointUniq adjI
  let e := Functor.isoWhiskerRight i (mset A) ≪≫ I.moduleUnderlying
  refine ⟨e, ?_⟩
  intro M H a
  have h := hI M H (i.inv.app M ≫ a)
  have hi : adjI.homEquiv M H (i.inv.app M ≫ a) = adj.homEquiv M H a := by
    simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    have hu : adjI.unit.app M ≫ f.modules.map (i.inv.app M) = adj.unit.app M := by
      exact Adjunction.unit_leftAdjointUniq_hom_app adjI adj M
    rw [hu]
  rw [hi] at h
  simpa only [e, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc] using h
/-- When the structural ring map is invertible, any module left adjoint has the
underlying geometric inverse image, compatibly with the specified Hom equivalences.

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3 (module inverse image).
(blueprint: lem-pur-cartesian-module-pullback-underlying).
Proof: transport the additive and scalar operations through the structural ring
isomorphism to construct the algebraic inverse image. Its module adjunction is
induced from the geometric Hom equivalence. Uniqueness of left adjoints compares
this construction with the supplied left adjoint; its unit identity gives the
stated Hom normalization. -/
theorem cartesianModulePullbackUnderlying
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {R : Sheaf K RingCat.{u}} {S : Sheaf L RingCat.{u}}
    (hR : ∀ U (a b : R.obj.obj U), a * b = b * a)
    (hS : ∀ U (a b : S.obj.obj U), a * b = b * a)
    (f : RingedToposMorphism R S) [IsIso f.ringMap]
    (P : ringedSiteModules.{u} S ⥤ ringedSiteModules.{u} R) (adj : P ⊣ f.modules) :
    ∃ e : P ⋙ diagramCoefficientUnderlying R ≅ diagramCoefficientUnderlying S ⋙ f.inverse,
      ∀ M H (a : P.obj M ⟶ H),
        (diagramCoefficientUnderlying S).map (adj.homEquiv M H a) ≫ f.underlying.hom.app H =
          f.adj.homEquiv _ _ (e.inv.app M ≫ (diagramCoefficientUnderlying R).map a) := by
  obtain ⟨R', hr⟩ := coefficientCommRingSheaf R hR
  obtain ⟨S', hs⟩ := coefficientCommRingSheaf S hS
  subst R
  subst S
  exact cartesian_pull_underlying R' S' f P adj
end CategoryTheory
