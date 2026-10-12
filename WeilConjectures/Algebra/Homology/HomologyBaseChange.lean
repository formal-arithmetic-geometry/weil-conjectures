/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.FlatComplexBaseChange
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The base change map on homology

For a short complex `S : X₁ ⟶ X₂ ⟶ X₃` of `A`-modules and an `A`-algebra `B`, the classes
`[z] ↦ [1 ⊗ z]` of cycles define the **base change map** on homology
`B ⊗[A] H(S) ⟶ H(B ⊗[A] S)` (`CategoryTheory.ShortComplex.homologyBaseChange`). It is natural in
`S` (`CategoryTheory.ShortComplex.homologyBaseChange_naturality`), and it is bijective as soon as
tensoring with `B` preserves the left exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ X₃`
(`CategoryTheory.ShortComplex.bijective_homologyBaseChange_of_exact`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace CategoryTheory.ShortComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
  (S : ShortComplex (ModuleCat.{u} A))

/-- The base change `S_B = B ⊗[A] S` of a short complex of `A`-modules. -/
noncomputable abbrev baseChange : ShortComplex (ModuleCat.{u} B) :=
  S.map (ModuleCat.baseChange A B)

/-- The cycles `ker (1 ⊗ g)` of the base change, as a submodule of `B ⊗[A] X₂`. -/
noncomputable abbrev cyclesBaseChange : Submodule B (B ⊗[A] S.X₂) :=
  LinearMap.ker (S.g.hom.baseChange B)

/-- The boundaries of the base change, as a submodule of its cycles. -/
noncomputable abbrev boundariesBaseChange : Submodule B (S.cyclesBaseChange B) :=
  LinearMap.range ((S.f.hom.baseChange B).codRestrict (S.cyclesBaseChange B) fun x ↦
    congr($((S.baseChange B).zero).hom x))

/-- The map `z ↦ 1 ⊗ z` from the cycles of `S` to the cycles of `B ⊗[A] S`. -/
noncomputable def baseChangeCycles :
    LinearMap.ker S.g.hom →ₗ[A] S.cyclesBaseChange B where
  toFun z := ⟨(1 : B) ⊗ₜ (z : S.X₂), by
    rw [LinearMap.mem_ker, LinearMap.baseChange_tmul, LinearMap.mem_ker.1 z.2, tmul_zero]⟩
  map_add' x y := Subtype.ext (tmul_add _ _ _)
  map_smul' a x := Subtype.ext (tmul_smul a (1 : B) (x : S.X₂))

@[simp]
lemma baseChangeCycles_apply_coe (z : LinearMap.ker S.g.hom) :
    (S.baseChangeCycles B z : B ⊗[A] S.X₂) = (1 : B) ⊗ₜ (z : S.X₂) :=
  rfl

lemma baseChangeCycles_mem (x : S.X₁) :
    S.baseChangeCycles B (S.moduleCatToCycles x) ∈ S.boundariesBaseChange B :=
  ⟨(1 : B) ⊗ₜ x, Subtype.ext rfl⟩

/-- The base change map on the explicit homology `ker g ⧸ im f`. -/
noncomputable def homologyBaseChangeAux :
    B ⊗[A] (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[B]
      (S.cyclesBaseChange B ⧸ S.boundariesBaseChange B) :=
  LinearMap.liftBaseChange B ((LinearMap.range S.moduleCatToCycles).liftQ
    (((S.boundariesBaseChange B).mkQ.restrictScalars A) ∘ₗ S.baseChangeCycles B) (by
      rintro _ ⟨x, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact S.baseChangeCycles_mem B x))

lemma homologyBaseChangeAux_tmul (b : B) (z : LinearMap.ker S.g.hom) :
    S.homologyBaseChangeAux B (b ⊗ₜ Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (b • S.baseChangeCycles B z) := by
  rw [homologyBaseChangeAux, LinearMap.liftBaseChange_tmul, Submodule.liftQ_apply,
    Submodule.Quotient.mk_smul]
  rfl
/-- **The base change map on homology** `B ⊗[A] H(S) ⟶ H(B ⊗[A] S)`, `b ⊗ [z] ↦ [b ⊗ z]`. -/
noncomputable def homologyBaseChange :
    B ⊗[A] S.homology →ₗ[B] (S.baseChange B).homology :=
  (S.baseChange B).moduleCatHomologyIso.inv.hom ∘ₗ S.homologyBaseChangeAux B ∘ₗ
    S.moduleCatHomologyIso.hom.hom.baseChange B

lemma bijective_homologyBaseChange_iff :
    Function.Bijective (S.homologyBaseChange B) ↔
      Function.Bijective (S.homologyBaseChangeAux B) := by
  let e₁ : B ⊗[A] S.homology ≃ₗ[B]
      B ⊗[A] (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.baseChange A B _ _
  let e₂ := (S.baseChange B).moduleCatHomologyIso.toLinearEquiv
  have h : S.homologyBaseChange B = e₂.symm.toLinearMap ∘ₗ S.homologyBaseChangeAux B ∘ₗ
      e₁.toLinearMap := rfl
  rw [h, LinearMap.coe_comp, LinearMap.coe_comp, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e₂.symm.bijective.of_comp_iff', e₁.bijective.of_comp_iff]
  exact Iff.rfl

/-- The comparison map `B ⊗[A] ker g ⟶ ker (1 ⊗ g)`. -/
noncomputable def cyclesBaseChangeMap :
    B ⊗[A] LinearMap.ker S.g.hom →ₗ[B] S.cyclesBaseChange B :=
  LinearMap.liftBaseChange B (S.baseChangeCycles B)

lemma coe_cyclesBaseChangeMap (x : B ⊗[A] LinearMap.ker S.g.hom) :
    (S.cyclesBaseChangeMap B x : B ⊗[A] S.X₂) =
      (LinearMap.ker S.g.hom).subtype.lTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b z =>
    rw [cyclesBaseChangeMap, LinearMap.liftBaseChange_tmul, Submodule.coe_smul,
      baseChangeCycles_apply_coe, LinearMap.lTensor_tmul, smul_tmul', smul_eq_mul, mul_one]
    rfl
  | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy]

lemma homologyBaseChangeAux_lTensor_mkQ (x : B ⊗[A] LinearMap.ker S.g.hom) :
    S.homologyBaseChangeAux B ((LinearMap.range S.moduleCatToCycles).mkQ.lTensor B x) =
      Submodule.Quotient.mk (S.cyclesBaseChangeMap B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b z =>
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply, homologyBaseChangeAux_tmul,
      cyclesBaseChangeMap, LinearMap.liftBaseChange_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Submodule.Quotient.mk_add]

lemma cyclesBaseChangeMap_lTensor_toCycles (y : B ⊗[A] S.X₁) :
    S.cyclesBaseChangeMap B (S.moduleCatToCycles.lTensor B y) =
      (S.f.hom.baseChange B).codRestrict (S.cyclesBaseChange B) (fun x ↦
        congr($((S.baseChange B).zero).hom x)) y := by
  refine Subtype.ext ?_
  rw [coe_cyclesBaseChangeMap, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
    LinearMap.codRestrict_apply, LinearMap.baseChange_eq_ltensor]
  rfl

/-- **Criterion for the base change map to be bijective.** If tensoring with `B` preserves the
left exact sequence `0 ⟶ ker g ⟶ X₂ ⟶ X₃`, the base change map on homology is bijective. -/
theorem bijective_homologyBaseChangeAux_of_exact
    (hinj : Function.Injective ((LinearMap.ker S.g.hom).subtype.lTensor B))
    (hex : Function.Exact ((LinearMap.ker S.g.hom).subtype.lTensor B) (S.g.hom.lTensor B)) :
    Function.Bijective (S.homologyBaseChangeAux B) := by
  have hj (x y : B ⊗[A] LinearMap.ker S.g.hom)
      (h : S.cyclesBaseChangeMap B x = S.cyclesBaseChangeMap B y) : x = y := by
    refine hinj ?_
    rw [← coe_cyclesBaseChangeMap, ← coe_cyclesBaseChangeMap, h]
  have hj' (y : S.cyclesBaseChange B) : ∃ x, S.cyclesBaseChangeMap B x = y := by
    have hy : S.g.hom.lTensor B (y : B ⊗[A] S.X₂) = 0 := by
      rw [← LinearMap.baseChange_eq_ltensor]
      exact y.2
    obtain ⟨x, hx⟩ := (hex _).1 hy
    exact ⟨x, Subtype.ext ((coe_cyclesBaseChangeMap _ _ _).trans hx)⟩
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro w hw
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective B
      (Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles)) w
    rw [LinearMap.mem_ker, homologyBaseChangeAux_lTensor_mkQ,
      Submodule.Quotient.mk_eq_zero] at hw
    obtain ⟨y, hy⟩ := hw
    have hxy : x = S.moduleCatToCycles.lTensor B y :=
      hj _ _ (by rw [cyclesBaseChangeMap_lTensor_toCycles]; exact hy.symm)
    rw [hxy, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.mem_bot]
    have : (LinearMap.range S.moduleCatToCycles).mkQ ∘ₗ S.moduleCatToCycles = 0 := by
      ext x
      simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  · intro h
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ h
    obtain ⟨x, rfl⟩ := hj' y
    exact ⟨_, S.homologyBaseChangeAux_lTensor_mkQ B x⟩

section Naturality

variable {R : Type u} [Ring R]

lemma moduleCatHomologyIso_inv_mk (T : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker T.g.hom) :
    T.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) =
      T.homologyπ.hom (T.moduleCatCyclesIso.inv.hom z) :=
  (T.moduleCatCyclesIso_inv_π_apply z).symm

lemma iCycles_moduleCatCyclesIso_inv (T : ShortComplex (ModuleCat.{u} R))
    (z : LinearMap.ker T.g.hom) : T.iCycles.hom (T.moduleCatCyclesIso.inv.hom z) = z.1 :=
  T.moduleCatCyclesIso_inv_iCycles_apply z

lemma mem_ker_τ₂ {T₁ T₂ : ShortComplex (ModuleCat.{u} R)} (ψ : T₁ ⟶ T₂)
    (z : LinearMap.ker T₁.g.hom) : ψ.τ₂.hom z.1 ∈ LinearMap.ker T₂.g.hom := by
  have h := congr($(ψ.comm₂₃).hom z.1)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.mem_ker.1 z.2,
    map_zero] at h
  exact LinearMap.mem_ker.2 h

/-- The map induced on homology by a morphism of short complexes of modules sends the class of a
cycle `z` to the class of its image. -/
lemma homologyMap_moduleCatHomologyIso_inv_mk {T₁ T₂ : ShortComplex (ModuleCat.{u} R)}
    (ψ : T₁ ⟶ T₂) (z : LinearMap.ker T₁.g.hom) :
    (homologyMap ψ).hom (T₁.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      T₂.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk ⟨ψ.τ₂.hom z, mem_ker_τ₂ ψ z⟩) := by
  rw [moduleCatHomologyIso_inv_mk, moduleCatHomologyIso_inv_mk]
  have h := congr($(homologyπ_naturality ψ).hom (T₁.moduleCatCyclesIso.inv.hom z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h]
  congr 1
  refine (ModuleCat.mono_iff_injective T₂.iCycles).1 inferInstance ?_
  have h' := congr($(cyclesMap_i ψ).hom (T₁.moduleCatCyclesIso.inv.hom z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h'
  change T₂.iCycles.hom _ = T₂.iCycles.hom _
  rw [h', iCycles_moduleCatCyclesIso_inv, iCycles_moduleCatCyclesIso_inv]

end Naturality

lemma homologyBaseChange_tmul_mk (b : B) (z : LinearMap.ker S.g.hom) :
    S.homologyBaseChange B (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
      (S.baseChange B).moduleCatHomologyIso.inv.hom
        (Submodule.Quotient.mk (b • S.baseChangeCycles B z)) := by
  have h := congr($(S.moduleCatHomologyIso.inv_hom_id).hom (Submodule.Quotient.mk z))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  have h1 : (S.moduleCatHomologyIso.hom.hom.baseChange B)
      (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)) =
        b ⊗ₜ Submodule.Quotient.mk z := by
    rw [LinearMap.baseChange_tmul, h]
  calc S.homologyBaseChange B (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z))
      = (S.baseChange B).moduleCatHomologyIso.inv.hom (S.homologyBaseChangeAux B
          ((S.moduleCatHomologyIso.hom.hom.baseChange B)
            (b ⊗ₜ S.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z)))) := rfl
    _ = (S.baseChange B).moduleCatHomologyIso.inv.hom
          (S.homologyBaseChangeAux B (b ⊗ₜ Submodule.Quotient.mk z)) := by rw [h1]
    _ = _ := by rw [homologyBaseChangeAux_tmul]

/-- **Naturality of the base change map on homology.** -/
theorem homologyBaseChange_naturality {S₁ S₂ : ShortComplex (ModuleCat.{u} A)} (φ : S₁ ⟶ S₂)
    (x : B ⊗[A] S₁.homology) :
    S₂.homologyBaseChange B ((homologyMap φ).hom.baseChange B x) =
      (homologyMap ((ModuleCat.baseChange A B).mapShortComplex.map φ)).hom
        (S₁.homologyBaseChange B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul b h =>
    obtain ⟨z, rfl⟩ : ∃ z, S₁.moduleCatHomologyIso.inv.hom (Submodule.Quotient.mk z) = h := by
      obtain ⟨w, hw⟩ := Submodule.mkQ_surjective _ (S₁.moduleCatHomologyIso.hom.hom h)
      refine ⟨w, ?_⟩
      have e := congr($(S₁.moduleCatHomologyIso.hom_inv_id).hom h)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] at e
      rw [← e, ← hw]
      rfl
    rw [LinearMap.baseChange_tmul, homologyMap_moduleCatHomologyIso_inv_mk,
      homologyBaseChange_tmul_mk, homologyBaseChange_tmul_mk]
    erw [homologyMap_moduleCatHomologyIso_inv_mk]
    congr 2

end CategoryTheory.ShortComplex
