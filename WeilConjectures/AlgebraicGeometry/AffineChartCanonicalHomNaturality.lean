/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.ChartOrdinaryMapRecovery
public import WeilConjectures.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
import WeilConjectures.AlgebraicGeometry.AffineChartNormalizedSectionModels
import WeilConjectures.AlgebraicGeometry.AffineChartTensorRecovery

/-! # Canonical affine chart Hom naturality

## References

* Stacks Project, Tags 01ZR, 01I6, 0095 and 0096
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Extension of scalars along an explicitly identified composite ring map.
-/
noncomputable def scalarExtensionCompOfEq
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (r₁ : B →+* C) (r₀ : A →+* C) (h : r₀ = r₁.comp r)
    (P : ModuleCat.{u} A) :
    (ModuleCat.extendScalars r₀).obj P ≅
      (ModuleCat.extendScalars r₁).obj ((ModuleCat.extendScalars r).obj P) :=
  eqToIso (congrArg (fun f ↦ (ModuleCat.extendScalars f).obj P) h) ≪≫
    (ModuleCat.extendScalarsComp r r₁).app P

/-- The composition comparison sends each unit tensor to its iterated unit tensor.
-/
theorem scalarExtensionCompOfEq_one_tmul
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (r : A →+* B) (r₁ : B →+* C) (r₀ : A →+* C) (h : r₀ = r₁.comp r)
    (P : ModuleCat.{u} A) (m : P) :
    (scalarExtensionCompOfEq r r₁ r₀ h P).hom ((1 : C) ⊗ₜ[A, r₀] m) =
      (1 : C) ⊗ₜ[B, r₁] ((1 : B) ⊗ₜ[A, r] m) := by
  subst r₀
  simpa only [scalarExtensionCompOfEq, Iso.trans_hom, eqToIso_refl,
    Iso.refl_hom, Category.id_comp] using!
    ModuleCat.extendScalarsComp_hom_app_one_tmul r r₁ P m

/-- Scalar extension through a stage of a colimit, using its cocone equation.
-/
noncomputable def colimitScalarExtensionComp
    {J : Type u} [Category J] (F : J ⥤ CommRingCat.{u})
    {t x : J} (h : t ⟶ x) (P : ModuleCat.{u} (F.obj t)) :
    (ModuleCat.extendScalars (colimit.ι F t).hom).obj P ≅
      (ModuleCat.extendScalars (colimit.ι F x).hom).obj
        ((ModuleCat.extendScalars (F.map h).hom).obj P) :=
  scalarExtensionCompOfEq (F.map h).hom (colimit.ι F x).hom (colimit.ι F t).hom
    (congrArg CommRingCat.Hom.hom (colimit.w F h).symm) P

/-- The canonical colimit comparison is normalized on tensor generators.
-/
theorem colimitScalarExtensionComp_one_tmul
    {J : Type u} [Category J] (F : J ⥤ CommRingCat.{u})
    {t x : J} (h : t ⟶ x) (P : ModuleCat.{u} (F.obj t)) (m : P) :
    (colimitScalarExtensionComp F h P).hom
        ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, (colimit.ι F t).hom] m) =
      (1 : ↑(colimit F)) ⊗ₜ[F.obj x, (colimit.ι F x).hom]
        ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, (F.map h).hom] m) := by
  exact scalarExtensionCompOfEq_one_tmul _ _ _ _ P m

set_option maxHeartbeats 600000 in
-- The dependent chart and section-model witnesses require substantial elaboration.
/-- Affine Hom comparisons commute with the canonical scalar-extension map
(Stacks, Tags 01ZR, 01I6, 0095 and 0096). -/
theorem affine_chart_canonical_hom_naturality
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : U.I₀) (ha : IsAffine (U.X a))
    (M N : (U.X a).Modules)
    (hMq : M.IsQuasicoherent)
    (hNq : N.IsQuasicoherent)
    :
    let rep := (OrderEmbedding.ofAntisymmetrization
      (α := {k : I // j ≤ k})).monotone.functor
    let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
    let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
    let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
    let B : (U.X a).Modules → ModuleCat.{u} (F.obj t) := fun L ↦ by
      let k := rep.obj t
      let r := Spec.map (R.map (homOfLE k.property))
      change ModuleCat.{u} Γ(pullback r g, ⊤)
      exact ModuleCat.of _ Γ((Scheme.Modules.pullback (pullback.snd r g)).obj L, ⊤)
    let P := B M
    let Q := B N
    let r₀ := (colimit.ι F t).hom
    let q₀ := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    ∃ α : ((ModuleCat.extendScalars r₀).obj P ⟶
        (ModuleCat.extendScalars r₀).obj Q) ≃
      ((Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj M ⟶
        (Scheme.Modules.pullback (U.pullbackHom q₀ a)).obj N),
      ∀ (x : Antisymmetrization {k : I // j ≤ k} (· ≤ ·)) (htx : t ≤ x),
        let k := (rep.obj x).val
        let hjk := (rep.obj x).property
        let q := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (Over.homMk (Spec.map (R.map (homOfLE hjk)))
            (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let p := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
        let q₀ := baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
        let w : p ≫ q = q₀ := by
          rw [← baseChangeMap_comp]
          congr 1
          ext
          simpa using c.w (homOfLE hjk).op
        let r := (F.map (homOfLE htx)).hom
        let r₁ := (colimit.ι F x).hom
        ∃ β : ((ModuleCat.extendScalars r).obj P ⟶
            (ModuleCat.extendScalars r).obj Q) ≃
          ((Scheme.Modules.pullback (U.pullbackHom q a)).obj M ⟶
            (Scheme.Modules.pullback (U.pullbackHom q a)).obj N),
          ∀ (s : (ModuleCat.extendScalars r).obj P ⟶
              (ModuleCat.extendScalars r).obj Q),
            chartOrdinaryMapRecovery q p q₀ w U a M N
              (α ((colimitScalarExtensionComp F (homOfLE htx) P).hom ≫
                (ModuleCat.extendScalars r₁).map s ≫
                (colimitScalarExtensionComp F (homOfLE htx) Q).inv)) (β s) := by
  classical
  let rep := (OrderEmbedding.ofAntisymmetrization
    (α := {k : I // j ≤ k})).monotone.functor
  let g := U.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE hij)))
  let F := rep ⋙ (upperTailChartDiagram R j g).rightOp ⋙ Scheme.Γ
  let t := toAntisymmetrization (· ≤ ·) (⟨j, le_rfl⟩ : {k : I // j ≤ k})
  let B : (U.X a).Modules → ModuleCat.{u} (F.obj t) := fun L ↦ by
    let k := rep.obj t
    let r := Spec.map (R.map (homOfLE k.property))
    change ModuleCat.{u} Γ(pullback r g, ⊤)
    exact ModuleCat.of _ Γ((Scheme.Modules.pullback (pullback.snd r g)).obj L, ⊤)
  let P := B M
  let Q := B N
  obtain ⟨δM, δN, ρ₀, e₀M, e₀N, α, _h₀M, h₀N, n₀M, n₀N, hα, hx⟩ :=
    affine_chart_normalized_section_models R c hc i f j hij U a ha M N hMq hNq
  refine ⟨α, ?_⟩
  intro x htx
  obtain ⟨ρₓ, eₓM, eₓN, β, hₓM, hₓN, nₓM, nₓN, hβ, hAffine, hRing⟩ := hx x htx
  refine ⟨β, ?_⟩
  intro s
  let r := (F.map (homOfLE htx)).hom
  let r₁ := (colimit.ι F x).hom
  let r₀ := (colimit.ι F t).hom
  let cP := colimitScalarExtensionComp F (homOfLE htx) P
  let cQ := colimitScalarExtensionComp F (homOfLE htx) Q
  let τ := cP.hom ≫ (ModuleCat.extendScalars r₁).map s ≫ cQ.inv
  have hτ (m : P) : τ ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m) =
      cQ.inv ((1 : ↑(colimit F)) ⊗ₜ[F.obj x, r₁]
        s ((1 : ↑(F.obj x)) ⊗ₜ[F.obj t, r] m)) := by
    change cQ.inv ((ModuleCat.extendScalars r₁).map s
      (cP.hom ((1 : ↑(colimit F)) ⊗ₜ[F.obj t, r₀] m))) = _
    apply congrArg cQ.inv
    exact (congrArg ((ModuleCat.extendScalars r₁).map s)
      (colimitScalarExtensionComp_one_tmul F (homOfLE htx) P m)).trans
        (ModuleCat.ExtendScalars.map_tmul r₁ s 1 _)
  apply affine_chart_tensor_coordinate_recovery r r₁ r₀ _ _ _ _ U a M N hMq P Q
    δM δN ρ₀ ρₓ e₀M e₀N eₓM eₓN h₀N hₓM hₓN n₀M n₀N nₓM nₓN hAffine
    cQ (colimitScalarExtensionComp_one_tmul F (homOfLE htx) Q)
    τ s hτ (α τ) (β s) (hα τ) (hβ s)
  exact hRing

end AlgebraicGeometry
