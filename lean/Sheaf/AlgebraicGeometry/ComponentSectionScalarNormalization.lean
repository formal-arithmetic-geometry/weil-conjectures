/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import Sheaf.AlgebraicGeometry.ComponentSectionMap

/-! # Scalar normalization for the constructed component section map
Source: Hemo--Richarz--Scholbach, Remark 3.2 and Proposition 4.3(3)
(blueprint: lem-zl-component-section-scalar-normalization).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
  (T : Scheme.{u}) [IsAffine T]
  [(componentTests T).IsContinuous
    ((coherentTopology Profinite.{u}).over (affineComponentSpace T))
    (Scheme.ProEt.topology T)]
  [(componentInverse T).Braided]
  [PreservesFiniteLimits (componentInverse T)]
/-- The constructed section map sends a point scalar to its specified affine pullback.
Source: HRS Remark 3.2 and the monoidal point factorization, Construction (4.1)
(blueprint: lem-zl-component-section-scalar-normalization).
Proof: represent r by its integer-multiple map from the abelian tensor unit and transpose
under the constant-sheaf adjunction. Slice restriction sends this global section to the
section defining profiniteScalarMap. Pull it back by component inverse image. Naturality
of β at this unit section, together with its monoidal unit equation and hα, identifies
the result with the map t in affineScalarSection. Evaluation at the canonical section 1
gives the asserted equality. No invertibility or weak contractibility is used. -/
theorem component_section_scalar_normalization
    (α : (componentInverse T).mapMon.obj
      (Mon.mk (profiniteCoefficient Λ.X (affineComponentSpace T))) ≅
      Mon.mk (condensedRingObj Λ.X T))
    (β : (coherentTopology Profinite.{u}).overPullback Ab.{u + 1}
      (affineComponentSpace T) ⋙ componentInverse T ≅ upperStarFromPoint T)
    (hβ : NatTrans.IsMonoidal β.hom) (hα : α.hom.hom = β.hom.app Λ.X) :
    ∀ r : condensedScalarRing Λ.X,
      componentSectionMap Λ T α (profiniteScalarMap Λ.X (affineComponentSpace T) r) =
        affineScalarSection Λ.X T r := by
  let := hβ
  intro r
  let J := coherentTopology Profinite.{u}
  let S := affineComponentSpace T
  let F := J.overPullback Ab.{u + 1} S
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  let G := componentInverse T
  let : G.Additive := Functor.additive_of_preserves_binary_products G
  let H := upperStarFromPoint T
  let rmap : 𝟙_ Ab.{u + 1} ⟶ Λ.X.obj.obj (Opposite.op (⊤_ Profinite.{u})) :=
    AddCommGrpCat.ofHom
      (((AddMonoidHom.mulRight r).comp (Int.castAddHom (condensedScalarRing Λ.X))).comp
        AddEquiv.ulift.toAddMonoidHom)
  have hr : rmap.hom (ULift.up 1) = r := by
    change ((1 : ℤ) : condensedScalarRing Λ.X) * r = r
    simp only [Int.cast_one, one_mul]
  let s : 𝟙_ (Sheaf J Ab.{u + 1}) ⟶ Λ.X :=
    ((constantSheafAdj J Ab.{u + 1} terminalIsTerminal).homEquiv _ Λ.X).symm rmap
  let x : MonObj.Γ (profiniteCoefficient Λ.X S) :=
    MonObj.Γ.mapFunctor F (MonObj.Γ.ofHom s)
  have hx : InternalAbelianSheafModule.sectionGlobalEval (J.over S)
      (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) x = profiniteScalarMap Λ.X S r := by
    let U := Opposite.op (Over.mk (𝟙 S))
    let e := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      (Over.forget S) Ab.{u + 1} (J.over S) J
    change (((Functor.LaxMonoidal.ε (sheafToPresheaf (J.over S) Ab.{u + 1})).app U ≫
      (Functor.LaxMonoidal.ε F).hom.app U) ≫ (F.map s).hom.app U).hom (ULift.up 1) =
      ((e.hom.app Λ.X).app U).hom
        (Λ.X.obj.map (terminal.from S).op r)
    rw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app]
    dsimp [e]
    rw [Functor.sheafToPresheafCompWhiskeringLeftIsoPushforward_hom_app]
    have hs : toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (𝟙_ Ab.{u + 1})) ≫
        s.hom = ((constantPresheafAdj Ab.{u + 1} terminalIsTerminal).homEquiv _ _).symm
          rmap := by
      change (sheafificationAdjunction J Ab.{u + 1}).homEquiv
        ((Functor.const Profinite.{u}ᵒᵖ).obj (𝟙_ Ab.{u + 1})) Λ.X s = _
      simp only [s, constantSheafAdj, Adjunction.comp_homEquiv]
      exact Equiv.apply_symm_apply _ _
    change (((toSheafify J ((Functor.const Profinite.{u}ᵒᵖ).obj (𝟙_ Ab.{u + 1}))).app
      (Opposite.op S)) ≫ s.hom.app (Opposite.op S)).hom (ULift.up 1) =
        (Λ.X.obj.map (terminal.from S).op).hom r
    rw [← NatTrans.comp_app, hs, Adjunction.homEquiv_counit]
    change (Λ.X.obj.map (terminalIsTerminal.from S).op).hom
      (rmap.hom (ULift.up 1)) = _
    have hf : terminalIsTerminal.from S = (terminal.from S : S ⟶ ⊤_ Profinite.{u}) :=
      terminalIsTerminal.hom_ext _ _
    rw [hf]
    exact congrArg (Λ.X.obj.map (terminal.from S).op).hom hr
  have hsection :
      Functor.LaxMonoidal.ε G ≫ G.map x.hom ≫ α.hom.hom =
        Functor.LaxMonoidal.ε H ≫ H.map s := by
    change Functor.LaxMonoidal.ε G ≫
      G.map (Functor.LaxMonoidal.ε F ≫ F.map s) ≫ α.hom.hom = _
    rw [G.map_comp, hα]
    have hn : G.map (F.map s) ≫ β.hom.app Λ.X =
        β.hom.app (𝟙_ (Sheaf J Ab.{u + 1})) ≫ H.map s := β.hom.naturality s
    simp only [Category.assoc]
    rw [hn]
    have hu : (Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F)) ≫
        β.hom.app (𝟙_ (Sheaf J Ab.{u + 1})) = Functor.LaxMonoidal.ε H :=
      NatTrans.IsMonoidal.unit (τ := β.hom)
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ H.map s) hu
  unfold componentSectionMap
  dsimp only
  rw [← hx]
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe]
  change InternalAbelianSheafModule.sectionGlobalEval (Scheme.ProEt.topology T)
    (condensedRingObj Λ.X T) (Scheme.ProEt.mk (𝟙 T))
    (MonObj.Γ.map α.hom.hom (MonObj.Γ.mapFunctor G
      ((InternalAbelianSheafModule.sectionGlobalEquiv (J.over S)
        (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal).symm
        ((InternalAbelianSheafModule.sectionGlobalEquiv (J.over S)
          (profiniteCoefficient Λ.X S) (Over.mk (𝟙 S)) Over.mkIdTerminal) x)))) = _
  rw [RingEquiv.symm_apply_apply]
  change InternalAbelianSheafModule.sectionGlobalEval (Scheme.ProEt.topology T)
    (condensedRingObj Λ.X T) (Scheme.ProEt.mk (𝟙 T))
      (MonObj.Γ.ofHom (Functor.LaxMonoidal.ε G ≫ G.map x.hom ≫ α.hom.hom)) = _
  rw [hsection]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
