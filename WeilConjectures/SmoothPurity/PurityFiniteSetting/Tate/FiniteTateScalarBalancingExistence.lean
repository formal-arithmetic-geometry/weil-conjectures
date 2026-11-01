/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Tate.FiniteTateScalarSourceData
import all WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf

/-! # Existence of finite Tate scalar balancing families

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2;
Stacks 06YN, 06YY, 07A6 and 07A4.
(blueprint: lem-pur-finite-tate-scalar-balancing-existence)

Degree zero is the oplax monoidal unit of extension of scalars, degree one the
root-generator normalized ordinary Tate scalar isomorphism of
`WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects`, and degree `r + 2` the oplax
tensorator followed by the tensor product of the previous degrees. The generator
formula follows by induction from the monoidality of the scalar adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting
variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

private instance balancingAdjMonoidal (φ : A →+* B) (X : Scheme.{u}) :
    (Etale.purityScalarSheafAdjunction φ X).IsMonoidal :=
  isMonoidal_sheafAdjunction X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private instance balancingEtaIso (φ : A →+* B) (X : Scheme.{u}) :
    IsIso (Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X)) :=
  isIso_η_composeAndSheafify X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ)

private instance balancingDeltaIso (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    IsIso (Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X) M N) :=
  isIso_δ_composeAndSheafify X.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} φ) M N

private theorem balancingTensorAdjoint (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (M' N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (f : (Etale.purityScalarSheaf φ X).obj M ⟶ M')
    (g : (Etale.purityScalarSheaf φ X).obj N ⟶ N') :
    (Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X) M N ≫ (f ⊗ₘ g)) =
      (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ f) ⊗ₘ
        ((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ g)) ≫
      Functor.LaxMonoidal.μ (Sheaf.restrictScalars X.smallEtaleTopology φ) M' N' := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [(Etale.purityScalarSheafAdjunction φ X).unit_app_tensor_comp_map_δ]
  rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

private def ordinaryBalancingIso
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) :
    (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA 1) ≅
      Scheme.finiteEtaleTateTwist X N B hB 1 :=
  @asIso _ _ _ _
    (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _).symm
      (AlgebraicGeometry.ProEtale.reductionEtaleTateMap φ X N hA hB))
    (AlgebraicGeometry.ProEtale.reductionTateOrdinaryScalar_isIso φ X N hA hB)

private noncomputable def balancingFamily
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj
          (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r
  | 0 => asIso (Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X))
  | 1 => ordinaryBalancingIso φ N hA hB X
  | r + 2 =>
      asIso (Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X)
        (Scheme.finiteEtaleTateTwist X N A hA (r + 1))
        (Scheme.finiteEtaleTateLine X N A hA)) ≪≫
      tensorIso (balancingFamily φ N hA hB X (r + 1))
        (ordinaryBalancingIso φ N hA hB X)

private theorem balancingUnitGenerator (R : Type (u + 1)) [CommRing R]
    (X : Scheme.{u}) :
    Functor.LaxMonoidal.ε (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) =
      toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R)) := by
  simp only [Adjunction.rightAdjointLaxMonoidal_ε, Adjunction.homEquiv_unit]
  change _ ≫ (sheafToPresheaf _ _).map (𝟙 _) = _
  simp
  rfl

private theorem balancingRestrictionUnit (φ : A →+* B) (X : Scheme.{u})
    (U : X.Etaleᵒᵖ) (a : A) :
    (Functor.LaxMonoidal.ε (Sheaf.restrictScalars X.smallEtaleTopology φ)).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of B B))).app U (φ a) := by
  have h := congrArg (fun t ↦ t.app U)
    (Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose
      X.smallEtaleTopology (ModuleCat.restrictScalars φ))
  rw [balancingUnitGenerator, balancingUnitGenerator] at h
  have hh := ConcreteCategory.congr_hom h a
  change (Functor.LaxMonoidal.ε
    (Sheaf.restrictScalars X.smallEtaleTopology φ)).hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of A A))).app U a) =
      (toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of B B))).app U
          (Functor.LaxMonoidal.ε (ModuleCat.restrictScalars φ) a) at hh
  simpa only [ModuleCat.restrictScalars_η] using hh

private theorem balancingTensorGenerator (φ : A →+* B) (X : Scheme.{u})
    (M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) (U : X.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (Functor.LaxMonoidal.μ (Sheaf.restrictScalars X.smallEtaleTopology φ) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ _).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} B)) M N).app U (x ⊗ₜ[B] y) := by
  have h := congrArg (fun t ↦ t.app U)
    (Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose
      X.smallEtaleTopology (ModuleCat.restrictScalars φ) M N)
  let x' : ((ModuleCat.restrictScalars φ).obj (M.obj.obj U)) := x
  let y' : ((ModuleCat.restrictScalars φ).obj (N.obj.obj U)) := y
  have hh := ConcreteCategory.congr_hom h (x' ⊗ₜ[A] y')
  change (Functor.LaxMonoidal.μ
    (Sheaf.restrictScalars X.smallEtaleTopology φ) M N).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ _).app U (x' ⊗ₜ[A] y')) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} B)) M N).app U
      (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars φ)
        (M.obj.obj U) (N.obj.obj U) (x' ⊗ₜ[A] y')) at hh
  simpa only [ModuleCat.restrictScalars_μ_tmul] using hh

private theorem balancingTensorMap (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {M N M' N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (f ⊗ₘ g).hom.app U
      ((Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app U (x ⊗ₜ[R] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M' N').app U
      (f.hom.app U x ⊗ₜ[R] g.hom.app U y) := by
  have h := congrArg (fun t ↦ t.app U)
    (Functor.LaxMonoidal.μ_natural (F := sheafToPresheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} R)) f g)
  exact (ConcreteCategory.congr_hom h (x ⊗ₜ[R] y)).symm

private theorem balancingAdjointTensorGenerator (φ : A →+* B) (X : Scheme.{u})
    {M N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {M' N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (f : (Etale.purityScalarSheaf φ X).obj M ⟶ M')
    (g : (Etale.purityScalarSheaf φ X).obj N ⟶ N') (U : X.Etaleᵒᵖ)
    (x : M.obj.obj U) (y : N.obj.obj U) :
    (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X) M N ≫ (f ⊗ₘ g))).hom.app U)
        ((Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M N).app U (x ⊗ₜ[A] y)) =
    (Functor.LaxMonoidal.μ (sheafToPresheaf _ _) M' N').app U
      ((@id (M'.obj.obj U)
        (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ f).hom.app U x)) ⊗ₜ[B]
      (@id (N'.obj.obj U)
        (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ g).hom.app U y))) := by
  rw [balancingTensorAdjoint]
  change (Functor.LaxMonoidal.μ
    (Sheaf.restrictScalars X.smallEtaleTopology φ) M' N').hom.app U ((tensorHom
      ((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ f)
      ((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _ g)).hom.app U _) = _
  rw [balancingTensorMap]
  exact balancingTensorGenerator φ X M' N' U _ _

private theorem balancingOneCoefficient (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hR : (N : R) = 0) (X : Scheme.{u}) (U : X.Etaleᵒᵖ)
    (a b : R) (z : (X.rootsOfUnitySheaf N).obj.obj U) :
    b • Scheme.finiteEtaleTateOneGenerator R N X hR U a z =
      Scheme.finiteEtaleTateOneGenerator R N X hR U (b * a) z := by
  let _ := AddCommGroup.zmodModule (Scheme.finiteEtaleMu_annihilated X N U)
  let P := Scheme.finiteEtaleMuModulePresheaf X N
  let q := (toSheafify X.smallEtaleTopology (P ⋙ ModuleCat.extendScalars
    (Scheme.finiteEtaleTwistScalar N R hR))).app U
  change b • q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
    (Module.compHom _ (Scheme.finiteEtaleTwistScalar N R hR)) _ a z) =
    q (@TensorProduct.tmul (ZMod N) _ _ _ _ _
      (Module.compHom _ (Scheme.finiteEtaleTwistScalar N R hR)) _ (b * a) z)
  rw [← map_smul]
  exact congrArg q (ModuleCat.ExtendScalars.smul_tmul
    (Scheme.finiteEtaleTwistScalar N R hR) b a (show P.obj U from z))

private theorem balancingPowerCoefficient (R : Type (u + 1)) [CommRing R]
    (N : ℕ) (hR : (N : R) = 0) (X : Scheme.{u}) (r : ℕ)
    (U : X.Etaleᵒᵖ) (a b : R) (z : Fin r → (X.rootsOfUnitySheaf N).obj.obj U) :
    b • Scheme.finiteTateEtalePowerGenerator X R N hR U a r z =
      Scheme.finiteTateEtalePowerGenerator X R N hR U (b * a) r z := by
  induction r using Nat.twoStepInduction with
  | zero => exact (map_smul _ b a).symm
  | one => exact balancingOneCoefficient R N hR X U a b (z 0)
  | more r _ ih =>
    dsimp only [Scheme.finiteTateEtalePowerGenerator]
    erw [← map_smul, TensorProduct.smul_tmul', ih]
    rfl

private theorem balancingOneNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (U : X.Etaleᵒᵖ) (a : A)
    (z : (X.rootsOfUnitySheaf N).obj.obj U) :
    (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (ordinaryBalancingIso φ N hA hB X).hom).hom.app U)
        (Scheme.finiteEtaleTateOneGenerator A N X hA U a z) =
      Scheme.finiteEtaleTateOneGenerator B N X hB U (φ a) z := by
  simp only [ordinaryBalancingIso, asIso_hom, Equiv.apply_symm_apply]
  exact (ProEtale.reductionEtaleTateMap_existsUnique φ X N hA hB).exists.choose_spec U a z

private theorem balancingNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (r : ℕ) (U : X.Etaleᵒᵖ) (a : A)
    (z : Fin r → (X.rootsOfUnitySheaf N).obj.obj U) :
    (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (balancingFamily φ N hA hB X r).hom).hom.app U)
        (Scheme.finiteTateEtalePowerGenerator X A N hA U a r z) =
      Scheme.finiteTateEtalePowerGenerator X B N hB U (φ a) r z := by
  induction r using Nat.twoStepInduction with
  | zero =>
    change (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X))).hom.app U) _ = _
    rw [Adjunction.homEquiv_unit,
      (Etale.purityScalarSheafAdjunction φ X).unit_app_unit_comp_map_η]
    exact balancingRestrictionUnit φ X U a
  | one => exact balancingOneNormalized φ N hA hB X U a (z 0)
  | more r _ ih =>
    change (((Etale.purityScalarSheafAdjunction φ X).homEquiv _ _
      (Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X) _ _ ≫
        ((balancingFamily φ N hA hB X (r + 1)).hom ⊗ₘ
          (ordinaryBalancingIso φ N hA hB X).hom))).hom.app U)
      ((Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} A)) _ _).app U
        (Scheme.finiteTateEtalePowerGenerator X A N hA U a (r + 1)
          (fun i ↦ z i.castSucc) ⊗ₜ[A]
            Scheme.finiteEtaleTateOneGenerator A N X hA U 1 (z (Fin.last (r + 1))))) = _
    rw [balancingAdjointTensorGenerator]
    have h := congrArg₂
      (fun (x : (Scheme.finiteEtaleTateTwist X N B hB (r + 1)).obj.obj U)
        (y : (Scheme.finiteEtaleTateLine X N B hB).obj.obj U) ↦
      (Functor.LaxMonoidal.μ (sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} B)) _ _).app U (x ⊗ₜ[B] y))
      (ih (fun i ↦ z i.castSucc))
      (balancingOneNormalized φ N hA hB X U 1 (z (Fin.last (r + 1))))
    simpa only [map_one, id_eq, Scheme.finiteTateEtalePowerGenerator,
      Scheme.finiteEtaleTateTwist] using h

/-- A finite coefficient extension admits a recursively normalized Tate balancing family.

Source: sk-prop-an, cor-pur-vector-bundle-purity.proof.md, paragraph 2; Stacks 06YN,
06YY, 07A6 and 07A4 (blueprint: lem-pur-finite-tate-scalar-balancing-existence).

Proof: degree zero is the oplax monoidal unit of extension of scalars.  Degree one is the
published root-generator normalized ordinary Tate adjunction, whose invertibility is proved
by the scalar-extension/restriction comparison.  Higher powers are obtained recursively from
the oplax tensorator and the degree-one map.  Naturality of the scalar adjunction unit and the
monoidal coherence equations give the stated generator formula by induction; the same
coherence equations give the displayed unit and successor equalities definitionally. -/
theorem finite_tate_scalar_balancing_exists [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u}) (hX : ∀ x : X, IsUnit (N : X.presheaf.stalk x)) :
    ∃ β : ∀ r : ℕ,
        (Etale.purityScalarSheaf φ X).obj
            (Scheme.finiteEtaleTateTwist X N A hA r) ≅
          Scheme.finiteEtaleTateTwist X N B hB r,
      IsFiniteTateScalarBalancing φ N hA hB X β := by
  classical
  have _ := hN
  have _ := hX
  refine ⟨balancingFamily φ N hA hB X, ?_, rfl, ?_⟩
  · intro r U a b z
    rw [map_smul]
    have h : (balancingFamily φ N hA hB X r).hom.hom.app U
        (((Etale.purityScalarSheafAdjunction φ X).unit.app
          (Scheme.finiteEtaleTateTwist X N A hA r)).hom.app U
            (Scheme.finiteTateEtalePowerGenerator X A N hA U a r z)) =
        Scheme.finiteTateEtalePowerGenerator X B N hB U (φ a) r z :=
      balancingNormalized φ N hA hB X r U a z
    dsimp only [id]
    erw [h]
    simpa only [mul_comm] using balancingPowerCoefficient B N hB X r U (φ a) b z
  · intro r
    rfl

end WeilConjectures.PurityFiniteSetting
