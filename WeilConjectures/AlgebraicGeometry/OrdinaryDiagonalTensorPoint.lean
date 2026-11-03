/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldRestrictionExteriorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # The ordinary diagonal retract at the point

The finite-ring Kunneth proof starts from the separability section on vector spaces.
This file constructs its action and section, with naturality and the canonical balanced map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory MonoidalCategory
open scoped TensorProduct
universe u
section
variable (F B : Type u) [Field F] [Field B] [Algebra F B]
variable (M N : Type u) [AddCommGroup M] [AddCommGroup N]
  [Module F M] [Module F N] [Module B M] [Module B N]
  [IsScalarTower F B M] [IsScalarTower F B N]
private def factorAction : B →ₗ[F] B →ₗ[F] (M ⊗[F] N →ₗ[F] M ⊗[F] N) :=
  LinearMap.compl₁₂
    (TensorProduct.mapBilinear (RingHom.id F) M N M N : (M →ₗ[F] M) →ₗ[F]
      (N →ₗ[F] N) →ₗ[F] (M ⊗[F] N →ₗ[F] M ⊗[F] N))
    (Algebra.lsmul F F M).toLinearMap (Algebra.lsmul F F N).toLinearMap
private def act : B ⊗[F] B →ₗ[F] (M ⊗[F] N →ₗ[F] M ⊗[F] N) :=
  TensorProduct.lift (factorAction F B M N)
private theorem act_tmul (a b : B) (m : M) (n : N) :
    act F B M N (a ⊗ₜ[F] b) (m ⊗ₜ[F] n) = (a • m) ⊗ₜ[F] (b • n) := by
  rfl
private theorem act_mul (x y : B ⊗[F] B) :
    act F B M N (x * y) = (act F B M N x).comp (act F B M N y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c d =>
      ext m n
      simp [act, factorAction, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [mul_add, hx, hy, LinearMap.comp_add]
  | add x y hx hy => simp [add_mul, hx, hy, LinearMap.add_comp]
private theorem act_smul (x : B ⊗[F] B) (c : B) (v : M ⊗[F] N) :
    act F B M N x (c • v) = c • act F B M N x v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, smul_add]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy, smul_add]
    | tmul m n => simp [act_tmul, TensorProduct.smul_tmul', smul_comm a c m]
private theorem act_balanced
    (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (c : B) (m : M) (n : N) :
    act F B M N e ((c • m) ⊗ₜ[F] n) = act F B M N e (m ⊗ₜ[F] (c • n)) := by
  have hh : e * (c ⊗ₜ[F] (1 : B)) = e * ((1 : B) ⊗ₜ[F] c) := by
    simpa only [sub_mul, sub_eq_zero, mul_comm e] using hd c
  calc
    _ = act F B M N (e * (c ⊗ₜ[F] (1 : B))) (m ⊗ₜ[F] n) := by
      rw [act_mul]
      simp only [LinearMap.comp_apply, act_tmul, one_smul]
    _ = act F B M N (e * ((1 : B) ⊗ₜ[F] c)) (m ⊗ₜ[F] n) := by rw [hh]
    _ = _ := by
      rw [act_mul]
      simp only [LinearMap.comp_apply, act_tmul, one_smul]
private def sectionB (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    M ⊗[B] N →ₗ[B] M ⊗[F] N :=
  TensorProduct.lift (LinearMap.mk₂ B
    (fun m n ↦ act F B M N e (m ⊗ₜ[F] n))
    (fun _ _ _ ↦ by simp [TensorProduct.add_tmul])
    (fun c m n ↦ by rw [← TensorProduct.smul_tmul', act_smul])
    (fun _ _ _ ↦ by simp [TensorProduct.tmul_add])
    (fun c m n ↦ by rw [← act_balanced F B M N e hd, ← TensorProduct.smul_tmul',
      act_smul]))
private def quotient : M ⊗[F] N →ₗ[F] M ⊗[B] N :=
  TensorProduct.mapOfCompatibleSMul B F F M N
private theorem quotient_act (x : B ⊗[F] B) (v : M ⊗[F] N) :
    quotient F B M N (act F B M N x v) =
      Algebra.TensorProduct.lmul' F x • quotient F B M N v := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_smul]
  | tmul a b =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [hx, hy, smul_add]
    | tmul m n =>
      simp [quotient, act_tmul, TensorProduct.smul_tmul', TensorProduct.tmul_smul,
        mul_smul, smul_comm a b m]
private theorem quotient_section (e : B ⊗[F] B)
    (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    (quotient F B M N).comp ((sectionB F B M N e hd).restrictScalars F) =
      LinearMap.id := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | tmul m n =>
    change quotient F B M N (act F B M N e (m ⊗ₜ[F] n)) = m ⊗ₜ[B] n
    rw [quotient_act, hμ, one_smul]
    rfl
private theorem section_quotient (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    ((sectionB F B M N e hd).restrictScalars F).comp (quotient F B M N) =
      act F B M N e := by
  ext m n
  rfl
private def action : (B ⊗[F] B) →+* Module.End F (M ⊗[F] N) where
  toFun := act F B M N
  map_zero' := (act F B M N).map_zero
  map_add' := (act F B M N).map_add
  map_one' := by
    ext m n
    change act F B M N ((1 : B) ⊗ₜ[F] (1 : B)) (m ⊗ₜ[F] n) = m ⊗ₜ[F] n
    simp only [act_tmul, one_smul]
  map_mul' := act_mul F B M N
variable {M' N' : Type u} [AddCommGroup M'] [AddCommGroup N']
  [Module F M'] [Module F N'] [Module B M'] [Module B N']
  [IsScalarTower F B M'] [IsScalarTower F B N']
private theorem action_naturality (x : B ⊗[F] B) (f : M →ₗ[B] M') (g : N →ₗ[B] N') :
    (TensorProduct.map (f.restrictScalars F) (g.restrictScalars F)).comp
      (act F B M N x) =
    (act F B M' N' x).comp
      (TensorProduct.map (f.restrictScalars F) (g.restrictScalars F)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [LinearMap.comp_add, LinearMap.add_comp, hx, hy]
  | tmul a b =>
    ext m n
    change f (a • m) ⊗ₜ[F] g (b • n) = (a • f m) ⊗ₜ[F] (b • g n)
    rw [f.map_smul, g.map_smul]
private theorem section_naturality (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0)
    (f : M →ₗ[B] M') (g : N →ₗ[B] N') :
    (TensorProduct.map (f.restrictScalars F) (g.restrictScalars F)).comp
      ((sectionB F B M N e hd).restrictScalars F) =
    ((sectionB F B M' N' e hd).restrictScalars F).comp
      ((TensorProduct.map f g).restrictScalars F) := by
  apply LinearMap.ext
  intro v
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp_all
  | tmul m n =>
    exact LinearMap.congr_fun (action_naturality F B M N e f g) (m ⊗ₜ[F] n)
end

namespace Native
open scoped ModuleCat.Algebra
variable (F B : Type u) [Field F] [Field B] [Algebra F B]
private abbrev U := ModuleCat.restrictScalars (algebraMap F B)
private abbrev source :=
  (((Functor.whiskeringLeft₂ (ModuleCat.{u} F)).obj (U F B)).obj (U F B)).obj
    (curriedTensor (ModuleCat.{u} F))
private abbrev target :=
  (Functor.postcompose₂.obj (U F B)).obj (curriedTensor (ModuleCat.{u} B))
private noncomputable def ordinaryAction (x : B ⊗[F] B) :
    End (source F B) where
  app M :=
    { app N := by
        exact ModuleCat.ofHom (act F B M N x)
      naturality N N' g := by
        apply ModuleCat.hom_ext
        exact (action_naturality F B M N x (LinearMap.id) g.hom).symm }
  naturality M M' f := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact (action_naturality F B M N x f.hom (LinearMap.id)).symm
private noncomputable def ordinaryActionRing : (B ⊗[F] B) →+* End (source F B) where
  toFun := ordinaryAction F B
  map_zero' := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact (act F B M N).map_zero
  map_one' := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact (action F B M N).map_one
  map_add' x y := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact (act F B M N).map_add x y
  map_mul' x y := by
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact act_mul F B M N x y
private noncomputable def ordinarySection (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    target F B ⟶ source F B where
  app M :=
    { app N := ModuleCat.ofHom ((sectionB F B M N e hd).restrictScalars F)
      naturality N N' g := by
        apply ModuleCat.hom_ext
        exact (section_naturality F B M N e hd LinearMap.id g.hom).symm }
  naturality M M' f := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    exact (section_naturality F B M N e hd f.hom LinearMap.id).symm
private theorem ordinarySection_split (e : B ⊗[F] B)
    (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    ordinarySection F B e hd ≫ Functor.LaxMonoidal.μNatTrans (U F B) = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext N
  have hq : (Functor.LaxMonoidal.μ (U F B) M N).hom = quotient F B M N := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply LinearMap.ext
    intro n
    exact ModuleCat.restrictScalars_μ_tmul (algebraMap F B) M N m n
  apply ModuleCat.hom_ext
  change (Functor.LaxMonoidal.μ (U F B) M N).hom.comp
    ((sectionB F B M N e hd).restrictScalars F) = LinearMap.id
  rw [hq]
  exact quotient_section F B M N e hμ hd
private theorem ordinarySection_retract (e : B ⊗[F] B)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    Functor.LaxMonoidal.μNatTrans (U F B) ≫ ordinarySection F B e hd =
      ordinaryActionRing F B e := by
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext N
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  change sectionB F B M N e hd
    (Functor.LaxMonoidal.μ (U F B) M N (m ⊗ₜ[F] n)) = _
  rw [ModuleCat.restrictScalars_μ_tmul]
  rfl
private theorem ordinaryAction_pure (a b : B) (M N : ModuleCat.{u} B) :
    ((ordinaryActionRing F B (a ⊗ₜ[F] b)).app M).app N =
      (U F B).map (a • 𝟙 M) ⊗ₘ (U F B).map (b • 𝟙 N) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro n
  rfl
end Native

namespace AlgebraicGeometry.Etale

/-- The ordinary point tensor quotient is the diagonal retract specified by a separability
element.
Source: the finite-ring Kunneth proof, first paragraph, termwise vector-space argument.

Proof. Define the F-linear tensor-ring action by the bilinear map sending a,b to the tensor
of their two scalar multiplication maps. Tensor induction proves multiplicativity and
naturality. Act by e on the F-tensor of m and n; the diagonal relation equates its values on
b m tensor n and m tensor b n. Thus it defines a B-bilinear map and hence a section on the
B-tensor. The ordinary quotient after this section is multiplication(e) times the identity,
so equals the identity. In the opposite order the composite is exactly the e-action.
Tensor induction also proves naturality of the action and section in both module variables.
The quotient is the existing lax tensorator: both send every pure tensor to the same
B-balanced tensor. This proves the two identities for the specified tensorator and records
the action of every pure coefficient tensor.
(blueprint: lem-pur-ordinary-diagonal-tensor-point). -/
theorem ordinaryDiagonalTensorPoint
    (F B : Type u) [Field F] [Field B] [Algebra F B]
    (e : B ⊗[F] B) (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (hd : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    let U := ModuleCat.restrictScalars.{u} (algebraMap F B)
    let S := (((Functor.whiskeringLeft₂ (ModuleCat.{u} F)).obj U).obj U).obj
      (curriedTensor (ModuleCat.{u} F))
    let T := (Functor.postcompose₂.obj U).obj (curriedTensor (ModuleCat.{u} B))
    ∃ (a : (B ⊗[F] B) →+* End S) (s : T ⟶ S),
      s ≫ Functor.LaxMonoidal.μNatTrans U = 𝟙 _ ∧
      Functor.LaxMonoidal.μNatTrans U ≫ s = a e ∧
      ∀ (b c : B) (M N : ModuleCat.{u} B),
        ((a (b ⊗ₜ[F] c)).app M).app N = U.map (b • 𝟙 M) ⊗ₘ U.map (c • 𝟙 N) := by
  exact ⟨Native.ordinaryActionRing F B, Native.ordinarySection F B e hd,
    Native.ordinarySection_split F B e hμ hd, Native.ordinarySection_retract F B e hd,
    Native.ordinaryAction_pure F B⟩

#print axioms ordinaryDiagonalTensorPoint

end AlgebraicGeometry.Etale
