/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.RingTheory.Trace.Basic
/-!
# Trace adjunction for finite separable coefficient fields

Source: the finite field trace argument in Bhatt--Scholze, Proposition 6.8.14(2),
used in the coefficient extension argument; the elementary algebraic step is an
agent elaboration (blueprint: lem-sf-finite-separable-module-trace-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory TensorProduct
namespace ModuleCat
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
private def traceTensorEquiv (M : ModuleCat.{v} K) :
    L ⊗[K] M ≃ₗ[K] (L →ₗ[K] M) :=
  TensorProduct.congr ((Algebra.traceForm K L).toDual (traceForm_nondegenerate K L))
    (LinearEquiv.refl K M) ≪≫ₗ dualTensorHomEquiv K L M
private def restrictedSelf :
    (restrictScalars (algebraMap K L)).obj (ModuleCat.of L L) ≃ₗ[K] L where
  toFun s := s
  invFun s := s
  map_add' _ _ := rfl
  map_smul' r s := (Algebra.smul_def r (show L from s)).symm
  left_inv _ := rfl
  right_inv _ := rfl
private def traceTensorCoextension (M : ModuleCat.{u} K) :
    (extendScalars (algebraMap K L)).obj M ≃ₗ[L]
      (coextendScalars (algebraMap K L)).obj M := by
  let e := ((TensorProduct.congr (restrictedSelf K L) (LinearEquiv.refl K M) ≪≫ₗ
      traceTensorEquiv K L M).toAddEquiv.trans
    ((restrictedSelf K L).symm.arrowCongrAddEquiv (LinearEquiv.refl K M))).trans
      (CoextendScalars.equiv (algebraMap K L) M).symm.toAddEquiv
  exact LinearEquiv.ofBijective
    ({ toFun := e
       map_add' := fun x y ↦ by
         exact e.map_add x y
       map_smul' := fun a z ↦ by
         apply CoextendScalars.ext
         apply LinearMap.ext
         intro (b : (restrictScalars (algebraMap K L)).obj (ModuleCat.of L L))
         induction z using TensorProduct.induction_on with
         | zero => simp [e]
         | tmul s m =>
           change Algebra.trace K L (restrictedSelf K L (a • s) * restrictedSelf K L b) • m =
             Algebra.trace K L (restrictedSelf K L s * (restrictedSelf K L b * a)) • m
           congr 2
           change (a * (show L from s)) * (show L from b) =
             (show L from s) * ((show L from b) * a)
           ring
         | add x y hx hy =>
           simpa only [smul_add, map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hx hy }
      : (extendScalars (algebraMap K L)).obj M →ₗ[L]
          (coextendScalars (algebraMap K L)).obj M)
    e.bijective
private def traceTensorCoextensionIso :
    extendScalars (algebraMap K L) ≅ coextendScalars (algebraMap K L) :=
  NatIso.ofComponents (fun M ↦ (traceTensorCoextension K L M).toModuleIso) (by
    intro M N f
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    apply CoextendScalars.ext
    apply LinearMap.ext
    intro (b : L)
    change Algebra.trace K L (1 * b) • f m =
      f (Algebra.trace K L (1 * b) • m)
    exact (f.hom.map_smul _ _).symm)
private def traceRestrictExtendAdjunction :
    restrictScalars (algebraMap K L) ⊣ extendScalars (algebraMap K L) :=
  (restrictCoextendScalarsAdj (algebraMap K L)).ofNatIsoRight
    (traceTensorCoextensionIso K L).symm

/-- Restriction is left adjoint to extension for a finite separable field extension.
Source: the trace step of the finite coefficient argument in Bhatt--Scholze,
Proposition 6.8.14(2) (agent elaboration).
(blueprint: lem-sf-finite-separable-module-trace-adjunction).

Proof: the nondegenerate trace form identifies L with its K-dual. Tensoring with
M and contracting gives L tensor_K M isomorphic to Hom_K(L,M). On pure tensors
this map sends s tensor m to the function b mapping to Tr(s*b)m. Commutativity
of L makes it L-linear for the coextension action, and K-linearity of module
morphisms makes it natural in M. Thus extension is naturally isomorphic to
coextension. Transport the usual restriction--coextension adjunction through
this natural isomorphism. This includes the zero module and the identity field
extension, and no choice of trace-dual basis is required. -/
theorem finiteSeparableTraceAdjunction :
    Nonempty (restrictScalars.{u, u, u} (algebraMap K L) ⊣
      extendScalars (algebraMap K L)) :=
  ⟨traceRestrictExtendAdjunction K L⟩
end ModuleCat
