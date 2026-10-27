/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q129
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtUniqueness

/-! # Inverse formulas for insertion-normalized scalar tensor maps

Source: Stacks Project, Modules on Sites, Section 03EK and Tag 0GMW,
with the explicit balanced inverse calculation in the node's proof.
(blueprint: lem-pd-sheaf-scalar-tensor-inverse-formulas)

The tensor objects are the existing sheafifications `siteSheafTensorRight.{u, u, u, u}`.
The existing `scalarExtensionRingIsoTmul α X U x s` is the section denoted
`τ_X(s,x)` in the node; its definition does not require a ring isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace SheafOfModules

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped ChangeOfRings TensorProduct

private abbrev Mod {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

section Calculus
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

private noncomputable def sheafUnit (R : Sheaf J CommRingCat.{u})
    (P : PresheafOfModules.{u} (R.obj ⋙ forget₂ CommRingCat RingCat)) :
    P ⟶ ((PresheafOfModules.sheafification
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).obj P).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).unit.app P

private noncomputable def tensorUnit {R : Sheaf J CommRingCat.{u}} (M N : Mod R) :
    siteTensorPresheaf M.val N.val ⟶ ((siteSheafTensorRight.{u, u, u, u} N).obj M).val :=
  sheafUnit R (siteTensorPresheaf M.val N.val)

private noncomputable def tensorBilin {R : Sheaf J CommRingCat.{u}} (M N : Mod R)
    (U : Cᵒᵖ) : M.val.obj U →ₗ[R.obj.obj U] N.val.obj U →ₗ[R.obj.obj U]
      ((siteSheafTensorRight.{u, u, u, u} N).obj M).val.obj U :=
  TensorProduct.curry ((tensorUnit M N).app U).hom

private theorem tensor_restrict {R : Sheaf J CommRingCat.{u}} (M N : Mod R)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    siteSheafTensorTmul.{u, u, u, u} M N V (M.val.map i x) (N.val.map i y) =
      ((siteSheafTensorRight.{u, u, u, u} N).obj M).val.map i (siteSheafTensorTmul.{u, u, u, u} M N
        U x y) :=
  PresheafOfModules.naturality_apply (tensorUnit M N) i (x ⊗ₜ[R.obj.obj U] y)

private noncomputable def tensorLift {R : Sheaf J CommRingCat.{u}}
    (M N P : Mod R)
    (β : ∀ U : Cᵒᵖ, M.val.obj U →ₗ[R.obj.obj U]
      N.val.obj U →ₗ[R.obj.obj U] P.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U),
      β V (M.val.map i x) (N.val.map i y) = P.val.map i (β U x y)) :
    (siteSheafTensorRight.{u, u, u, u} N).obj M ⟶ P :=
  (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)).homEquiv _ P |>.symm
    { app := fun U ↦ ModuleCat.ofHom (TensorProduct.lift (β U))
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        ext z
        change TensorProduct.lift (β V) ((siteTensorPresheaf M.val N.val).map i z) =
          P.val.map i (TensorProduct.lift (β U) z)
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul x y => exact hβ i x y
        | add z w hz hw => simp only [map_add, hz, hw] }

private theorem tensorLift_apply {R : Sheaf J CommRingCat.{u}}
    (M N P : Mod R)
    (β : ∀ U : Cᵒᵖ, M.val.obj U →ₗ[R.obj.obj U]
      N.val.obj U →ₗ[R.obj.obj U] P.val.obj U)
    (hβ : ∀ {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U),
      β V (M.val.map i x) (N.val.map i y) = P.val.map i (β U x y))
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (tensorLift M N P β hβ).val.app U (siteSheafTensorTmul.{u, u, u, u} M N U x y) = β U x y := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R) (𝟙 _)
  let q : siteTensorPresheaf M.val N.val ⟶ P.val :=
    (adj.homEquiv _ P) (tensorLift M N P β hβ)
  have h : q =
      { app := fun U ↦ ModuleCat.ofHom (TensorProduct.lift (β U))
        naturality := by
          intro U V i
          ext z
          change TensorProduct.lift (β V) ((siteTensorPresheaf M.val N.val).map i z) =
            P.val.map i (TensorProduct.lift (β U) z)
          induction z using TensorProduct.induction_on with
          | zero => simp only [map_zero]
          | tmul x y => exact hβ i x y
          | add z w hz hw => simp only [map_add, hz, hw] } :=
    (adj.homEquiv _ P).apply_symm_apply _
  exact congrArg (fun f : siteTensorPresheaf M.val N.val ⟶ P.val ↦
    f.app U (x ⊗ₜ[R.obj.obj U] y)) h

private theorem tensor_ext {R : Sheaf J CommRingCat.{u}} (M N P : Mod R)
    {f g : (siteSheafTensorRight.{u, u, u, u} N).obj M ⟶ P}
    (h : ∀ U (x : M.val.obj U) (y : N.val.obj U),
      f.val.app U (siteSheafTensorTmul.{u, u, u, u} M N U x y) =
        g.val.app U (siteSheafTensorTmul.{u, u, u, u} M N U x y)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (𝟙 _)).homEquiv _ P |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  exact h U

private theorem tau_smul {A S : Sheaf J CommRingCat.{u}} (α : A ⟶ S) (M : Mod A)
    (U : Cᵒᵖ) (x : M.val.obj U) (s t : S.obj.obj U) :
    scalarExtensionRingIsoTmul.{u, u, u, u} α M U x (s * t) =
      s • scalarExtensionRingIsoTmul.{u, u, u, u} α M U x t := by
  change (sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α M)).app U
    ((s * t) ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] x) = _
  exact map_smul ((sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α M)).app U).hom s
    (t ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] x)

private theorem tau_restrict {A S : Sheaf J CommRingCat.{u}} (α : A ⟶ S) (M : Mod A)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) (s : S.obj.obj U) :
    scalarExtensionRingIsoTmul.{u, u, u, u} α M V (M.val.map i x) (S.obj.map i s) =
      (changeOfRingsOfUniverses.{u, u, u, u} α M).val.map i (scalarExtensionRingIsoTmul.{u, u, u,
        u} α M U x s) := by
  have h := PresheafOfModules.naturality_apply
    (sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α M)) i
    (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] x)
  rw [show (changeOfRingsPresheafOfUniverses.{u, u, u, u} α M).map i _ = _ from
    changeOfRingsMap_tmulOfUniverses α M i s x] at h
  exact h

private noncomputable def scalarRestrict {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (M : Mod A) (P : Mod S) (f : changeOfRingsOfUniverses.{u, u, u, u} α M ⟶ P) :
    M ⟶ (restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α)).obj P where
  val :=
    { app := fun U ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (α.hom.app U).hom ((sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α M)).app U ≫
          f.val.app U)
      naturality := by
        intro U V i
        ext x
        change f.val.app V (scalarExtensionRingIsoTmul.{u, u, u, u} α M V (M.val.map i x) 1) =
          P.val.map i (f.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α M U x 1))
        have h := tau_restrict α M i x 1
        rw [map_one] at h
        rw [h]
        exact PresheafOfModules.naturality_apply f.val i _ }

private theorem scalar_ext {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (M : Mod A) (P : Mod S)
    {f g : changeOfRingsOfUniverses.{u, u, u, u} α M ⟶ P}
    (h : ∀ U (x : M.val.obj U), f.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α M U x 1) =
      g.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α M U x 1)) : f = g := by
  apply (PresheafOfModules.sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
    (𝟙 _)).homEquiv _ P |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.ExtendScalars.hom_ext
  exact h U

private noncomputable def rawPairing {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (H K : Mod A) (U : Cᵒᵖ) :
    (changeOfRingsPresheafOfUniverses.{u, u, u, u} α H).obj U →ₗ[S.obj.obj U]
      (changeOfRingsPresheafOfUniverses.{u, u, u, u} α K).obj U →ₗ[S.obj.obj U]
        (changeOfRingsOfUniverses.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj
          H)).val.obj U := by
  let := (α.hom.app U).hom.toAlgebra
  exact TensorProduct.curry
    (((sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α
      ((siteSheafTensorRight.{u, u, u, u} K).obj H))).app U).hom.comp
      (((ModuleCat.extendScalars (α.hom.app U).hom).map
        ((tensorUnit H K).app U)).hom.comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange
            (A.obj.obj U) (S.obj.obj U) (H.val.obj U) (K.val.obj U)).symm.toLinearMap))

private theorem rawPairing_tmul {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (H K : Mod A) (U : Cᵒᵖ)
    (s t : S.obj.obj U) (h : H.val.obj U) (k : K.val.obj U) :
    rawPairing α H K U
      (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] h)
      (t ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] k) =
    scalarExtensionRingIsoTmul.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H) U
      (siteSheafTensorTmul.{u, u, u, u} H K U h k) (s * t) := by
  let := (α.hom.app U).hom.toAlgebra
  change (sheafUnit S (changeOfRingsPresheafOfUniverses.{u, u, u, u} α
    ((siteSheafTensorRight.{u, u, u, u} K).obj H))).app U
    (((ModuleCat.extendScalars (α.hom.app U).hom).map ((tensorUnit H K).app U))
      ((TensorProduct.AlgebraTensorModule.distribBaseChange
        (A.obj.obj U) (S.obj.obj U) (H.val.obj U) (K.val.obj U)).symm
          ((s ⊗ₜ[A.obj.obj U] h) ⊗ₜ[S.obj.obj U] (t ⊗ₜ[A.obj.obj U] k)))) = _
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
  rfl

private theorem rawPairing_restrict {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (H K : Mod A) {U V : Cᵒᵖ} (i : U ⟶ V)
    (x : (changeOfRingsPresheafOfUniverses.{u, u, u, u} α H).obj U)
    (y : (changeOfRingsPresheafOfUniverses.{u, u, u, u} α K).obj U) :
    rawPairing α H K V ((changeOfRingsPresheafOfUniverses.{u, u, u, u} α H).map i x)
      ((changeOfRingsPresheafOfUniverses.{u, u, u, u} α K).map i y) =
    (changeOfRingsOfUniverses.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H)).val.map
      i
      (rawPairing α H K U x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul s h =>
    change S.obj.obj U at s
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul t k =>
      change S.obj.obj U at t
      change rawPairing α H K V (changeOfRingsMapOfUniverses α H i _)
        (changeOfRingsMapOfUniverses α K i _) = _
      rw [changeOfRingsMap_tmulOfUniverses α H i s h,
        changeOfRingsMap_tmulOfUniverses α K i t k,
        rawPairing_tmul, rawPairing_tmul, ← tau_restrict, map_mul, ← tensor_restrict]

private theorem tensor_smul_left {R : Sheaf J CommRingCat.{u}} (M N : Mod R)
    (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    siteSheafTensorTmul.{u, u, u, u} M N U (s • x) y = s • siteSheafTensorTmul.{u, u, u, u} M N U x
      y :=
  (tensorBilin M N U).map_smul₂ s x y

private theorem tensor_smul_right {R : Sheaf J CommRingCat.{u}} (M N : Mod R)
    (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    siteSheafTensorTmul.{u, u, u, u} M N U x (s • y) = s • siteSheafTensorTmul.{u, u, u, u} M N U x
      y :=
  (tensorBilin M N U x).map_smul s y

private noncomputable def mappedPairing {R : Sheaf J CommRingCat.{u}}
    (M N P : Mod R) (f : (siteSheafTensorRight.{u, u, u, u} N).obj M ⟶ P) (U : Cᵒᵖ) :
    M.val.obj U →ₗ[R.obj.obj U] N.val.obj U →ₗ[R.obj.obj U] P.val.obj U :=
  TensorProduct.curry ((f.val.app U).hom.comp ((tensorUnit M N).app U).hom)

private theorem mappedPairing_restrict {R : Sheaf J CommRingCat.{u}}
    (M N P : Mod R) (f : (siteSheafTensorRight.{u, u, u, u} N).obj M ⟶ P)
    {U V : Cᵒᵖ} (i : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    mappedPairing M N P f V (M.val.map i x) (N.val.map i y) =
      P.val.map i (mappedPairing M N P f U x y) := by
  change f.val.app V (siteSheafTensorTmul.{u, u, u, u} M N V (M.val.map i x) (N.val.map i y)) = _
  rw [tensor_restrict]
  exact PresheafOfModules.naturality_apply f.val i _

private theorem extendedTensor_ext {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (H K : Mod A) (P : Mod S)
    {f g : changeOfRingsOfUniverses.{u, u, u, u} α
      ((siteSheafTensorRight.{u, u, u, u} K).obj H) ⟶ P}
    (h : ∀ U (x : H.val.obj U) (y : K.val.obj U),
      f.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α _ U (siteSheafTensorTmul.{u, u, u, u}
        H K U x y) 1) =
      g.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α _ U (siteSheafTensorTmul.{u, u, u, u}
        H K U x y) 1)) :
    f = g := by
  apply scalar_ext α _ P
  have he : scalarRestrict α _ P f = scalarRestrict α _ P g := by
    apply tensor_ext H K
    exact h
  intro U x
  exact congrArg (fun a ↦ a.val.app U x) he

private theorem tau_one {A S : Sheaf J CommRingCat.{u}} (α : A ⟶ S) (M : Mod A)
    (U : Cᵒᵖ) (x : M.val.obj U) (s : S.obj.obj U) :
    scalarExtensionRingIsoTmul.{u, u, u, u} α M U x s =
      s • scalarExtensionRingIsoTmul.{u, u, u, u} α M U x 1 := by
  simpa only [mul_one] using tau_smul α M U x s 1

private theorem scalarTensor_ext {A S : Sheaf J CommRingCat.{u}}
    (α : A ⟶ S) (H K : Mod A) (P : Mod S)
    {f g : (siteSheafTensorRight.{u, u, u, u}
      (changeOfRingsOfUniverses.{u, u, u, u} α K)).obj
      (changeOfRingsOfUniverses.{u, u, u, u} α H) ⟶ P}
    (h : ∀ U (x : H.val.obj U) (y : K.val.obj U),
      f.val.app U (siteSheafTensorTmul.{u, u, u, u} _ _ U
        (scalarExtensionRingIsoTmul.{u, u, u, u} α H U x 1)
          (scalarExtensionRingIsoTmul.{u, u, u, u} α K U y 1)) =
      g.val.app U (siteSheafTensorTmul.{u, u, u, u} _ _ U
        (scalarExtensionRingIsoTmul.{u, u, u, u} α H U x 1)
          (scalarExtensionRingIsoTmul.{u, u, u, u} α K U y 1))) :
    f = g := by
  have := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  have := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  have he := PresheafOfModules.unique_bilinear_sheafification_extension
    S.obj S (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
      (changeOfRingsPresheafOfUniverses.{u, u, u, u} α H)
      (changeOfRingsPresheafOfUniverses.{u, u, u, u} α K) P
      (γ := mappedPairing _ _ P f) (δ := mappedPairing _ _ P g)
      (fun {_ _} i x y ↦ mappedPairing_restrict _ _ P f i x y)
      (fun {_ _} i x y ↦ mappedPairing_restrict _ _ P g i x y) ?_
  · apply tensor_ext _ _ P
    intro U x y
    exact congrArg (fun a ↦ a U x y) he
  · intro U x y
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | tmul s x =>
      change S.obj.obj U at s
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | tmul t y =>
        change S.obj.obj U at t
        change f.val.app U (siteSheafTensorTmul.{u, u, u, u} _ _ U
          (scalarExtensionRingIsoTmul.{u, u, u, u} α H U x s)
          (scalarExtensionRingIsoTmul.{u, u, u, u} α K U y t)) =
          g.val.app U (siteSheafTensorTmul.{u, u, u, u} _ _ U
            (scalarExtensionRingIsoTmul.{u, u, u, u} α H U x s)
            (scalarExtensionRingIsoTmul.{u, u, u, u} α K U y t))
        rw [tau_one α H U x s, tau_one α K U y t,
          tensor_smul_left, tensor_smul_right, map_smul, map_smul,
          map_smul, map_smul, h]

end Calculus

attribute [local irreducible] siteSheafTensorRight

/-- Any insertion-normalized scalar tensor map is an isomorphism, with the forward
formula and the inverse formula multiplying the two scalar coefficients.
Source: Stacks Project, Modules on Sites, Section 03EK and Tag 0GMW.
(blueprint: lem-pd-sheaf-scalar-tensor-inverse-formulas)

Proof:
1. Balancing gives `q_X(a x) = α(a) q_X(x)` and `τ_X(s,x) = s q_X(x)`.
   Linearity of `b` and its insertion normalization give the forward formula
   [def-weil-pbc-module-tensor-product, def-weil-presheaf-modules-sheafification,
   def-pur-sheaf-tensor-product].
2. On the sectionwise extension presheaves define the pairing
   `(s ⊗ h, t ⊗ k) ↦ τ_(H ⊗ K)(st,h ⊗ k)`. Additivity and the two balancing
   relations make it well-defined. Commutativity of the target ring makes it
   bilinear over that ring [def-weil-pbc-module-tensor-product].
3. Restriction of all four factors commutes with the displayed pairing on pure
   tensors. Ordinary tensor generation extends this to all presheaf sections.
4. Extend this bilinear pairing uniquely through both module sheafification units
   [lem-pc-sites-module-sheafification-bilinear-extension], then use the sheaf
   tensor universal property, implemented directly by `tensorLift` using the
   module-sheafification adjunction and the ordinary tensor universal property.
   This constructs an S-linear sheaf map `d` with the asserted inverse formula.
5. To prove `b ≫ d = 𝟙`, use the sheafification universal property, ordinary
   tensor generation and then the sheaf tensor universal property over A.
   On insertions of `h ⊗ k` the composite is `τ(1,h ⊗ k)` by normalization.
6. To prove `d ≫ b = 𝟙`, use the sheaf tensor universal property over S and
   uniqueness of bilinear extension to reduce to the original presheaves.
   Tensor generation and S-bilinearity reduce to `(1 ⊗ h,1 ⊗ k)`.
   The inverse formula followed by the given normalization fixes this pair.
   Thus `d` is the inverse as an S-linear sheaf morphism. No step assumes
   surjectivity of a sheafification unit on sections, flatness or nonzero rings. -/
theorem scalarTensor_inverse_formulas
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (A S : Sheaf J CommRingCat.{u}) (α : A ⟶ S)
    (H K : ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A))
    (b : changeOfRingsOfUniverses.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H) ⟶
      (siteSheafTensorRight.{u, u, u, u} (changeOfRingsOfUniverses.{u, u, u, u} α K)).obj
        (changeOfRingsOfUniverses.{u, u, u, u} α H))
    (hb : ∀ (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U),
      b.val.app U
          (scalarExtensionRingIsoTmul.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H) U
            (siteSheafTensorTmul.{u, u, u, u} H K U h k) 1) =
        siteSheafTensorTmul.{u, u, u, u} (changeOfRingsOfUniverses.{u, u, u, u} α H)
          (changeOfRingsOfUniverses.{u, u, u, u} α K)
          U (scalarExtensionRingIsoTmul.{u, u, u, u} α H U h 1)
            (scalarExtensionRingIsoTmul.{u, u, u, u} α K U k 1)) :
    ∃ e : changeOfRingsOfUniverses.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H) ≅
        (siteSheafTensorRight.{u, u, u, u} (changeOfRingsOfUniverses.{u, u, u, u} α K)).obj
          (changeOfRingsOfUniverses.{u, u, u, u} α H),
      e.hom = b ∧
      (∀ (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U) (s : S.obj.obj U),
        b.val.app U
            (scalarExtensionRingIsoTmul.{u, u, u, u} α
              ((siteSheafTensorRight.{u, u, u, u} K).obj H) U
              (siteSheafTensorTmul.{u, u, u, u} H K U h k) s) =
          siteSheafTensorTmul.{u, u, u, u} (changeOfRingsOfUniverses.{u, u, u, u} α H)
          (changeOfRingsOfUniverses.{u, u, u, u} α K)
            U (scalarExtensionRingIsoTmul.{u, u, u, u} α H U h s)
              (scalarExtensionRingIsoTmul.{u, u, u, u} α K U k 1)) ∧
      (∀ (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U) (s t : S.obj.obj U),
        e.inv.val.app U
            (siteSheafTensorTmul.{u, u, u, u} (changeOfRingsOfUniverses.{u, u, u, u} α H)
              (changeOfRingsOfUniverses.{u, u, u, u} α K) U
              (scalarExtensionRingIsoTmul.{u, u, u, u} α H U h s)
              (scalarExtensionRingIsoTmul.{u, u, u, u} α K U k t)) =
          scalarExtensionRingIsoTmul.{u, u, u, u} α ((siteSheafTensorRight.{u, u, u, u} K).obj H) U
            (siteSheafTensorTmul.{u, u, u, u} H K U h k) (s * t)) := by
  let L := (siteSheafTensorRight.{u, u, u, u} K).obj H
  let TH := changeOfRingsOfUniverses.{u, u, u, u} α H
  let TK := changeOfRingsOfUniverses.{u, u, u, u} α K
  let V := changeOfRingsOfUniverses.{u, u, u, u} α L
  let W := (siteSheafTensorRight.{u, u, u, u} TK).obj TH
  have forward (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U) (s : S.obj.obj U) :
      b.val.app U (scalarExtensionRingIsoTmul.{u, u, u, u} α L U (siteSheafTensorTmul.{u, u, u, u}
        H K U h k) s) =
        siteSheafTensorTmul.{u, u, u, u} TH TK U (scalarExtensionRingIsoTmul.{u, u, u, u} α H U h s)
          (scalarExtensionRingIsoTmul.{u, u, u, u} α K U k 1) := by
    rw [tau_one α L U _ s, map_smul, hb, tau_one α H U h s, tensor_smul_left]
  have := siteTensor_identity_locallyInjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  have := siteTensor_identity_locallySurjective
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
  obtain ⟨γ, hγ, _⟩ := PresheafOfModules.existsUnique_bilinear_sheafification_extension
    S.obj S (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)
      (changeOfRingsPresheafOfUniverses.{u, u, u, u} α H)
      (changeOfRingsPresheafOfUniverses.{u, u, u, u} α K) V
      (rawPairing α H K) (rawPairing_restrict α H K)
  let d : W ⟶ V := tensorLift TH TK V γ hγ.1
  have hd (U : Cᵒᵖ) (h : H.val.obj U) (k : K.val.obj U) (s t : S.obj.obj U) :
      d.val.app U (siteSheafTensorTmul.{u, u, u, u} TH TK U 
        (scalarExtensionRingIsoTmul.{u, u, u, u} α H U h s)
        (scalarExtensionRingIsoTmul.{u, u, u, u} α K U k t)) =
      scalarExtensionRingIsoTmul.{u, u, u, u} α L U 
        (siteSheafTensorTmul.{u, u, u, u} H K U h k) (s * t) := by
    rw [tensorLift_apply]
    exact (hγ.2 U (s ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] h)
      (t ⊗ₜ[A.obj.obj U, (α.hom.app U).hom] k)).trans (rawPairing_tmul α H K U s t h k)
  have hbd : b ≫ d = 𝟙 V := by
    apply extendedTensor_ext α H K V
    intro U h k
    change d.val.app U (b.val.app U _) = _
    rw [hb, hd, one_mul]
    rfl
  have hdb : d ≫ b = 𝟙 W := by
    apply scalarTensor_ext α H K W
    intro U h k
    change b.val.app U (d.val.app U _) = _
    rw [hd, one_mul, hb]
    rfl
  exact ⟨⟨b, d, hbd, hdb⟩, rfl, forward, hd⟩

end SheafOfModules
