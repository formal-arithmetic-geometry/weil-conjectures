/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor
import Sheaf.AlgebraicGeometry.PicardConstantScalarExtensionSections

/-! # Balanced sections of scalar-extended constant tensor coefficients

Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
(blueprint: lem-sc-picard-constant-tensor-balanced-sections).
-/

@[expose] public section
universe w
open CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Scalar extension followed by tensoring with `G` has the usual balanced sections.
Source: Stacks Project, Varieties, Tag 0BED, degree-zero tensor calculation.
(blueprint: lem-sc-picard-constant-tensor-balanced-sections).

Proof: First construct the presheaf E with E(V) = O_Y(V) tensor_k M and
restriction a tensor s mapping to res(a) tensor s. For every O_Y-module
presheaf H, maps E to H correspond to maps from the constant M presheaf
to restriction of scalars of H: evaluate a map at 1 tensor s in one
direction, and send a tensor s to a times the image of s in the other.
The tensor relations prove well-definedness, and restriction compatibility
makes these inverse Hom equivalences natural in H. Thus E represents the
same Hom functor as the chosen PresheafOfModules.pullback value. Uniqueness
of representing objects identifies these presheaves by an O_Y-linear
isomorphism, compatible with restriction. Transport along this isomorphism
before applying the formulas below; no definitional pointwise computation
of the chosen left adjoint is assumed.
Associativity and balance identify (O_Y(V) tensor_k M) tensor_{O_Y(V)} G(V)
with M tensor_k G(V), sending (a tensor s) tensor t to s tensor (a*t).
The inverse sends s tensor t to (1 tensor s) tensor t. Tensor induction and
balance prove that these additive maps are inverse: balancing over O_Y(V)
moves a from the first tensor to t, while k-balance moves a k-scalar
between s and t. The composites fix (a tensor s) tensor t and s tensor t,
respectively; these pure tensors generate their additive groups. Multiplying by a section
of O_Y(V) on the source multiplies the second factor on the target, which is
the first identity below. Restricting the displayed pure-tensor formulas
restricts the ring coefficient and t while keeping s fixed. Tensor induction
gives the second identity. These arguments also apply to the empty open,
zero M, and zero G; no geometric hypothesis is needed. -/
theorem exists_picard_constant_tensor_balanced_sections
    (k : Type w) [Field k] (Y : Scheme.{w})
    (g : Y ⟶ Spec (CommRingCat.of k)) (M : ModuleCat.{w} k) (G : Y.Modules) :
    ∃ e : ∀ V : Y.Opens,
        (picardConstantSectionsTensor k Y g M G).obj (op V) ≃+
          (M ⊗[k] scalarObj g G (op V)),
      (∀ (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : scalarObj g G (op V)),
        e V (a • (e V).symm (s ⊗ₜ[k] t)) =
          s ⊗ₜ[k] (show scalarObj g G (op V) from a • (show G.val.obj (op V) from t))) ∧
      (∀ {U V : Y.Opensᵒᵖ} (i : U ⟶ V)
          (x : (picardConstantSectionsTensor k Y g M G).obj U),
        e V.unop ((picardConstantSectionsTensor k Y g M G).map i x) =
          ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i) (e U.unop x)) := by
  classical
  let tmul (V : Y.Opens) (a : Γ(Y, V)) (s : M) :
      (ModuleCat.extendScalars (scalarMap g V)).obj M := by
    let : Module k Γ(Y, V) := Module.compHom _ (scalarMap g V)
    exact TensorProduct.tmul k a s
  obtain ⟨q, hq⟩ := exists_picard_constant_scalar_extension_sections k Y g M
  let P := (PresheafOfModules.pullback (picardConstantRingMap k Y g)).obj
    (picardConstantVector k Y M)
  let e (V : Y.Opens) :
      (picardConstantSectionsTensor k Y g M G).obj (op V) ≃+
        (M ⊗[k] scalarObj g G (op V)) := by
    let : Algebra k Γ(Y, V) := (scalarMap g V).toAlgebra
    let : Module k (G.val.obj (op V)) := Module.compHom _ (scalarMap g V)
    let : IsScalarTower k Γ(Y, V) (G.val.obj (op V)) :=
      IsScalarTower.of_algebraMap_smul (fun a t ↦ rfl)
    exact (TensorProduct.congr (q V).symm (LinearEquiv.refl _ _)).toAddEquiv.trans
      ((TensorProduct.comm Γ(Y, V) _ _).toAddEquiv.trans
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange
          k Γ(Y, V) Γ(Y, V) (G.val.obj (op V)) M).toAddEquiv.trans
            (TensorProduct.comm k _ _).toAddEquiv))
  have he (V : Y.Opens) (a : Γ(Y, V)) (s : M) (t : G.val.obj (op V)) :
      e V ((q V (tmul V a s)) ⊗ₜ[Γ(Y, V)] t) =
        s ⊗ₜ[k] (show scalarObj g G (op V) from a • t) := by
    let : Algebra k Γ(Y, V) := (scalarMap g V).toAlgebra
    let : Module k (G.val.obj (op V)) := Module.compHom _ (scalarMap g V)
    let : IsScalarTower k Γ(Y, V) (G.val.obj (op V)) :=
      IsScalarTower.of_algebraMap_smul (fun a t ↦ rfl)
    simp [e, tmul]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro V a s t
    have hi : (e V).symm (s ⊗ₜ[k] t) =
        (q V (tmul V 1 s)) ⊗ₜ[Γ(Y, V)]
          (show G.val.obj (op V) from t) := by
      apply (e V).injective
      simp only [AddEquiv.apply_symm_apply, he, one_smul]
    rw [hi]
    change e V (a • (_ ⊗ₜ[Γ(Y, V)] _)) = _
    rw [← TensorProduct.tmul_smul]
    simpa only [one_smul] using he V 1 s (a • (show G.val.obj (op V) from t))
  · intro U V i x
    change e V.unop ((MonoidalCategory.tensorObj P G.val).map i x) = _
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul p t =>
      obtain ⟨z, rfl⟩ := (q U.unop).surjective p
      induction z using TensorProduct.induction_on with
      | zero =>
        simp only [map_zero, TensorProduct.zero_tmul]
      | add z z' hz hz' =>
        simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hz hz'
      | tmul a s =>
        change e V.unop (P.map i (q U.unop (tmul U.unop a s))
          ⊗ₜ[Γ(Y, V.unop)] G.val.map i t) = _
        rw [hq, he]
        change _ = ((scalarPresheaf g G ⋙ MonoidalCategory.tensorLeft M).map i)
          (e U.unop ((q U.unop (tmul U.unop a s))
            ⊗ₜ[Γ(Y, U.unop)] t))
        rw [he]
        change s ⊗ₜ[k] (show scalarObj g G V from
            (Y.presheaf.map i a) • G.val.map i t) =
          s ⊗ₜ[k] (show scalarObj g G V from G.val.map i (a • t))
        rw [G.val.map_smul]
        rfl

end AlgebraicGeometry.Scheme.Modules
