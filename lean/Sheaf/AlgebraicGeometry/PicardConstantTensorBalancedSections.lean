/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.PicardConstantSectionsTensor

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
  sorry

end AlgebraicGeometry.Scheme.Modules
