/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Ideal multiplication kernels under ordinary base change

Source: Stacks Project, Algebra, Tags 00MO, 00MM, 00MN and 00M6.
(blueprint: lem-weil-pbc-base-change-ideal-kernel-generators)
-/

@[expose] public section
universe u w t
open scoped TensorProduct
namespace Module

/-- Ordinary base change generates the ideal multiplication kernel when the quotient is flat.
Source: Stacks Project, Algebra, Tag 00MO, third proof paragraph, using Tags 00MM,
00MN and the connecting-map description of Tag 00M6.
(blueprint: lem-weil-pbc-base-change-ideal-kernel-generators)

Proof: write Q = R/I, J = IR', Q' = R'/J and N = R' tensor_R M.
Construct theta by the balanced bilinear rule a tensor x |-> rho(a) tensor (1 tensor x).
Tag 00MM for R -> Q -> Q' gives a canonical surjection from Tor_1(M,Q) tensor_Q Q'
to Tor_1(M,Q'); the flatness assumption is exactly the hypothesis of that tag.
Compose with the change-of-rings surjection of Tag 00MN. The connecting maps of
Tag 00M6 identify the target with ker(J tensor N -> N) and the original Tor with
ker(I tensor M -> M). Naturality identifies the map on generators with theta.
Since I annihilates the original Tor, tensoring this kernel over Q with Q' equals
tensoring it over R with R'. Every tensor is a finite sum of pure tensors, whose
images are R'-scalar multiples of theta(k). Tensor symmetry transfers this
statement into the displayed span. This constructs theta from its pure-tensor
formula, rather than choosing unspecified data from an existence assertion.
The zero ideal, unit ideal and zero base-change ring all give zero kernels. -/
theorem exists_baseChange_ideal_kernel_generators
    {R : Type u} {R' : Type w} [CommRing R] [CommRing R'] [Algebra R R']
    (I : Ideal R) (M : Type t) [AddCommGroup M] [Module R M]
    (hquot : Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)) :
    ∃ θ : I ⊗[R] M →+ (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M),
      (∀ (a : I) (x : M), θ (a ⊗ₜ[R] x) =
        (⟨algebraMap R R' a, Ideal.mem_map_of_mem (algebraMap R R') a.property⟩ :
          I.map (algebraMap R R')) ⊗ₜ[R'] ((1 : R') ⊗ₜ[R] x)) ∧
      (∀ y : (I.map (algebraMap R R')) ⊗[R'] (R' ⊗[R] M),
        TensorProduct.lift
          ((LinearMap.lsmul R' (R' ⊗[R] M)).comp
            (I.map (algebraMap R R')).subtype) y = 0 →
        TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) y ∈
          Submodule.span R'
            ((fun k : I ⊗[R] M ↦
              TensorProduct.comm R' (I.map (algebraMap R R')) (R' ⊗[R] M) (θ k)) ''
              (LinearMap.ker (TensorProduct.lift
                ((LinearMap.lsmul R M).comp I.subtype)) : Set (I ⊗[R] M)))) := by
  sorry

end Module
