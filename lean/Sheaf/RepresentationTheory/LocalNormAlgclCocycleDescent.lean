/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.RepresentationTheory.LAdic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular

/-! # Local finite-field normal form for continuous algebraic-closure cocycles

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic expansion: local cocycle input to finite-index transfer.
The blueprint does not prove this input; an exact higher-degree norm-topology
reference is WANTED (blueprint: lem-sfb-local-norm-algcl-cocycle-descent).

The cochains below are continuous functions, with the ordinary inhomogeneous
cocycle and coboundary equations written pointwise. The topology of each scalar
extension is Mathlib's module topology over its scalar field, hence the product
topology in any finite basis. The algebraic closure is not completed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Representation

/-- A continuous positive-degree cocycle over the norm-topological algebraic closure
is cohomologous, on some open subgroup, to a finite-field-valued continuous cocycle.
The parameter `n` denotes degree `n + 1`. In degree one, `b` is a continuous function
on the one-point space `H^0`, namely a single vector. The displayed equations use
`Fin.contractNth`: its interior faces multiply adjacent entries and its last face
drops the last entry. Thus the degree-zero differential is `g • v - v`.

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
agent arithmetic expansion; exact higher-degree norm-topology reference WANTED
(blueprint: lem-sfb-local-norm-algcl-cocycle-descent).

Proof:
1. Choose an E-basis of W and homogenize z by
   f(g0,...,gn) = g0 z(g0^-1 g1,...,g(n-1)^-1 gn). Equivariance, continuity,
   and the homogeneous cocycle equation follow from the displayed differential.
2. By lem-sfb-algcl-countable-closed-finite-cover, Omega is an increasing countable
   union of closed finite extensions F_j containing E. Their finite powers cover
   Omega^d, also when d=0. Apply lem-sfb-baire-closed-cover-interior to the inverse
   images under f in the nonempty compact Hausdorff space G^(degree+1). Some
   inverse image has nonempty interior.
3. Choose a product neighbourhood in that interior, with coordinates a_i. The
   profinite open-subgroup basis gives H with H a_i in each neighbourhood, so f
   takes values in F^d on the rectangle H a_0 times ... times H a_degree.
4. By lem-sfb-finite-subfield-continuous-linear-retraction choose a continuous
   E-linear retraction p: Omega -> F, and apply it coordinatewise. It commutes
   with the E-valued action matrices. Thus (1-p)f is a continuous equivariant
   homogeneous cocycle vanishing on the rectangle. Apply
   lem-sfb-homogeneous-cocycle-rectangle-detection to write its restriction as
   the homogeneous coboundary of a continuous equivariant cochain t.
5. Put u = pz restricted to H, and dehomogenize t to b by evaluation at
   (1,h1,h1*h2,...). Then du=0 and z restricted to H equals u+db under the
   canonical coefficient inclusion. When the degree is one, b=t(1).
   No closure of the coboundaries or identification with derived invariants is used.
-/
theorem local_norm_algcl_cocycle_descent
    (l : ℕ) [Fact l.Prime] (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (E : IntermediateField ℚ_[l] Ω)
    [FiniteDimensional ℚ_[l] E] (G : ProfiniteGrp.{v})
    (W : Type w) [AddCommGroup W] [Module E W]
    (ρ : G →* (W ≃ₗ[E] W)) (hρ : IsContinuousCoefficient l E G W ρ)
    (n : ℕ)
    (z : @ContinuousMap (Fin (n + 1) → G) (Ω ⊗[E] W) inferInstance
      (moduleTopology Ω (Ω ⊗[E] W)))
    (hz : ∀ g : Fin (n + 2) → G,
      coefficientScalarExtension E Ω G W ρ (g 0) (z (fun i ↦ g i.succ)) +
        ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j.val + 1) •
          z (Fin.contractNth j (· * ·) g) = 0) :
    ∃ (H : OpenSubgroup G) (F : IntermediateField E Ω)
      (_ : FiniteDimensional E F)
      (u : @ContinuousMap (Fin (n + 1) → H) (F ⊗[E] W) inferInstance
        (moduleTopology F (F ⊗[E] W)))
      (b : @ContinuousMap (Fin n → H) (Ω ⊗[E] W) inferInstance
        (moduleTopology Ω (Ω ⊗[E] W))),
      (∀ g : Fin (n + 2) → H,
        coefficientScalarExtension E F G W ρ (g 0 : G) (u (fun i ↦ g i.succ)) +
          ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j.val + 1) •
            u (Fin.contractNth j (· * ·) g) = 0) ∧
      ∀ g : Fin (n + 1) → H,
        z (fun i ↦ (g i : G)) =
          TensorProduct.map (IsScalarTower.toAlgHom E F Ω).toLinearMap
            (LinearMap.id : W →ₗ[E] W) (u g) +
          (coefficientScalarExtension E Ω G W ρ (g 0 : G) (b (fun i ↦ g i.succ)) +
            ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
              b (Fin.contractNth j (· * ·) g)) := by
  sorry

end Representation
