/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups N9 and Q120
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Cofactor targets and normalized local formula data

Source: Stacks Project, duality.tex, Tag 0E9Y, displayed cofactor formula;
algebra.tex, Tags 0C6F, 00DL, 00CS, exterior, dual and cokernel scalar comparisons.
(blueprint: def-sfb-cofactor-local-data)

These definitions are extracted from CofactorLocalDescent without changing their data.
The target, normalized comparison structure and arbitrary-chart formula can be used
without assuming the existence and uniqueness theorem for a global cofactor map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w z

open scoped TensorProduct

namespace Module

/-- The displayed determinant target in Stacks Tag 0E9Y, in dual-first order.
(blueprint: def-sfb-cofactor-local-data). -/
abbrev CofactorTarget (A : Type u) [CommRing A] (P : Type v) (Q : Type w)
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q] (c : ℕ) :=
  Dual A (⋀[A]^c P) ⊗[A] (⋀[A]^(c + 1) Q)

/-- The local basis expression of Stacks Tag 0E9Y. The determinant pairing of the
coordinate forms is the functional dual to the ordered top basis wedge.
(blueprint: def-sfb-cofactor-local-data). -/
noncomputable def cofactorBasisValue {A : Type u} [CommRing A]
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] {c : ℕ}
    (u : P →ₗ[A] Q) (p : Module.Basis (Fin c) A P) (v : Q) :
    CofactorTarget A P Q c :=
  exteriorPower.pairingDual A P c (exteriorPower.ιMulti A c p.coord) ⊗ₜ[A]
    exteriorPower.ιMulti A (c + 1) (Fin.snoc (fun i ↦ u (p i)) v)

/-- The canonical scalar comparisons, including the quotient comparison, specified
by their values on spanning pure tensors. Source: Stacks Tags 0C6F, 00DL, 00CS;
the dual evaluation is the comparison used in Tag 0E9Y.
(blueprint: def-sfb-cofactor-local-data). -/
structure CofactorScalarComparison {A : Type u} [CommRing A]
    (B : Type z) [CommRing B] [Algebra A B]
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (u : P →ₗ[A] Q) (c : ℕ) where
  /-- Exterior comparison for the degree-c power of P. -/
  source : B ⊗[A] (⋀[A]^c P) ≃ₗ[B] (⋀[B]^c (B ⊗[A] P))
  /-- Pure-wedge normalization. -/
  source_wedge : ∀ (b : B) (x : Fin c → P),
    source (b ⊗ₜ[A] exteriorPower.ιMulti A c x) =
      b • exteriorPower.ιMulti B c (fun i ↦ 1 ⊗ₜ[A] x i)
  /-- Exterior comparison for the top power of Q. -/
  target : B ⊗[A] (⋀[A]^(c + 1) Q) ≃ₗ[B] (⋀[B]^(c + 1) (B ⊗[A] Q))
  /-- Pure-wedge normalization. -/
  target_wedge : ∀ (b : B) (x : Fin (c + 1) → Q),
    target (b ⊗ₜ[A] exteriorPower.ιMulti A (c + 1) x) =
      b • exteriorPower.ιMulti B (c + 1) (fun i ↦ 1 ⊗ₜ[A] x i)
  /-- Finite-projective dual comparison. -/
  dual : B ⊗[A] Dual A (⋀[A]^c P) ≃ₗ[B] Dual B (⋀[B]^c (B ⊗[A] P))
  /-- The comparison sends b tensor lambda to b b' lambda(x). -/
  dual_eval : ∀ (b b' : B) (l : Dual A (⋀[A]^c P)) (x : ⋀[A]^c P),
    dual (b ⊗ₜ[A] l) (source (b' ⊗ₜ[A] x)) = b * b' * algebraMap A B (l x)
  /-- Tensor of the dual and exterior comparisons. -/
  line : B ⊗[A] CofactorTarget A P Q c ≃ₗ[B]
    CofactorTarget B (B ⊗[A] P) (B ⊗[A] Q) c
  /-- Pure-tensor normalization; the scalar can be put in the first factor. -/
  line_tensor : ∀ (b : B) (l : Dual A (⋀[A]^c P)) (x : ⋀[A]^(c + 1) Q),
    line (b ⊗ₜ[A] (l ⊗ₜ[A] x)) = dual (b ⊗ₜ[A] l) ⊗ₜ[B] target (1 ⊗ₜ[A] x)
  /-- Exact scalar extension of the cokernel. -/
  cokernel : B ⊗[A] (Q ⧸ LinearMap.range u) ≃ₗ[B]
    ((B ⊗[A] Q) ⧸ LinearMap.range (u.baseChange B))
  /-- The cokernel comparison on a class represented by v. -/
  cokernel_class : ∀ (b : B) (v : Q),
    cokernel (b ⊗ₜ[A] (LinearMap.range u).mkQ v) =
      (LinearMap.range (u.baseChange B)).mkQ (b ⊗ₜ[A] v)

/-- The arbitrary-chart formula, with the scalar extension of the actual map on the
actual cokernel. It quantifies over every ordered basis and every lift, so it includes
basis and lift independence. Source: Stacks Tag 0E9Y.
(blueprint: def-sfb-cofactor-local-data). -/
def IsLocalCofactor {A : Type u} [CommRing A]
    {P : Type v} {Q : Type w} [AddCommGroup P] [Module A P]
    [AddCommGroup Q] [Module A Q] (u : P →ₗ[A] Q) (c : ℕ)
    (e : ∀ S : Submonoid A, CofactorScalarComparison (Localization S) u c)
    (w : (Q ⧸ LinearMap.range u) →ₗ[A] CofactorTarget A P Q c) : Prop :=
  ∀ (S : Submonoid A) (p : Module.Basis (Fin c) (Localization S) (Localization S ⊗[A] P))
      (v : Localization S ⊗[A] Q),
    (e S).line (w.baseChange (Localization S)
      ((e S).cokernel.symm ((LinearMap.range (u.baseChange (Localization S))).mkQ v))) =
    cofactorBasisValue (u.baseChange (Localization S)) p v

end Module
