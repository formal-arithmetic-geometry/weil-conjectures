/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecTraceFormula.TwoTermDeterminantEncoding
public import Sheaf.LinearAlgebra.ProjectiveDeterminantExactSequence
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Sheaf.RingTheory.LineModuleDuality
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-!
# Kernel normalization for two-term determinant lines

Source: Stacks Project, More on Algebra, Tag 0FJI, construction preceding Tag 0FJJ,
and Tag 0FJB (blueprint: lem-trf-two-term-kernel-normalization).

The independent arrow-category encoding supplies the two-term complexes and their
kernel differential. This module fixes the assembly by its pure-tensor formula using
the canonical kernel-first maps, and fixes the kernel element by contraction with
every negative-degree determinant vector.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory
open scoped TensorProduct

namespace Module

/-- The canonical assembly and kernel determinant element, with a common pair of
kernel-first exact-sequence maps. The pure-tensor identity is precisely tensoring
`γzero` with the inverse dual of `γneg`. Contraction of `δ` is the exterior map of
the restricted differential, rather than an arbitrary generator of the kernel line.
Source: Stacks Project, More on Algebra, Tags 0FJI and 0FJB
(blueprint: lem-trf-two-term-kernel-normalization). -/
def IsKernelNormalizedAssembly {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q)
    (Γ : TwoTerm.determinant Q ⊗[R] TwoTerm.kernelDeterminant a ≃ₗ[R]
      TwoTerm.determinant P)
    (δ : TwoTerm.kernelDeterminant a)
    (T : TwoTerm.determinant P ≃ₗ[R] TwoTerm.determinant Q) : Prop :=
  ∃ (γneg :
      (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.left)) ⊗[R]
        Module.determinantModule R (Q.left : Type v)) ≃ₗ[R]
        Module.determinantModule R (P.left : Type v))
    (γzero :
      (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.right)) ⊗[R]
        Module.determinantModule R (Q.right : Type v)) ≃ₗ[R]
        Module.determinantModule R (P.right : Type v)),
    Module.IsDeterminantExactSequenceMap (Submodule.subtype _)
      (ModuleCat.Hom.hom a.left) γneg ∧
    Module.IsDeterminantExactSequenceMap (Submodule.subtype _)
      (ModuleCat.Hom.hom a.right) γzero ∧
    (∀ (qzero : Module.determinantModule R (Q.right : Type v))
      (φq : Module.Dual R (Module.determinantModule R (Q.left : Type v)))
      (nzero : Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.right)))
      (φn : Module.Dual R
        (Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.left)))),
      Γ ((qzero ⊗ₜ[R] φq) ⊗ₜ[R] (nzero ⊗ₜ[R] φn)) =
        γzero (nzero ⊗ₜ[R] qzero) ⊗ₜ[R]
          ((TensorProduct.lift (φn.smulRight φq)).comp γneg.symm.toLinearMap)) ∧
    (∀ (nneg : Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.left)))
      (nzero : Module.determinantModule R (LinearMap.ker (ModuleCat.Hom.hom a.right))),
      ExteriorAlgebra.map (TwoTerm.kernelDifferential a) nneg.val = nzero.val →
      TensorProduct.rid R _
        (TensorProduct.map LinearMap.id (LinearMap.applyₗ nneg) δ) = nzero) ∧
    Submodule.span R ({δ} : Set (TwoTerm.kernelDeterminant a)) = ⊤ ∧
    (∀ x : TwoTerm.determinant Q, T (Γ (x ⊗ₜ[R] δ)) = x) ∧
    (∀ S : TwoTerm.determinant P ≃ₗ[R] TwoTerm.determinant Q,
      (∀ x : TwoTerm.determinant Q, S (Γ (x ⊗ₜ[R] δ)) = x) → S = T)

/-- Kernel normalization for a degreewise-surjective quasi-isomorphism of two-term
finite-projective complexes.  The kernel terms are finite projective and the restricted
differential is an isomorphism.  The canonical short-exact-sequence determinant maps in
both degrees, tensoring with the inverse dual in the negative degree, give an assembly
`Γ : D(Q) ⊗ D(N) ≃ D(P)`.  The determinant element `δ` of the kernel differential spans
`D(N)`, and insertion of `δ` gives an isomorphism `D(Q) ≃ D(P)` with unique inverse `T`.
Source: Stacks Project, More on Algebra, Tag 0FJI, construction preceding Tag 0FJJ,
and Tag 0FJB (blueprint: lem-trf-two-term-kernel-normalization).

Proof, following the seven steps of the node:
1. Lift the identity of each quotient term by projectivity. The maps `(n,q) ↦ n+s(q)`
and `p ↦ (p-s(a(p)),a(p))` split the sequences, making the kernels direct summands
of finite projective modules, hence finite projective.
2. A vector in the kernel of the restricted differential is a degree-minus-one cycle
whose cohomology image is zero. Injectivity on that cohomology makes the vector zero.
3. For a degree-zero kernel vector y, injectivity on cokernels gives y=d(p).
Then a(p) is a cycle. Surjectivity on degree-minus-one cycles gives a cycle z with
a(z)=a(p), so p-z lies in the negative kernel and has differential y. Thus d_N is bijective.
4. Apply `Module.existsUnique_determinantExactSequence` to both split sequences for
the canonical kernel-first maps. Its determinant modules are finite projective lines.
5. Use `lTensorHomEquivHomLTensor` and finite-projective duality to tensor the zero-degree
map with the inverse dual of the negative-degree map. Ordinary tensor symmetry gives
exactly the displayed pure-tensor formula for Γ, without a graded sign.
6. On finite standard free covers, the exterior maps of d_N and its inverse preserve
the determinant socles and are inverse. Chart descent identifies these with the local
top exterior maps. Tensor-Hom identifies this map with the unique δ whose evaluation
at nneg is nzero whenever the exterior map sends nneg to nzero. Line-module duality
identifies scalar endomorphisms with all endomorphisms of the negative determinant line.
It follows that R → D(N), r ↦ r • δ, is an isomorphism: δ spans D(N).
7. Tensor that trivialization with D(Q), remove the right unitor and apply Γ.
This gives the isomorphism x ↦ Γ(x ⊗ δ). Take its inverse T. For any other inverse S,
S = S F T = T. All constructions include zero-rank terms, varying local rank,
characteristic two and the zero ring.
-/
theorem two_term_kernel_normalization {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q)
    [Module.Finite R P.left] [Module.Projective R P.left]
    [Module.Finite R P.right] [Module.Projective R P.right]
    [Module.Finite R Q.left] [Module.Projective R Q.left]
    [Module.Finite R Q.right] [Module.Projective R Q.right]
    (ha : TwoTerm.DegreewiseSurjective a) (hqa : TwoTerm.QuasiIso a) :
    Module.Finite R (LinearMap.ker (ModuleCat.Hom.hom a.left)) ∧
    Module.Projective R (LinearMap.ker (ModuleCat.Hom.hom a.left)) ∧
    Module.Finite R (LinearMap.ker (ModuleCat.Hom.hom a.right)) ∧
    Module.Projective R (LinearMap.ker (ModuleCat.Hom.hom a.right)) ∧
    (∃ s : (Q.left : Type v) →ₗ[R] (P.left : Type v),
      ModuleCat.Hom.hom a.left ∘ₗ s = LinearMap.id) ∧
    (∃ s : (Q.right : Type v) →ₗ[R] (P.right : Type v),
      ModuleCat.Hom.hom a.right ∘ₗ s = LinearMap.id) ∧
    Function.Bijective (TwoTerm.kernelDifferential a) ∧
    ∃! T : TwoTerm.determinant P ≃ₗ[R] TwoTerm.determinant Q,
      ∃ (Γ : TwoTerm.determinant Q ⊗[R] TwoTerm.kernelDeterminant a ≃ₗ[R]
        TwoTerm.determinant P) (δ : TwoTerm.kernelDeterminant a),
        IsKernelNormalizedAssembly a Γ δ T := by
  sorry

end Module

end
