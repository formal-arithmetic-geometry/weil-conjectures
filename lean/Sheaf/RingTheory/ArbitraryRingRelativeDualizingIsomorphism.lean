/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.RingPseudoCoherent
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison
import Sheaf.Algebra.Homology.ProjectiveHomEvaluationModel

/-! # Unmarked relative dualizing complexes over arbitrary rings

Source: Stacks Project, dualizing.tex, Definition 0E2C and Lemma 0E2D
(blueprint: lem-sfb-arbitrary-ring-relative-dualizing-isomorphism).

The diagonal and derived scalar extension are the shared affine constructions.
Derived internal Hom is its ordinary-module presentation on the one-object ringed site.
The finite Tor interval is over the base ring, not over the diagonal algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Two relative dualizing complexes over an arbitrary flat finitely presented algebra
are isomorphic. No compatibility with chosen diagonal classes is asserted.
Source: Stacks Project, dualizing.tex, Definition 0E2C and Lemma 0E2D
(blueprint: lem-sfb-arbitrary-ring-relative-dualizing-isomorphism).

Proof (the accepted polynomial-duality route):
1. Choose a finite polynomial presentation P = R[x_1,...,x_n] onto A. Put
   C = C_{P to A}(P)[n]. By lem-sfb-arbitrary-polynomial-dual-properties, C is
   R-perfect and the scalar-action map h : A[0] to RHom_A(C,C) is invertible.
   This also applies to the zero algebra, whose derived category has only zero objects.
2. For T = M,N, restrict the assumed diagonal isomorphism along the actual first
   coprojection p1 : A to A tensor_R A. Multiplication composed with p1 is the identity,
   so the restricted target is the usual A[0]. The comparison of
   lem-sfb-arbitrary-polynomial-diagonal-hom gives g_T : A[0] isomorphic to RHom_A(C,T).
   Only existence is needed; no generator is fixed or preserved.
3. Use lem-pod-projective-hom-evaluation-model on a bounded-above finite-free model of C,
   supplied by its pseudo-coherence. The adjunct of g_T gives f_T : C to T, using
   C tensor_A A[0] isomorphic to C. Naturality of tensor-Hom adjunction gives
   RHom_A(C,f_T) composed with h equal to g_T, since h is adjunct to the identity of C.
   Consequently RHom_A(C,f_T) is invertible.
4. Both C and T are R-perfect. The morphism clause of
   lem-sfb-relative-perfect-polynomial-dual-detection therefore makes f_T invertible.
   Compose the inverse of f_M with f_N to obtain M isomorphic to N. There is no
   normalization condition on this composite.
-/
theorem arbitraryRing_relativeDualizing_isomorphic
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (hflat : RingHom.Flat (algebraMap R A)) [Algebra.FinitePresentation R A]
    (M N : DerivedCategory (ModuleCat.{u} A))
    (hM : DerivedCategory.IsPseudoCoherent M)
    (hN : DerivedCategory.IsPseudoCoherent N)
    (hMTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj M) ⊗
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q))))
    (hNTor : ∃ a b : ℤ, a ≤ b ∧ ∀ (Q : ModuleCat.{u} R) (i : ℤ),
      i < a ∨ b < i → IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj N) ⊗
            DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj Q))))
    (hMHom : Nonempty
      ((ordinaryModuleDerivedInternalHom (A ⊗[R] A)).obj
        (op (relativeDualizingModuleDiagonal R A),
          (relativeDualizingDerivedExtension
            (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj M) ≅
        relativeDualizingModuleDiagonal R A))
    (hNHom : Nonempty
      ((ordinaryModuleDerivedInternalHom (A ⊗[R] A)).obj
        (op (relativeDualizingModuleDiagonal R A),
          (relativeDualizingDerivedExtension
            (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom).obj N) ≅
        relativeDualizingModuleDiagonal R A)) :
    Nonempty (M ≅ N) := by
  sorry

end AlgebraicGeometry
