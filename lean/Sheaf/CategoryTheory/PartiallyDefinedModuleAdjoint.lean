/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint

/-!
# Extending an adjoint from an epimorphic generating class

Source: Stacks Project, Homology, Tag 0793, lemma-partially-defined-adjoint,
the additive specialization (blueprint: lem-trf-partially-defined-module-adjoint).
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

/-- An additive functor between abelian categories has a left adjoint if the Hom
functors associated to an epimorphic generating class are corepresentable.

Source: Stacks Project, Homology, Tag 0793, lemma-partially-defined-adjoint,
the additive specialization (blueprint: lem-trf-partially-defined-module-adjoint).

Proof:
1. For each generator P, choose its stipulated representing object L_P and natural
bijections theta. By Yoneda (lem-galois-yoneda-hom-bijection), if i_P is the image of
its identity, then theta(a) = i_P followed by R(a). Additivity of R implies that
zero corresponds to zero.
2. For B, choose an epimorphism q : P_1 -> B from the class. Choose another such
epimorphism r : P_2 -> kernel(q), and let d be r followed by the kernel inclusion.
No projectivity or lifting property of the generators is needed.
3. The map q is a cokernel of d: a map killing d kills the kernel inclusion by
cancellation of the epimorphism r, and therefore factors uniquely through q,
since epimorphisms in an abelian category are cokernels of their kernels.
4. Define D : L_{P_2} -> L_{P_1} as the inverse image of d followed by i_{P_1}.
Naturality gives theta(a composed after D) = theta(a) composed after d.
The zero compatibility and injectivity of theta show that a kills D exactly when
theta(a) kills d.
5. Take C_B to be the cokernel of D in the abelian category A. The cokernel
universal properties on both sides and step 4 give bijections
Hom(C_B, X) = Hom(B, R(X)), characterized after precomposition with q by theta.
6. These bijections are natural in X: compose the defining equation with R(f),
use naturality of theta, and cancel the epimorphism q. Thus the required Hom
functor is corepresentable for every B.
7. Apply lem-sfb-right-adjoint-from-objectwise-representability to R.op and then
reverse arrows. The objectwise representing objects assemble into a left adjoint
to R with Hom bijections natural in both variables. Functor categories can be
formed in a containing universe. -/
theorem isRightAdjoint_of_epi_generating_class
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (R : A ⥤ B) [R.Additive]
    (P : Set B)
    (hcover : ∀ Y : B, ∃ Q : B, Q ∈ P ∧ ∃ q : Q ⟶ Y, Epi q)
    (hrep : ∀ Q ∈ P, ∃ LQ : A,
      ∃ theta : ∀ X : A, (LQ ⟶ X) ≃ (Q ⟶ R.obj X),
        ∀ (X X' : A) (f : X ⟶ X') (a : LQ ⟶ X),
          theta X' (a ≫ f) = theta X a ≫ R.map f) :
    R.IsRightAdjoint := by
  sorry

end CategoryTheory.Functor
