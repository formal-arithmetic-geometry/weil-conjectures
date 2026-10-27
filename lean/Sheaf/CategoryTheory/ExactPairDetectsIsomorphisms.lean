/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Exact pairs detecting zero objects detect isomorphisms

Source: Stacks Project, homology.tex, Tag 010N (lemma-exact-functor), and the
joint-zero-detection argument in Step 4 of lem-cbc-ringed-open-extension-products
(blueprint: lem-cbc-exact-pair-detects-isomorphisms).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory

/-- A pair of exact functors between abelian categories that jointly detects zero
objects detects isomorphisms.

Source: Stacks Project, homology.tex, Tag 010N (lemma-exact-functor), with the
joint-detection assembly from lem-cbc-ringed-open-extension-products, Step 4
(blueprint: lem-cbc-exact-pair-detects-isomorphisms).

Proof:
1. Choose a kernel k : K ⟶ M and a cokernel q : N ⟶ Q of c using
   def-sp-abelian. By def-galois-exact-functor and clause (a) of
   lem-sp-exact-functor-preserves-homology, J and I carry them to kernels and
   cokernels of the respective images of c.
2. For F = J and F = I, invertibility of F(c) forces F(k) = 0 and F(q) = 0.
   Kernel and cokernel uniqueness then give identity = zero on F(K) and F(Q).
   In a preadditive category this makes each object initial and terminal:
   every morphism to or from it equals its composite with the zero identity.
   This is Tag 00ZZ (lemma-preadditive-zero). Joint zero detection makes K and Q zero.
3. If c composed with a and b agrees, the difference a - b factors through K
   and is zero. Thus c is monic. Dually, a difference annihilating c factors
   through Q and is zero, so c is epic.
4. By the normal-monomorphism axiom of def-sp-abelian, c is a kernel of some
   h : N ⟶ P. Since c is epic and c ≫ h = 0, h = 0. The kernel universal
   property applied to the identity of N gives s : N ⟶ M with s ≫ c = 𝟙 N.
   Monicity of c then gives c ≫ s = 𝟙 M, so c is invertible. -/
theorem isIso_of_exact_pair_detects_zero
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [Abelian C] [Abelian D] [Abelian E]
    (J : C ⥤ D) (I : C ⥤ E)
    [J.PreservesZeroMorphisms] [I.PreservesZeroMorphisms]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (hd : ∀ M : C, IsZero (J.obj M) → IsZero (I.obj M) → IsZero M)
    {M N : C} (c : M ⟶ N) [IsIso (J.map c)] [IsIso (I.map c)] : IsIso c := by
  have hk : IsZero (kernel c) := hd _
    ((isZero_kernel_of_mono (J.map c)).of_iso (PreservesKernel.iso J c))
    ((isZero_kernel_of_mono (I.map c)).of_iso (PreservesKernel.iso I c))
  have hc : IsZero (cokernel c) := hd _
    ((isZero_cokernel_of_epi (J.map c)).of_iso (PreservesCokernel.iso J c))
    ((isZero_cokernel_of_epi (I.map c)).of_iso (PreservesCokernel.iso I c))
  have : Mono c := Preadditive.mono_of_isZero_kernel c hk
  have : Epi c := Preadditive.epi_of_isZero_cokernel c hc
  exact isIso_of_mono_of_epi c

end CategoryTheory
