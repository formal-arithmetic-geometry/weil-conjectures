/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Prod

import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.Equalizer

/-! # Relative finite presentation of patched modules

Source: Stacks Project, Tag 08KP, the flat ambient algebra case in Situation 08KH
(blueprint: lem-sfb-relative-fp-module-fibre-product).

The algebra-map equations specify the canonical actions on the component tensor
products. Scalar-tower instances express restriction along these maps. The overlap
is written by extension from the component algebra, canonically equivalent to
extension from its base ring.
-/

@[expose] public section

set_option autoImplicit false

universe uA uA' uB uS uN uM

open scoped TensorProduct

namespace Module

/-- Relative finite presentation over a flat ambient algebra, Stacks Project, Tag 08KP
(blueprint: lem-sfb-relative-fp-module-fibre-product).

The pullback ring is `f.pullback g`. Its component algebra structures and the maps
between their scalar extensions are fixed by the displayed algebra-map equations.
The kernel in the conclusion consists exactly of pairs with equal overlap images;
its inherited action is the coordinatewise `S`-action.

Proof plan:
1. Flat module patching identifies `S` with the pullback of its component algebras.
   Right exactness identifies the kernel of the surjective overlap map
   (`lem-sfb-flat-module-fibre-product-patching`, `lem-weil-pbc-tensor-right-exact`).
2. Tensor cancellation identifies extension from a component algebra to the overlap
   with extension from the corresponding base ring. The given equivalence is thus
   the module patching datum of the node (`def-weil-pbc-module-tensor-product`,
   `lem-weil-pbc-tensor-over-quotient-ring`).
3. Finite module patching makes the patched module finite. Choose a finite free
   surjection onto it and denote its kernel by `K`
   (`lem-sfb-finite-module-fibre-product-patching`, `def-sc-finitely-presented-module`).
4. Patched-module base change and right exactness give surjections onto the component
   modules and their common overlap, with kernels `K_B`, `K_A'`, and `K_A`
   (`lem-sfb-patched-module-base-change`, `lem-weil-pbc-tensor-right-exact`).
5. Finite presentation of the component modules makes `K_B` and `K_A'` finite,
   by `Module.FinitePresentation.fg_ker`
   (`lem-trf-finite-presentation-surjective-module-kernel`).
6. Flatness over the base rings keeps the component short exact sequences exact
   after tensoring. Hence both kernel extensions identify with `K_A`
   (`lem-weil-pbc-flat-quotient-tensor-injective`).
7. The pullback description of `S` identifies `K` with the fibre product of these
   component kernels: a compatible pair lifts uniquely to a vector, and its image
   is zero because both projections of that image are zero.
8. Finite module patching makes `K` finite. Its generators give the finite relations
   in a finite presentation of the patched module
   (`lem-sfb-finite-module-fibre-product-patching`, `def-sc-finitely-presented-module`).
-/
theorem finitePresentation_relative_fibreProduct
    {A : Type uA} {A' : Type uA'} {B : Type uB}
    [CommRing A] [CommRing A'] [CommRing B]
    (f : B →+* A) (g : A' →+* A) (hg : Function.Surjective g)
    [Algebra (f.pullback g) B] [Algebra (f.pullback g) A']
    [Algebra (f.pullback g) A]
    (hB : algebraMap (f.pullback g) B = f.pullbackFst g)
    (hA' : algebraMap (f.pullback g) A' = f.pullbackSnd g)
    (hA : algebraMap (f.pullback g) A = f.comp (f.pullbackFst g))
    (S : Type uS) [CommRing S] [Algebra (f.pullback g) S]
    [Module.Flat (f.pullback g) S]
    [Algebra B (S ⊗[f.pullback g] B)]
    [Algebra A' (S ⊗[f.pullback g] A')]
    (hSB : ∀ b : B, algebraMap B (S ⊗[f.pullback g] B) b = 1 ⊗ₜ b)
    (hSA' : ∀ a' : A', algebraMap A' (S ⊗[f.pullback g] A') a' = 1 ⊗ₜ a')
    [Algebra (S ⊗[f.pullback g] B) (S ⊗[f.pullback g] A)]
    [Algebra (S ⊗[f.pullback g] A') (S ⊗[f.pullback g] A)]
    (hBA : ∀ (s : S) (b : B),
      algebraMap (S ⊗[f.pullback g] B) (S ⊗[f.pullback g] A) (s ⊗ₜ b) =
        s ⊗ₜ f b)
    (hA'A : ∀ (s : S) (a' : A'),
      algebraMap (S ⊗[f.pullback g] A') (S ⊗[f.pullback g] A) (s ⊗ₜ a') =
        s ⊗ₜ g a')
    [IsScalarTower S (S ⊗[f.pullback g] B) (S ⊗[f.pullback g] A)]
    [IsScalarTower S (S ⊗[f.pullback g] A') (S ⊗[f.pullback g] A)]
    (N : Type uN) [AddCommGroup N] [Module (S ⊗[f.pullback g] B) N]
    [Module B N] [IsScalarTower B (S ⊗[f.pullback g] B) N]
    [Module S N] [IsScalarTower S (S ⊗[f.pullback g] B) N]
    [Module.FinitePresentation (S ⊗[f.pullback g] B) N] [Module.Flat B N]
    (M' : Type uM) [AddCommGroup M'] [Module (S ⊗[f.pullback g] A') M']
    [Module A' M'] [IsScalarTower A' (S ⊗[f.pullback g] A') M']
    [Module S M'] [IsScalarTower S (S ⊗[f.pullback g] A') M']
    [Module.FinitePresentation (S ⊗[f.pullback g] A') M'] [Module.Flat A' M']
    (φ : ((S ⊗[f.pullback g] A) ⊗[S ⊗[f.pullback g] B] N) ≃ₗ[S ⊗[f.pullback g] A]
      ((S ⊗[f.pullback g] A) ⊗[S ⊗[f.pullback g] A'] M')) :
    Module.FinitePresentation S
      (LinearMap.ker
        (((φ.toLinearMap.restrictScalars S) ∘ₗ
          (LinearMap.restrictScalars S
            (TensorProduct.mk (S ⊗[f.pullback g] B) (S ⊗[f.pullback g] A) N 1))) ∘ₗ
            LinearMap.fst S N M' -
          (LinearMap.restrictScalars S
            (TensorProduct.mk (S ⊗[f.pullback g] A') (S ⊗[f.pullback g] A) M' 1)) ∘ₗ
              LinearMap.snd S N M')) := by
  sorry

end Module
