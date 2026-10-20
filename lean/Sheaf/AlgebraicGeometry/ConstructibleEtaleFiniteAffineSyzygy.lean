/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q119
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteZeroCokernel
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.AlgebraicGeometry.FreeEtaleModuleShriekComparison
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekConstantConstructible
import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Finite affine-free syzygies of constructible etale module sheaves

Source: Stacks Project, Tags 095N, 03RZ and 03S8, finite iteration of affine-free
surjections and constructible kernels
(blueprint: lem-trf-constructible-etale-finite-affine-syzygy).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A constructible etale module sheaf has finite affine-free syzygy towers of every
positive finite length. The short exact sequences below say that `K (a.succ)` is the
kernel of `e a`, with inclusion `i a`, and that `e a` is an epimorphism. Splicing them,
with differential `e (a + 1) ≫ i a`, gives the exact sequence
`0 → K r → E (r - 1) → ... → E 0 → F → 0`.

Source: Stacks Project, Tag 095N (lemma-category-constructible-modules), Tag 03RZ
(lemma-constructible-abelian) and Tag 03S8 (lemma-jshriek-constructible).
(blueprint: lem-trf-constructible-etale-finite-affine-syzygy).

Proof:
1. Start with `K 0 = F`. Given constructible `K a`, apply
   `lem-weil-pbc-constructible-module-finite-zero-cokernel` to obtain a finite affine
   etale free cover with zero cokernel. Identify each sheafified free representable
   with the corresponding `j_!` constant rank-one module by
   `lem-weil-pbc-free-etale-module-shriek-comparison`. Thus the cover is `e a : E a → K a`.
   Zero cokernel makes this morphism epi in the abelian category of module sheaves
   (`def-weil-pbc-etale-sheaves`). Set `K (a + 1)` to its kernel.
2. Each affine etale object is qcqs. Its rank-one extension by zero is constructible
   by `lem-weil-pbc-etale-free-sheaf-constructible` (Tag 03S8). Finite sums are
   constructible by the extension clause of `thm-constructible-serre`, inductively
   using split short exact sequences; the empty sum is the kernel of an identity.
   The kernel clause of that same theorem (Tag 03RZ) now makes `K (a + 1)` constructible.
   Iterate these steps exactly `r` times.
3. The kernel inclusions and epimorphisms give the displayed short exact sequences.
   Splice them: consecutive composites vanish; the image of `e (a + 1) ≫ i a`
   is the kernel of `e a`, since `e (a + 1)` is epi. At the left endpoint the
   inclusion of `K r` is mono; at the right endpoint `e 0` is epi and `K 0 = F`.
   This gives exactness at every term of the requested finite sequence, with every
   syzygy constructible. -/
theorem exists_constructible_etale_finite_affine_syzygy
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) (r : ℕ) (hr : 1 ≤ r) :
    ∃ (K : Fin (r + 1) → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (E : Fin r → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
      (n : Fin r → ℕ) (U : ∀ a : Fin r, Fin (n a) → X.Etale)
      (i : ∀ a : Fin r, K a.succ ⟶ E a)
      (e : ∀ a : Fin r, E a ⟶ K a.castSucc),
      K 0 = F ∧
      (∀ a : Fin (r + 1), IsConstructibleEtaleModuleSheaf (K a)) ∧
      (∀ (a : Fin r) (t : Fin (n a)), IsAffine (U a t).left) ∧
      (∀ a : Fin r, E a = ∐ fun t : Fin (n a) ↦
        (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (U a t).hom inferInstance).obj
          ((constantSheaf (U a t).left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ∧
      ∃ w : ∀ a : Fin r, i a ≫ e a = 0,
        ∀ a : Fin r, (ShortComplex.mk (i a) (e a) (w a)).ShortExact := by
  sorry

end AlgebraicGeometry.Scheme
