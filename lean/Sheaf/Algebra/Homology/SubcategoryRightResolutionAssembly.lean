/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Assembling an ascending cokernel and pushout system

Source: Stacks Project, Tag 05T6(1), the ascending recursion dual to Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-assembly).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped ZeroObject

namespace CochainComplex

/-- Assemble a supplied sequence of terms, cokernels, augmentation components and local
pushout factorizations into an integer-indexed complex. This is only the assembly step:
the sequence, all its monomorphisms, and its pushouts are inputs; no quasi-isomorphism
is asserted. Source: Stacks Project, Tag 05T6(1), the recursion in the dual of Tag 05T7(1).
(blueprint: lem-weil-pbc-subcategory-right-resolution-assembly).

Proof: Put `I.X (a + m) = X m` for `m : ℕ`, and put the chosen zero object in every
smaller degree. Use the supplied `d m` as the differential in degree `a + m`; all other
differentials are zero. Successive differentials compose to zero because `d m` factors
through `p m` and `d (m - 1) ≫ p m = 0`; at the lower boundary the first map is zero.
Set the augmentation equal to `α m` in degree `a + m`, and zero below `a`. The identity
`K.pOpcycles ≫ β = α ≫ p` followed by the pushout identity proves commutation in each
nonzero degree. Below `a`, commutation holds since the source term of `K` is zero.
The initial `p 0` is an isomorphism, so it is a cokernel of the zero incoming differential.
For later degrees, `hcoker` identifies `Q m` with the opcycles of `I`. Under these
canonical identifications the induced map on opcycles is `β m`, by its characterization
after precomposition with the epimorphism `K.pOpcycles`. Thus it is mono. Transport the
supplied pushout squares along these identifications; the induced map out of opcycles
is `v ≫ j` by the differential factorization and cancellation of `p m`. In degree
`a - 1`, the opcycles on both sides are zero: take pushout object `K.X a`, maps the
identity and zero, and embedding `α 0`. In smaller degrees take the zero pushout.
Every augmentation component is mono, either by `hmono` or because its source is zero.
Membership follows from `hmem` and `hzero`; the lower bound follows from the construction.
-/
theorem exists_complex_of_cokernel_pushout_system
    (C : Type u) [Category.{v} C] [Abelian C]
    (𝓘 : Set C) (hzero : (0 : C) ∈ 𝓘)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, n < a → IsZero (K.X n))
    (X Q : ℕ → C) (p : ∀ m : ℕ, X m ⟶ Q m)
    (α : ∀ m : ℕ, K.X (a + m) ⟶ X m)
    (β : ∀ m : ℕ, K.opcycles (a + m) ⟶ Q m)
    (hmem : ∀ m : ℕ, X m ∈ 𝓘) (hepi : ∀ m : ℕ, Epi (p m))
    (hmono : ∀ m : ℕ, Mono (α m)) (hβ : ∀ m : ℕ, Mono (β m))
    (hcomm : ∀ m : ℕ, K.pOpcycles (a + m) ≫ β m = α m ≫ p m)
    (hinit : IsIso (p 0))
    (d : ∀ m : ℕ, X m ⟶ X (m + 1))
    (hzero_d : ∀ m : ℕ, d m ≫ p (m + 1) = 0)
    (hcoker : ∀ m : ℕ, IsColimit (CokernelCofork.ofπ (p (m + 1)) (hzero_d m)))
    (hsq : ∀ m : ℕ, ∃ (P : C) (u : K.X (a + (m + 1 : ℕ)) ⟶ P) (v : Q m ⟶ P)
      (j : P ⟶ X (m + 1)), Mono j ∧
      IsPushout (K.fromOpcycles (a + m) (a + (m + 1 : ℕ))) (β m) u v ∧
      u ≫ j = α (m + 1) ∧ p m ≫ v ≫ j = d m) :
    ∃ (I : CochainComplex C ℤ) (ι : K ⟶ I),
      (∀ n : ℤ, Mono (ι.f n)) ∧ (∀ n : ℤ, I.X n ∈ 𝓘) ∧
      (∀ n : ℤ, n < a → IsZero (I.X n)) ∧
      (∀ n : ℤ, Mono (opcyclesMap ι n)) ∧
      (∀ n : ℤ, ∃ (P : C) (u : K.X (n + 1) ⟶ P) (v : I.opcycles n ⟶ P)
        (j : P ⟶ I.X (n + 1)), Mono j ∧
        IsPushout (K.fromOpcycles n (n + 1)) (opcyclesMap ι n) u v ∧
        u ≫ j = ι.f (n + 1) ∧ v ≫ j = I.fromOpcycles n (n + 1)) := by
  sorry

end CochainComplex
