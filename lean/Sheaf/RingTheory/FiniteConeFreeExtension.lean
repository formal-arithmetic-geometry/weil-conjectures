/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# One descending finite free extension

Source: Stacks Project, Tag 064U, descending induction step.
(blueprint: lem-pc-ring-finite-cone-free-extension).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Extend a bounded finite free approximation by one degree using generators of its
finite obstruction module.

Source: Stacks Project, More on Algebra, Tag 064U, proof of (2) implies (1), induction
step; the cone-cycle version combines the kernel and cokernel generators in one step.
(blueprint: lem-pc-ring-finite-cone-free-extension).

Proof: Write `D = mappingCone f`. Choose finitely many generators of `H^(n-1)(D)`
and lift them to cycles. In the convention `D^(n-1) = F^n ⊕ C^(n-1)`, write a
representative as `(a,c)`; its equations are `d_F a = 0` and `f a + d_C c = 0`.
Take a finite free module on these generators in degree `n-1`, give it differential
`a` to `F^n`, and map it to `C^(n-1)` by `-c`. Retain all degrees at least `n`
and put zero in lower degrees. The cycle equations give the complex and chain-map
identities. Use `Shrink R` (R is small in v) for the finite free carrier in v.
The inclusion `j` of the old complex has identity components in degrees at least n,
and its lower components are the unique maps from zero. Thus `j ≫ g = f`.
The old cone has zero cohomology in degrees at least n. Adjoining the chosen cycles
kills every class of its degree n-1 cohomology, so the new cone is exact in degree
n-1 and remains exact above it. Equivalently the long exact sequence makes the new
map an isomorphism on cohomology above n-1 and surjective at n-1. The bound
`n ≤ b+1` ensures the new term does not exceed b, and all retained terms remain
finite free. Empty generators work for a zero obstruction module and for the zero
ring. This constructs the new complex from finite generators and cycle lifts. -/
theorem exists_finiteFree_cone_extension (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C F : CochainComplex (ModuleCat.{v} R) ℤ) (f : F ⟶ C) (b n : ℤ)
    (hn : n ≤ b + 1) (hlow : F.IsStrictlyGE n) (hupp : F.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i))
    (hvan : ∀ i : ℤ, n ≤ i → IsZero
      ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f))))
    (hfinite : Module.Finite R
      ((homologyFunctor (ModuleCat.{v} R) (n - 1)).obj
        (Q.obj (CochainComplex.mappingCone f)))) :
    ∃ (G : CochainComplex (ModuleCat.{v} R) ℤ) (g : G ⟶ C) (j : F ⟶ G),
      G.IsStrictlyGE (n - 1) ∧ G.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (G.X i) ∧ Module.Finite R (G.X i)) ∧
      (∀ i : ℤ, n - 1 ≤ i → IsZero
        ((homologyFunctor (ModuleCat.{v} R) i).obj
          (Q.obj (CochainComplex.mappingCone g)))) ∧
      j ≫ g = f ∧ (∀ i : ℤ, n ≤ i → IsIso (j.f i)) := by sorry

end DerivedCategory
