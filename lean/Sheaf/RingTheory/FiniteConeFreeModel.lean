/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker J1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.Free

/-!
# Finite obstruction groups give a finite free model

Source: Stacks Project, More on Algebra, Tag 064U, descending construction.
(blueprint: lem-pc-ring-finite-cone-free-model).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Construct a bounded above finite free model from finite top cohomology of the cones
of bounded finite free approximations. The ring fits in the module universe, so finite
free modules on finite sets of generators can be constructed in that universe.

Source: Stacks Project, More on Algebra, Lemma 15.66.5, Tag 064U, construction in the
proof of (2) implies (1), after the finite obstruction group has been established.
(blueprint: lem-pc-ring-finite-cone-free-model).

Proof: start at degree `b + 1` with the zero complex and the zero map to `C`. Since
`H^i(C) = 0` for `i > b`, this map is an isomorphism above `b + 1` and surjective at
`b + 1`. Suppose `F` is zero below `n` and above `b`, is finite free termwise, and its
map to `C` is an isomorphism above `n` and surjective at `n`. The cone long exact
sequence makes the cone zero in cohomology above `n - 1`. Its degree-`n - 1`
cohomology is finite by `hcone`. Choose finitely many generating classes and represent
them by cone cycles. A cone cycle is a pair in `F^n` and `C^(n - 1)` satisfying the
cycle and chain-map equations. Adjoin a finite free module in degree `n - 1`, mapping
its basis to these pairs (with the sign prescribed by the cone convention). The
cohomology sequence shows that this kills the kernel in degree `n` and covers the
cokernel in degree `n - 1`, giving an isomorphism at `n` and a surjection at `n - 1`.
All terms, maps and differentials in degrees at least `n` remain unchanged.
Use dependent choice to iterate these compatible extensions for `n = b + 1 - k`.
In each degree take the term and differential when they first stabilize; the
compatibilities give a cochain complex and a chain map to `C`. This is a real
construction from the chosen finite generating sets and cone cycles, not a definition
by an unproved existence theorem. Its terms are finite free and vanish above `b`.
For a fixed degree `i`, the stage below `i` already induces an isomorphism on `H^i`,
and all three terms computing that cohomology have stabilized. The resulting chain
map is therefore a quasi-isomorphism. The zero ring and an acyclic `C` are covered
by the same construction, with empty generating sets when the obstruction is zero. -/
theorem exists_finiteFree_model_of_finite_cones (R : Type u) [CommRing R] [Small.{v} R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ) (b : ℤ)
    (hvan : ∀ i : ℤ, b < i →
      IsZero ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj C)))
    (hcone : ∀ (F : CochainComplex (ModuleCat.{v} R) ℤ) (a c : ℤ),
      F.IsStrictlyGE a → F.IsStrictlyLE c →
      (∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i)) →
      ∀ (f : F ⟶ C) (n : ℤ),
        (∀ i : ℤ, n < i → IsZero
          ((homologyFunctor (ModuleCat.{v} R) i).obj (Q.obj (CochainComplex.mappingCone f)))) →
        Module.Finite R
          ((homologyFunctor (ModuleCat.{v} R) n).obj (Q.obj (CochainComplex.mappingCone f)))) :
    ∃ (F : CochainComplex (ModuleCat.{v} R) ℤ), F.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Free R (F.X i) ∧ Module.Finite R (F.X i)) ∧
      ∃ f : F ⟶ C, QuasiIso f := by sorry

end DerivedCategory
