/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Bounded flat complexes with finite cohomology over a Noetherian ring

Over a Noetherian ring `A`, a bounded complex of flat `A`-modules whose cohomology modules are
finite is quasi-isomorphic to a bounded complex of finite projective `A`-modules in the same
degrees: it is a perfect complex.
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- **A bounded flat complex with finite cohomology over a Noetherian ring is perfect.** Let `A`
be a Noetherian ring and `C` a complex of flat `A`-modules concentrated in degrees `[a, b]` whose
cohomology modules are finite. Then there is a quasi-isomorphism `P ⟶ C` from a complex `P` of
finite projective `A`-modules concentrated in degrees `[a, b]`.

One builds a bounded above complex of finite free modules mapping quasi-isomorphically to `C` by
descending induction on the degree, killing the finite cohomology of the cone in each degree. Its
truncation at `a` replaces the tail by `Q = coker(P^{a-1} ⟶ P^a)`, which is finitely presented and
flat (its `Tor_1` against any module is `H^{a-1}(C ⊗ N) = 0`), hence finite projective.

(blueprint: `lem-pc-noetherian-flat-complex-perfect`) -/
theorem exists_quasiIso_of_flat_of_finite {A : Type u} [CommRing A] [IsNoetherianRing A]
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [C.IsStrictlyGE a] [C.IsStrictlyLE b]
    (hflat : ∀ n, Module.Flat A (C.X n)) (hfin : ∀ n, Module.Finite A (C.homology n)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (φ : P ⟶ C), P.IsStrictlyGE a ∧
      P.IsStrictlyLE b ∧ (∀ n, Module.Projective A (P.X n) ∧ Module.Finite A (P.X n)) ∧
      QuasiIso φ :=
  sorry

end CochainComplex
