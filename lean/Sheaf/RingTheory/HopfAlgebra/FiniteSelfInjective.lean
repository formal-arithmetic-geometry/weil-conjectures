module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution

import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Self-injectivity of finite-dimensional commutative Hopf algebras

Source: Bichon, arXiv:2301.05480v2, section 3, first paragraph
(blueprint: lem-sfb-finite-hopf-self-injective).

The extension property is stated for arbitrary modules, with independent universes.
-/

@[expose] public section

universe u v w x y

namespace HopfAlgebra

/-- A commutative Hopf algebra with a finite vector-space basis is injective over itself:
every linear map into it extends along every injective module map, without any finiteness
assumption on the source or ambient module.

Source: Bichon, arXiv:2301.05480v2, section 3, first paragraph
(blueprint: lem-sfb-finite-hopf-self-injective).

Proof:
1. By lem-sfb-finite-hopf-frobenius-form choose a linear functional `λ : H →ₗ[k] k`
   for which `a ↦ (h ↦ λ (h * a))` is bijective. In particular these evaluations
   distinguish elements of `H`.
2. Restrict scalars on `U` and `V` to `k`. By
   lem-weil-pbc-vector-space-basis-through-vector choose a basis of `U` and extend its
   injective image under `j` to a basis of `V`. Give each image basis vector `j b` the
   value `λ (f b)` and give the added vectors value zero. Finite basis expansions define
   a linear functional `t : V →ₗ[k] k` with `t (j u) = λ (f u)` for every `u`.
3. For each `v : V`, bijectivity of the Frobenius map gives the unique `g v : H`
   satisfying `λ (h * g v) = t (h • v)` for every `h : H`. Evaluate this identity
   on sums and on `a • v`. Linearity of `t` and the separating evaluations show
   `g (v + w) = g v + g w` and `g (a • v) = a * g v`, so `g` is `H`-linear.
4. For every `u : U` and `h : H`, linearity of `j` and `f` gives
   `λ (h * g (j u)) = t (j (h • u)) = λ (h * f u)`. The separating evaluations
   imply `g (j u) = f u`. All basis expansions were finite even for infinite bases,
   so no finite-generation assumption on `U` or `V` is used. -/
theorem finiteDimensional_exists_extension (k : Type u) [Field k] (H : Type v)
    [CommRing H] [HopfAlgebra k H] (ι : Type w) [Finite ι] (basis : Module.Basis ι k H)
    (U : Type x) (V : Type y) [AddCommGroup U] [Module H U] [AddCommGroup V] [Module H V]
    (j : U →ₗ[H] V) (hj : Function.Injective j) (f : U →ₗ[H] H) :
    ∃ g : V →ₗ[H] H, g.comp j = f := by
  sorry

end HopfAlgebra
