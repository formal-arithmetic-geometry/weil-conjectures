module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Embedding a finite torsion-free module into a finite free module

Source: Stacks Project, More on Algebra, Tag 0AUU,
`lemma-finite-torsion-free-submodule-free`, torsion-free-to-embedding direction
(blueprint: lem-per-finite-torsion-free-free-embedding).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- A finitely generated torsion-free module over a commutative integral domain embeds
linearly into a finite coordinate module, allowing rank zero.

Source: Stacks Project, More on Algebra, Tag 0AUU,
`lemma-finite-torsion-free-submodule-free`, forward direction
(blueprint: lem-per-finite-torsion-free-free-embedding).

Proof:
1. Localize at the nonzero elements of `R` using `def-weil-pbc-module-localization`.
   The resulting ring `K` is a field: a fraction `a/s` vanishes exactly when `a = 0`,
   and every nonzero `a/s` has inverse `s/a`. Thus `R → K` is injective, and the
   localized module `V` is a `K`-vector space.
2. The localization map `j : M → V` is injective: its kernel criterion gives a nonzero
   scalar killing each element of its kernel, so torsion freeness kills that element.
   Choose finite generators `x_i` using `def-weil-finitely-generated-module`.
   Their images span `V`, since `m/s = ∑ i, (c_i/s) j(x_i)` when `m = ∑ i, c_i x_i`.
3. Choose a basis using `lem-weil-pbc-vector-space-free` and
   `def-weil-pbc-free-module`. The union of the supports of the finitely many `j(x_i)`
   is finite and contains every basis index: otherwise the corresponding basis vector
   would have both zero and unit coefficient there. Enumerate this basis to obtain
   a coordinate isomorphism `θ : V ≃ K^r` for some natural number `r`.
4. Write each coordinate of each `θ(j(x_i))` as `a_ik/b_ik`. The product `b` of these
   finitely many nonzero denominators is nonzero (the empty product is one).
   Every coordinate of `b θ(j(m))` lies in `R`, by expressing `m` in the generators.
   These coordinates are independent of that expression because `R → K` is injective.
5. Let `i(m)` be the resulting `R`-valued coordinates. Additivity and linearity follow
   from those of `j` and `θ` and injectivity of `R → K`. If `i(m) = 0`, then
   `b θ(j(m)) = 0`; invertibility of `b`, followed by injectivity of `θ` and `j`,
   gives `m = 0`. For `r = 0` the same argument forces `M = 0`, so the empty
   coordinate module is included. -/
theorem exists_injective_fin_fun_of_finite_of_isTorsionFree
    (R : Type u) (M : Type v) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.IsTorsionFree R M] :
    ∃ (r : ℕ) (i : M →ₗ[R] (Fin r → R)), Function.Injective i := by
  sorry

end Module
