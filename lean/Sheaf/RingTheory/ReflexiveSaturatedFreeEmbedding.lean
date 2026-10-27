module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.LeftExact
import Mathlib.LinearAlgebra.Pi
import Sheaf.LinearAlgebra.Dual.TorsionFreeBidualInjective
import Sheaf.RingTheory.FiniteInjectionBidualInjective

/-!
# Reflexive modules as saturated submodules of finite free modules

Source: Stacks Project, More on Algebra, Tag 0AV2 (`lemma-characterize-reflexive`),
with the converse expanded using Tag 0EB8 (`lemma-sequence-reflexive`).
(blueprint: lem-per-reflexive-saturated-free-embedding).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Module

/-- A finite module over a Noetherian domain is reflexive if and only if it admits an
injection into a finite free module with torsion-free quotient. The finite free module
is the module of `r`-tuples, including the zero module when `r = 0`.

Source: Stacks Project, Tag 0AV2 (`lemma-characterize-reflexive`); the converse uses
Tag 0EB8 (`lemma-sequence-reflexive`).
(blueprint: lem-per-reflexive-saturated-free-embedding).

Proof plan:
1. Suppose `M` is reflexive. Evaluate functionals on a finite generating family of `M`
   to embed `M*` in a finite power of `R`. By
   `lem-weil-pbc-noetherian-submodule-finite`, its image, hence `M*`, is finite.
   Choose generators of `M*` and then of the kernel of their surjection, using the same
   node again, to obtain a finite presentation `R^m → R^n → M* → 0`.
2. Apply `lem-weil-pbc-module-hom-left-exact` to dualize this presentation. Its coordinate
   identification of the duals of finite free modules gives an injection
   `j : M** → R^n` whose image is the kernel of a map `d : R^n → R^m`.
3. Set `N = range d` and restrict the codomain of `d` to obtain a surjection `q`.
   The module `N` is torsion free: if a nonzero scalar annihilates a vector, domain
   cancellation annihilates every coordinate. Compose `j` with the evaluation
   isomorphism of `M` to get the required injection with image `ker q`. Empty
   generating families are allowed throughout. Lift `N` to the displayed universe.
4. Conversely, suppose such `i` and `q` are given. The images under `q` of the coordinate
   basis generate `N`, so `lem-per-torsion-free-bidual-injective` gives injectivity of
   its evaluation map. Evaluation on `R^r` is an isomorphism: its inverse sends a
   bidual functional `z` to the tuple `z(π_k)` of values on coordinate projections.
   Functionals on `R^r` are linear combinations of these projections, giving both
   inverse identities. Evaluation on `M` is injective because the functionals `π_k ∘ i`
   separate points, by injectivity of `i`.
5. By `lem-per-finite-injection-bidual-injective`, the map `i**` is injective. For
   `x ∈ M**`, let `v = eval_R^r⁻¹(i** x)`. For every `ψ ∈ N*`, evaluation gives
   `eval_N(q v)(ψ) = x(ψ ∘ q ∘ i) = 0`. The injectivity of `eval_N` gives `q v = 0`.
   Exactness supplies `m` with `i m = v`. Naturality of evaluation gives
   `i**(eval_M m) = i** x`; injectivity of `i**` then gives `eval_M m = x`.
   Thus evaluation on `M` is also surjective, proving reflexivity. -/
theorem isReflexive_iff_exists_exact_finite_free
    (R : Type u) (M : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.IsReflexive R M ↔
      ∃ (r : ℕ) (N : Type (max u v)) (_ : AddCommGroup N) (_ : Module R N),
        Module.IsTorsionFree R N ∧
          ∃ (i : M →ₗ[R] (Fin r → R)) (q : (Fin r → R) →ₗ[R] N),
            Function.Injective i ∧ Function.Exact i q ∧ Function.Surjective q := by
  sorry

end Module
