module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Artin-Rees bounds under simultaneous perturbation

Source: Stacks Project, More on Algebra, Tag 07VE (lemma-approximate-complex),
first conclusion and first paragraph of the proof
(blueprint: lem-sfb-perturbed-image-artin-rees-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u v w t

namespace LinearMap

/-- A common Artin-Rees bound for the two maps of an exact complex remains a bound
for the right differential after perturbing both maps modulo `I^(c+1)`, provided
the perturbed maps still form a complex. The submodule `I^n • ⊤` is `I^n` times
the ambient module, including the whole module when `n = 0`.

Source: Stacks Project, More on Algebra, Tag 07VE (lemma-approximate-complex),
first conclusion and first paragraph of the proof
(blueprint: lem-sfb-perturbed-image-artin-rees-bound).

Proof (the node's six steps).
1. Fix `n ≥ c` and `y ∈ range g' ∩ I^n N`. Choose `a₀` with `g'(a₀) = y`.
   Set `k = n-c`; construct `aᵣ ∈ I^r M` with `g'(aᵣ) = y` for `0 ≤ r ≤ k`.
2. By linearity and expansion into finite sums, a map with image in `I^(c+1) U`
   sends `I^s T` into `I^(s+c+1) U`. Apply this to both difference maps.
3. If `r < k`, then `r+c+1 ≤ n`, so `g(aᵣ) = y + (g-g')(aᵣ)` belongs to
   `I^(r+c+1) N`. The bound for `g` gives `e ∈ I^(r+1) M` with `g(e) = g(aᵣ)`.
4. Exactness gives `b ∈ L` with `f(b) = aᵣ-e ∈ I^r M`. When `r ≥ c`, the
   bound for `f` permits choosing `b ∈ I^(r-c) L`; when `r < c`, retain `b`.
5. Put `aᵣ₊₁ = aᵣ-f'(b) = e+(f-f')(b)`. For `r < c`, the error is in
   `I^(c+1) M ⊆ I^(r+1) M`; for `r ≥ c`, step 2 puts it in
   `I^((r-c)+(c+1)) M = I^(r+1) M`. Since `g'f' = 0`, its image is still `y`.
6. At `r = k`, obtain `y = g'(aₖ)` with `aₖ ∈ I^(n-c) M`. When `n = c`,
   the initial preimage suffices and no adjustment is needed.
-/
theorem perturbed_image_artin_rees_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : ∀ m : Ideal A, m.IsMaximal → I ≤ m)
    {L : Type v} [AddCommGroup L] [Module A L] [Module.Finite A L]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {N : Type t} [AddCommGroup N] [Module A N] [Module.Finite A N]
    (f f' : L →ₗ[A] M) (g g' : M →ₗ[A] N)
    (h_exact : LinearMap.range f = LinearMap.ker g)
    (h_complex : g'.comp f' = 0) (c : ℕ)
    (hf : ∀ n : ℕ, c ≤ n →
      LinearMap.range f ⊓ (I ^ n • (⊤ : Submodule A M)) ≤
        Submodule.map f (I ^ (n - c) • (⊤ : Submodule A L)))
    (hg : ∀ n : ℕ, c ≤ n →
      LinearMap.range g ⊓ (I ^ n • (⊤ : Submodule A N)) ≤
        Submodule.map g (I ^ (n - c) • (⊤ : Submodule A M)))
    (hff' : LinearMap.range (f - f') ≤ I ^ (c + 1) • (⊤ : Submodule A M))
    (hgg' : LinearMap.range (g - g') ≤ I ^ (c + 1) • (⊤ : Submodule A N)) :
    ∀ n : ℕ, c ≤ n →
      LinearMap.range g' ⊓ (I ^ n • (⊤ : Submodule A N)) ≤
        Submodule.map g' (I ^ (n - c) • (⊤ : Submodule A M)) := by
  sorry

end LinearMap
